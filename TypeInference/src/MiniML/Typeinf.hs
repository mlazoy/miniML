module MiniML.Typeinf where

import qualified Data.Map as M
import Control.Monad.State
import Data.List (nub, (\\)) -- nub removes duplicates from a list. You may find it helpful.
import qualified Data.Set as S -- use it for constraints

import MiniML.Syntax
import MiniML.Error
import MiniML.Print -- For better error messages
import Debug.Trace -- Debug.Trace is your friend


-- A Typing context
type Ctx = M.Map String TypeScheme
-- Pretty-printing for context
showCtx :: Ctx -> String
showCtx ctx = unlines [x ++ " : " ++ showTypeScheme ts | (x, ts) <- M.toList ctx]

newtype Constraint = Constraint (Type, Type, Posn)  -- A single constraint
type Constraints = S.Set Constraint   -- A set of constraints

instance Eq Constraint where
  (Constraint (t1a, t2a, _)) == (Constraint (t1b, t2b, _)) =
    (t1a == t1b && t2a == t2b) || (t1a == t2b && t2a == t1b)

instance Ord Constraint where
  compare (Constraint (t1a, t2a, _)) (Constraint (t1b, t2b, _)) =
    compare (min t1a t2a, max t1a t2a) (min t1b t2b, max t1b t2b)

-- Insert a single constraint or a list of constraints into the set (top method)
insertCnstr :: [(Type, Type, Posn)] -> Constraints -> Constraints
insertCnstr [] constraints = constraints  -- If the list is empty, return the original set
insertCnstr [(t1, t2, p)] constraints = S.insert (Constraint (t1, t2, p)) constraints
insertCnstr ((t1, t2, p):xs) constraints =
  insertCnstr xs (S.insert (Constraint (t1, t2, p)) constraints)

-- Show a single constraint
showConstraint :: Constraint -> String
showConstraint (Constraint (t1, t2, posn)) =
  "At " ++ show posn ++ ": " ++ showType t1 ++ " == " ++ showType t2

-- Show all constraints in a set
showConstraints :: Constraints -> String
showConstraints cs = unlines (map showConstraint (S.toList cs))

-- Substitution
type Substitution = M.Map String Type

-- The state for the type inference monad. You may want to add extend the record
-- with more information (e.g., constraints), depending on your implementation
-- of constraint generation.
newtype TypeInfState = MkTIState { fresh :: Int }

-- The monad for type inference.
type TypeInf = StateT TypeInfState (Either (Posn,String))

-- Generate a fresh type variable
freshTVar :: TypeInf String
freshTVar = do
  MkTIState nextVar <- get
  put $ MkTIState (nextVar+1)
  return $ "a" <> show nextVar

-- Raise a type error
typeError :: Posn -> String -> Error a
typeError p msg = Left (p, msg)

traceIfDebug :: Bool -> String -> Either e ()
traceIfDebug debug msg = if debug then trace msg (Right ()) else Right ()

-- Constraint unification
unify :: Bool -> Constraints -> Error Substitution
unify debug constraints 
  | S.null constraints = Right M.empty -- no more constraints
  | Just (Constraint (t1, t2, posn), cnstr') <- S.minView constraints = do
      if t1 == t2 then unify debug cnstr'  -- trivial binding
      else case (t1, t2) of
        (TVar a, _) | not (occursFreeType a t2) -> do
            let subst = M.singleton a t2
            _ <- traceIfDebug debug ("Applying substitution: " ++ show subst) 
            subst' <- unify debug (applySubstCnstr cnstr' subst)
            let sub_union = M.union subst subst'
            _ <- traceIfDebug debug ("SubstitutionSet: " ++ show sub_union)
            let t2' = applySubst t2 sub_union
            return $ M.insert a t2' subst'
        (_, TVar a) | not (occursFreeType a t1) -> do
            let subst = M.singleton a t1
            _ <- traceIfDebug debug ("Applying substitution: " ++ show subst) 
            subst' <- unify debug (applySubstCnstr cnstr' subst)
            let sub_union = M.union subst subst'
            _ <- traceIfDebug debug ("SubstitutionSet: " ++ show sub_union)
            let t1' = applySubst t1 sub_union
            return $ M.insert a t1' subst'
        (TArrow t11 t12, TArrow t21 t22) -> do
            let c' = [(t11, t21, posn), (t12, t22, posn)]
            let c_union = insertCnstr c' cnstr'
            _ <- traceIfDebug debug ("Constraints: " ++ showConstraints c_union) 
            unify debug c_union
        (TProd t11 t12, TProd t21 t22) -> do
            let c' = [(t11, t21, posn), (t12, t22, posn)]
            let c_union = insertCnstr c' cnstr'
            _ <- traceIfDebug debug ("Constraints: " ++ showConstraints c_union) 
            unify debug c_union
        (TSum t11 t12, TSum t21 t22) -> do
            let c' = [(t11, t21, posn), (t12, t22, posn)]
            let c_union = insertCnstr c' cnstr'
            _ <- traceIfDebug debug ("Constraints: " ++ showConstraints c_union) 
            unify debug c_union
        (TList t1, TList t2) -> do
            let c' = [(t1, t2, posn)]
            let c_union = insertCnstr c' cnstr'
            _ <- traceIfDebug debug ("Constraints: " ++ showConstraints c_union) 
            unify debug c_union
        _ -> Left (posn, "Could not unify " ++ showType t1 ++ " with " ++ showType t2 ++ ".\n")


-- Constraint and type generation
inferType :: Bool -> Ctx -> Exp -> TypeInf (Type, Constraints)
-- Variables
inferType debug env (Var p x) = do 
  _ <- lift $ traceIfDebug debug ("Environment: " ++ showCtx env) 
  case M.lookup x env of 
    Just (Type typ) -> return (typ , S.empty)
    Just scheme@(Forall _ _) -> do 
      typ <- instantiate scheme 
      return (typ, S.empty)
    Nothing -> lift $ typeError p ("Unbound variable" ++ x)
-- Application
inferType debug env (App _ e1 e2) = do 
  (t1, c1) <- inferType debug env e1 
  (t2, c2) <- inferType debug env e2
  a <- freshTVar 
  let c_union = insertCnstr [(t1, TArrow t2 (TVar a), getPosn e1)] (S.union c1 c2)  -- union of constraints
  _ <- lift $ traceIfDebug debug ("Constraints(App): " ++ showConstraints c_union) 
  return (TVar a, c_union) 
-- Abstraction
inferType debug env (Abs _ x (Just tx) _ f) =  do --  CT-AbsAnnot
  (tf, cf) <- inferType debug (M.insert x (Type tx) env) f
  return (TArrow tx tf, cf)
inferType debug env (Abs _ x _ _ f) = do    -- CT-Abs
  a <- freshTVar
  (tf, cf) <- inferType debug (M.insert x (Type (TVar a)) env) f
  return (TArrow (TVar a) tf, cf)
-- Unit
inferType debug _ (Unit _) = return (TUnit, S.empty)
-- Nums 
inferType debug _ (NumLit _ _) = return (TInt, S.empty)
-- Booleans 
inferType debug _ (BoolLit _ _) = return (TBool, S.empty)
-- if-then-else
inferType debug env (ITE _ e1 e2 e3) = do 
  (t1, c1) <- inferType debug env e1 
  (t2, c2) <- inferType debug env e2 
  (t3, c3) <- inferType debug env e3 
  let c' = [(t1, TBool, getPosn e1), (t2, t3, getPosn e3)]
  let c_union = insertCnstr c' (S.unions [c1, c2, c3])
  _ <- lift $ traceIfDebug debug ("Constraints(ITE): " ++ showConstraints c_union)  
  return (t2, c_union)
-- operators 
inferType debug env (Bop _ bop e1 e2) | bop == Plus || bop == Minus || bop == Mult || bop == Div = do 
  (t1, c1) <- inferType debug env e1;
  (t2, c2) <- inferType debug env e2;
  -- avoid some redundant constraints
  let c' = [(t1, TInt, getPosn e1) | t1 /= TInt] ++ [(t2, TInt, getPosn e2) | t2 /= TInt] 
  let c_union = insertCnstr c' (S.union c1 c2)
  _ <- lift $ traceIfDebug debug ("Constraints(Bop-Int): " ++ showConstraints c_union)
  return (TInt, c_union) 
inferType debug env (Bop _ bop e1 e2) | bop == Lt || bop == Le || bop == Gt || bop == Ge = do 
  (t1, c1) <- inferType debug env e1
  (t2, c2) <- inferType debug env e2
  let c' = [(t1, TInt, getPosn e1) | t1 /= TInt] ++ [(t2, TInt, getPosn e2) | t2 /= TInt] 
  let c_union = insertCnstr c' (S.union c1 c2)
  _ <- lift $ traceIfDebug debug ("Constraints(Bop-Int): " ++ showConstraints c_union)
  return (TBool, c_union) 
inferType debug env (Bop _ bop e1 e2) | bop == And || bop == Or = do 
  (t1, c1) <- inferType debug env e1
  (t2, c2) <- inferType debug env e2
  let c' = [(t1, TBool, getPosn e1) | t1 /= TBool] ++ [(t2, TBool, getPosn e2) | t2 /= TBool]  
  let c_union = insertCnstr c' (S.union c1 c2)
  _ <- lift $ traceIfDebug debug ("Constraints(Bop-Bool): " ++ showConstraints c_union) 
  return (TBool, c_union) 
inferType debug env (Bop _ Eq e1 e2) =  do 
    (t1, c1) <- inferType debug env e1;
    (t2, c2) <- inferType debug env e2;
    let c_union = insertCnstr [(t1, t2, getPosn e1)] (S.union c1 c2) 
    _ <- lift $ traceIfDebug debug ("Constraints(Bop-Eq): " ++ showConstraints c_union) 
    return (TBool, c_union)
inferType debug env (Uop _ Not e) = do 
  (t, c) <- inferType debug env e 
  let c' = if t == TBool then c else insertCnstr [(t, TBool, getPosn e)] c 
  _ <- lift $ traceIfDebug debug ("Constraints(Uop): " ++ showConstraints c')
  return (TBool, c')
-- Pairs 
inferType debug env (Pair _ p1 p2) = do 
  (t1, c1) <- inferType debug env p1 
  (t2, c2) <- inferType debug env p2 
  let c_union = S.union c1 c2 
  _ <- lift $ traceIfDebug debug ("Constraints(Pair): " ++ showConstraints c_union)
  return (TProd t1 t2, c_union)
inferType debug env (Fst _ p) = do 
  (t, c) <- inferType debug env p 
  a <- freshTVar 
  b <- freshTVar
  let c' = insertCnstr [(t, TProd (TVar a) (TVar b), getPosn p)] c 
  _ <- lift $ traceIfDebug debug ("Constraints(Fst): " ++ showConstraints c') 
  return (TVar a, c') 
inferType debug env (Snd _ p) = do 
  (t, c) <- inferType debug env p 
  a <- freshTVar 
  b <- freshTVar
  let c' = insertCnstr [(t, TProd (TVar a) (TVar b), getPosn p)] c 
  _ <- lift $ traceIfDebug debug ("Constraints(Snd): " ++ showConstraints c') 
  return (TVar b, c') 
-- Lists 
inferType debug _ (Nil _) = do 
  a <- freshTVar
  return (TList (TVar a), S.empty)
inferType debug env (Cons _ e1 e2) = do 
  (t1, c1) <- inferType debug env e1 
  (t2, c2) <- inferType debug env e2 
  let c' = [(t2, TList t1, getPosn e2)]
  let c_union = insertCnstr c' (S.union c1 c2) 
  _ <- lift $ traceIfDebug debug ("Constraints(Cons): " ++ showConstraints c_union) 
  return (TList t1, c_union)
inferType debug env (CaseL _ e1 e2 x y e3) = do -- what?
  (t1, c1) <- inferType debug env e1                  -- empty branch        
  a <- freshTVar
  (t2, c2) <- inferType debug env e2
  let env' = M.insert x (Type (TVar a)) env           -- head 
  let env'' = M.insert y (Type (TList (TVar a))) env' -- tail  
  (t3, c3) <- inferType debug env'' e3
  let c' = [(t1, TList (TVar a), getPosn e1), (t3, t2, getPosn e3)]
  let c_union = insertCnstr c' (S.unions [c1, c2, c3])
  _ <- lift $ traceIfDebug debug ("Constraints(CaseL): " ++ showConstraints c_union) 
  return (t2, c_union)
-- Sums 
inferType debug env (Inl _ l) = do 
  (t, c) <- inferType debug env l 
  a <- freshTVar 
  return (TSum t (TVar a), c) 
inferType debug env (Inr _ r) = do 
  (t, c) <- inferType debug env r 
  a <- freshTVar 
  return (TSum (TVar a) t, c) -- TODO! constraints here ?
inferType debug env (Case _ e1 x e2 y e3) = do 
  (t1, c1) <- inferType debug env e1 
  a <- freshTVar 
  (t2, c2) <- inferType debug (M.insert x (Type (TVar a)) env) e2 
  b <- freshTVar 
  (t3, c3) <- inferType debug (M.insert y (Type (TVar b)) env) e3
  let c' = [(t1, TSum (TVar a) (TVar b), getPosn e1), (t2, t3, getPosn e3)]  
  let c_union = insertCnstr c' (S.unions [c1, c2, c3])
  _ <- lift $ traceIfDebug debug ("Constraints(Case): " ++ showConstraints c_union)
  return (t2, c_union)
-- Let 
inferType debug env (Let _ x (Just tx) e1 e2) = do -- Annotated
  (t1, c1) <- inferType debug env e1;
  (t2, c2) <- inferType debug (M.insert x (Type tx) env) e2 
  let c_union = insertCnstr [(t1, tx, getPosn e1)] (S.union c1 c2)
  _ <- lift $ traceIfDebug debug ("Constraints(Let-Annot): " ++ showConstraints c_union) 
  return (t2, c_union)
--introduce let-polymorphism here
inferType debug env (Let _ x _ e1 e2) = do 
  (t1, c1) <- inferType debug env e1 
  subst <- lift $ unify debug c1
  let t1' = applySubst t1 subst  
  let env' = applySubstEnv env subst 
  let s1 = generalize env' t1' 
  _ <- lift $traceIfDebug debug ("Generalised type: " ++ showTypeScheme s1)
  (t2, c2) <- inferType debug (M.insert x s1 env') e2 
  let c' = S.union c1 c2 -- TODO! is subst needed here?
  _ <- lift $ traceIfDebug debug ("Constraints(Let): " ++ showConstraints c') 
  return (t2, c')
-- LetRec with polymorphism
inferType debug env (LetRec pos f x tx tf e1 e2) = do
  tin <- case tx of 
    Just typx -> return typx 
    Nothing -> do 
      a <- freshTVar
      return (TVar a) 
  tout <- case tf of 
    Just typf -> return typf 
    Nothing -> do 
      b <- freshTVar
      return (TVar b) 

  let env' = M.insert x (Type tin) env  
      env'' = M.insert f (Type (TArrow tin tout)) env'
  (t1, c1) <- inferType debug env'' e1
  let c1' = insertCnstr [(t1, tout, pos)] c1 
  subst1 <- lift $ unify debug c1'
  let tf' = applySubst (TArrow tin tout) subst1
      -- Here, use the original environment (without f) for generalization.
      sub_env = applySubstEnv env subst1  
      sub_env' = M.delete f sub_env
      sf = generalize sub_env' tf'
  -- Now, in e2, bind f with its fully generalized (polymorphic) type.
  (t2, c2) <- inferType debug (M.insert f sf sub_env) e2
  let c_union = S.union c1' c2
  _ <- lift $ traceIfDebug debug ("Constraints(LetRec): " ++ showConstraints c_union)
  return (t2, c_union)


-- Top-level type inference function with an empty context
inferTypeTop :: Exp -> Error TypeScheme
inferTypeTop exp = do 
  let debug = False           -- if set True : prints constraints & environment updates
  case runStateT (inferType debug M.empty exp) (MkTIState 0) of 
    Left (p, msg) -> Left (p, msg)  -- Report type error
    Right ((t, constraints), _) -> 
      case unify debug constraints of    
        Left (p, msg) -> Left (p, msg)  -- Report unification failure
        Right subst -> do 
          _ <- traceIfDebug debug ("Final Substitution: " ++ show subst ++ " in inferred type " ++ showType t) 
          let inferredMono = applySubst t subst 
              inferredScheme = Type inferredMono
              finalScheme = case inferredScheme of
                              Type ty -> generalize M.empty ty
                              forallScheme@(Forall _ _) -> forallScheme
          Right finalScheme

-- Various helper functions

-- Apply a substitution to a type
applySubst :: Type -> Substitution -> Type
applySubst TUnit _ = TUnit
applySubst TInt _ = TInt
applySubst TBool _ = TBool
applySubst (TArrow t1 t2) subst = TArrow (applySubst t1 subst) (applySubst t2 subst)
applySubst (TProd t1 t2) subst = TProd (applySubst t1 subst) (applySubst t2 subst)
applySubst (TSum t1 t2) subst = TSum (applySubst t1 subst) (applySubst t2 subst)
applySubst (TList t) subst = TList (applySubst t subst)
applySubst (TVar a) subst = case M.lookup a subst of
  Just ty -> ty
  Nothing -> TVar a

-- Apply a substitution to a set of constraints
applySubstCnstr :: Constraints -> Substitution -> Constraints
applySubstCnstr cnstr subst =
  S.map (\(Constraint (t1, t2, pos)) -> Constraint (applySubst t1 subst, applySubst t2 subst, pos)) cnstr

-- Apply a substitution to a type scheme
applySubstTypeScheme :: TypeScheme -> Substitution -> TypeScheme
applySubstTypeScheme (Type t) subst = Type $ applySubst t subst
applySubstTypeScheme (Forall xs t) subst = Forall xs $ applySubst t (foldr M.delete subst xs)

-- Apply a substitution to a typing environment
applySubstEnv :: Ctx -> Substitution -> Ctx
applySubstEnv ctx subst = M.map (flip applySubstTypeScheme subst) ctx


-- Extend a substitution. Essentially the composition of a substitution subst
-- with a singleton substitution [x -> typ].
-- Extend a substitution. Essentially the composition of a substitution subst
-- with a singleton substitution [x -> typ].
extendSubst :: Substitution -> String -> Type -> Substitution
extendSubst subst x typ = 
    let newsubst = M.insert x typ subst in 
    M.map (\t -> applySubst t newsubst) newsubst


-- Instantiate universal type variables with fresh ones
instantiate :: TypeScheme -> TypeInf Type
instantiate (Type typ) = error "Must be applied to universal types only.\n"
instantiate (Forall vars typ) 
  |  null vars = return typ          
  |  otherwise = do       -- proceed with 1 var rename at a time
      x' <- freshTVar 
      instantiate (Forall (tail vars) (rename (head vars, x') typ)) 


-- Generalize a the free type variables in a type
generalize :: Ctx -> Type -> TypeScheme
generalize env typ = 
  let freeTypVars = nub (getFreeVars typ)  
      genVars = filter (\x -> not (occursFreeCtx x env)) freeTypVars
  in Forall genVars typ
      where 
        getFreeVars :: Type -> [String]
        getFreeVars TUnit = []
        getFreeVars TInt = []
        getFreeVars TBool = []
        getFreeVars (TVar a) = [a]  
        getFreeVars (TArrow t1 t2) = getFreeVars t1 ++ getFreeVars t2
        getFreeVars (TProd t1 t2) = getFreeVars t1 ++ getFreeVars t2
        getFreeVars (TSum t1 t2) = getFreeVars t1 ++ getFreeVars t2
        getFreeVars (TList t) = getFreeVars t


-- Rename a free type variable in a type
rename :: (String, String) -> Type -> Type
rename _ TUnit = TUnit
rename _ TInt = TInt
rename _ TBool = TBool
rename subst (TArrow t1 t2) = TArrow (rename subst t1) (rename subst t2)
rename subst (TProd t1 t2) = TProd (rename subst t1) (rename subst t2)
rename subst (TSum t1 t2) = TSum (rename subst t1) (rename subst t2)
rename subst (TList t) = TList (rename subst t)
rename (x, y) (TVar a) = if x == a then TVar y else TVar a

-- Check if a type variable occurs free in a type
occursFreeType :: String -> Type -> Bool
occursFreeType x (TVar a) = x == a
occursFreeType _ TUnit = False
occursFreeType _ TInt = False
occursFreeType _ TBool = False
occursFreeType x (TSum t1 t2) = occursFreeType x t1 || occursFreeType x t2
occursFreeType x (TProd t1 t2) = occursFreeType x t1 || occursFreeType x t2
occursFreeType x (TArrow t1 t2) = occursFreeType x t1 || occursFreeType x t2
occursFreeType x (TList t) = occursFreeType x t

-- Check if a type variable occurs free in a type scheme
occursFreeTypeScheme :: String -> TypeScheme -> Bool
occursFreeTypeScheme x (Type ty) = occursFreeType x ty
occursFreeTypeScheme x (Forall ys ty) = notElem x ys && occursFreeType x ty

-- Check if a type variable occurs free in a typing environment
occursFreeCtx :: String -> Ctx -> Bool
occursFreeCtx x = M.foldr ((||) . occursFreeTypeScheme x) False
