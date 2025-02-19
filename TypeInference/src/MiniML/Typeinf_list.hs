module MiniML.Typeinf where

import qualified Data.Map as M
import Control.Monad.State
import Data.List (nub) -- nub removes duplicates from a list. You may find it helpful.

import MiniML.Syntax
import MiniML.Error
import MiniML.Print -- For better error messages
import Debug.Trace -- Debug.Trace is your friend


-- A Typing context
type Ctx = M.Map String TypeScheme
-- Pretty-printing for context
showCtx :: Ctx -> String
showCtx ctx = unlines [x ++ " : " ++ showTypeScheme ts | (x, ts) <- M.toList ctx]

-- Typing constraints.
-- You may want to change the representation of constraints to use a more
-- efficient data structure.
type Constraints = [(Type, Type, Posn)]
-- Pretty-print a single constraint
showConstraint :: (Type, Type, Posn) -> String
showConstraint (t1, t2, pos) =
  "At " ++ show pos ++ ": " ++ showType t1 ++ " == " ++ showType t2
-- Pretty-print a list of constraints
showConstraints :: Constraints -> String
showConstraints cs = unlines (map showConstraint cs)

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
unify debug [] = Right M.empty -- no more constraints
unify debug ((t1, t2, posn):cnstr')   
  | t1 == t2 = unify debug cnstr'   -- trivial
  | (TVar a) <- t1, not (occursFreeType a t2) = do 
    let subst = M.singleton a t2
    _ <- traceIfDebug debug ( "Applying substitution: " ++ show subst) 
    subst' <- unify debug (applySubstCnstr cnstr' subst)
    let sub_union = M.union subst subst'
    _ <- traceIfDebug debug ("SubstitutionSet: " ++ show sub_union) 
    return sub_union
  | (TVar a) <- t2, not (occursFreeType a t1) = do 
    let subst = M.singleton a t1
    _ <- traceIfDebug debug ( "Applying substitution: " ++ show subst) 
    subst' <- unify debug (applySubstCnstr cnstr' subst)
    let sub_union = M.union subst subst'
    _ <- traceIfDebug debug ("SubstitutionSet: " ++ show sub_union) 
    return sub_union
  | (TArrow t11 t12) <- t1, (TArrow t21 t22) <- t2 = do
    let c' = (t11, t21, posn) 
    let c'' = (t12, t22, posn)  
    let c_union = c' : c'' : cnstr'
    _ <- traceIfDebug debug ("Constraints: " ++ showConstraints c_union) 
    unify debug c_union
  | (TProd t11 t12) <- t1, (TProd t21 t22) <- t2 = do
      let c' = (t11, t21, posn) 
      let c'' = (t12, t22, posn) 
      let c_union = c' : c'' : cnstr'
      _ <- traceIfDebug debug ("Constraints: " ++ showConstraints c_union) 
      unify debug c_union
  | (TSum t11 t12) <- t1, (TSum t21 t22) <- t2 = do 
      let c' = (t11, t21, posn) 
      let c'' = (t12, t22, posn) 
      let c_union = c' : c'' : cnstr'
      _ <- traceIfDebug debug ("Constraints: " ++ showConstraints c_union) 
      unify debug c_union
  | (TList t1) <- t1, (TList t2) <- t2 = do 
    let c' = (t1, t2, posn) 
    let c_union = c' : cnstr'
    _ <- traceIfDebug debug ("Constraints: " ++ showConstraints c_union) 
    unify debug c_union
  | otherwise = 
    Left (posn, "Could not unify " ++ showType t1 ++ " with " ++ showType t2 ++ ".\n")

-- Constraint and type generation
inferType :: Bool -> Ctx -> Exp -> TypeInf (Type, Constraints)
-- Variables
inferType debug env (Var p x) = do 
  _ <- lift $ traceIfDebug debug ("Environment: " ++ showCtx env) 
  case M.lookup x env of 
    Just (Type typ) -> return (typ , [] )
    Just scheme@(Forall _ _) -> do 
      typ <- instantiate scheme 
      return (typ, [])
    Nothing -> lift $ typeError p ("Unbound variable" ++ x)
-- Application
inferType debug env (App _ e1 e2) = do 
  (t1, c1) <- inferType debug env e1 
  (t2, c2) <- inferType debug env e2
  a <- freshTVar 
  let c_union = (t1, TArrow t2 (TVar a), getPosn e1) : c1 ++ c2  -- union of constraints
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
inferType debug env (Unit _) = return (TUnit, [])
-- Nums 
inferType debug env (NumLit _ _) = return (TInt, [])
-- Booleans 
inferType debug env (BoolLit _ _) = return (TBool, [])
-- if-then-else
inferType debug env (ITE _ e1 e2 e3) = do 
  (t1, c1) <- inferType debug env e1 
  (t2, c2) <- inferType debug env e2 
  (t3, c3) <- inferType debug env e3 
  let c' = (t1, TBool, getPosn e1) 
  let c'' = (t2, t3, getPosn e3) 
  let c_union = c'' : c' : c1 ++ c2 ++ c3 
  _ <- lift $ traceIfDebug debug ("Constraints(ITE): " ++ showConstraints c_union)  
  return (t2, c_union)
-- operators 
inferType debug env (Bop _ bop e1 e2) | bop == Plus || bop == Minus || bop == Mult || bop == Div = do 
  (t1, c1) <- inferType debug env e1;
  (t2, c2) <- inferType debug env e2;
  let c1' = [(t1, TInt, getPosn e1) | t1 /= TInt] -- avoid some redundant constraints
  let c2' = [(t2, TInt, getPosn e2) | t2 /= TInt] 
  let c_union = c2' ++ c1' ++ c1 ++ c2 
  _ <- lift $ traceIfDebug debug ("Constraints(Bop-Int): " ++ showConstraints c_union)
  return (TInt, c_union) 
inferType debug env (Bop _ bop e1 e2) | bop == Lt || bop == Le || bop == Gt || bop == Ge = do 
  (t1, c1) <- inferType debug env e1
  (t2, c2) <- inferType debug env e2
  let c1' = [(t1, TInt, getPosn e1) | t1 /= TInt]
  let c2' = [(t2, TInt, getPosn e2) | t2 /= TInt] 
  let c_union = c2' ++ c1' ++ c1 ++ c2
  _ <- lift $ traceIfDebug debug ("Constraints(Bop-Int): " ++ showConstraints c_union)
  return (TBool, c_union) 
inferType debug env (Bop _ bop e1 e2) | bop == And || bop == Or = do 
  (t1, c1) <- inferType debug env e1
  (t2, c2) <- inferType debug env e2
  let c1' = [(t1, TBool, getPosn e1) | t1 /= TBool]  
  let c2' = [(t2, TBool, getPosn e2) | t2 /= TBool]  
  let c_union = c2' ++ c1' ++ c1 ++ c2 
  _ <- lift $ traceIfDebug debug ("Constraints(Bop-Bool): " ++ showConstraints c_union) 
  return (TBool, c_union) 
inferType debug env (Bop _ Eq e1 e2) =  do 
    (t1, c1) <- inferType debug env e1;
    (t2, c2) <- inferType debug env e2;
    let c_union = (t1, t2, getPosn e1) : c1 ++ c2 
    _ <- lift $ traceIfDebug debug ("Constraints(Bop-Eq): " ++ showConstraints c_union) 
    return (TBool, c_union)
inferType debug env (Uop _ Not e) = do 
  (t, c) <- inferType debug env e 
  let c' = if t == TBool then c else (t, TBool, getPosn e) : c 
  _ <- lift $ traceIfDebug debug ("Constraints(Uop): " ++ showConstraints c')
  return (TBool, c')
-- Pairs 
inferType debug env (Pair _ p1 p2) = do 
  (t1, c1) <- inferType debug env p1 
  (t2, c2) <- inferType debug env p2 
  let c_union = c1 ++ c2 
  _ <- lift $ traceIfDebug debug ("Constraints(Pair): " ++ showConstraints c_union)
  return (TProd t1 t2, c_union)
inferType debug env (Fst _ p) = do 
  (t, c) <- inferType debug env p 
  a <- freshTVar 
  b <- freshTVar
  let c' = (t, TProd (TVar a) (TVar b), getPosn p) : c 
  _ <- lift $ traceIfDebug debug ("Constraints(Fst): " ++ showConstraints c') 
  return (TVar a, c') 
inferType debug env (Snd _ p) = do 
  (t, c) <- inferType debug env p 
  a <- freshTVar 
  b <- freshTVar
  let c' = (t, TProd (TVar a) (TVar b), getPosn p) : c 
  _ <- lift $ traceIfDebug debug ("Constraints(Snd): " ++ showConstraints c') 
  return (TVar b, c') 
-- Lists 
inferType debug env (Nil _) = do 
  a <- freshTVar
  return (TList (TVar a), [])
inferType debug env (Cons _ e1 e2) = do 
  (t1, c1) <- inferType debug env e1 
  (t2, c2) <- inferType debug env e2 
  a <- freshTVar 
  let c' = (t1, TVar a, getPosn e1) 
  let c'' = (t2, TList (TVar a), getPosn e2) 
  let c_union = c' : c'' : c1 ++ c2 
  _ <- lift $ traceIfDebug debug ("Constraints(Cons): " ++ showConstraints c_union) 
  return (TList (TVar a), c_union)
inferType debug env (CaseL _ e1 e2 x y e3) = do -- what?
  (t1, c1) <- inferType debug env e1 
  (t2, c2) <- inferType debug env e2                  -- empty branch
  a <- freshTVar
  let env' = M.insert x (Type (TVar a)) env           -- head 
  let env'' = M.insert y (Type (TList (TVar a))) env' -- tail  
  (t3, c3) <- inferType debug env'' e3
  let c' = (t1, TList (TVar a), getPosn e1) 
  let c'' = (t3, t2, getPosn e3) 
  let c_union = c' : c'' : c1 ++ c2 ++ c3 
  _ <- lift $ traceIfDebug debug ("Constraints(CaseL): " ++ showConstraints c_union) 
  return (t3, c_union)
-- Sums 
inferType debug env (Inl _ l) = do 
  (t, c) <- inferType debug env l 
  a <- freshTVar 
  return (TSum t (TVar a), c) 
inferType debug env (Inr _ r) = do 
  (t, _) <- inferType debug env r -- TODO! constraints here ?
  a <- freshTVar 
  return (TSum (TVar a) t, []) 
inferType debug env (Case _ e1 x e2 y e3) = do 
  (t1, c1) <- inferType debug env e1 
  a <- freshTVar 
  (t2, c2) <- inferType debug (M.insert x (Type (TVar a)) env) e2 
  b <- freshTVar 
  (t3, c3) <- inferType debug (M.insert y (Type (TVar b)) env) e3
  let c1' = (t1, TSum (TVar a) (TVar b), getPosn e1)  
  let c2' = (t2, t3, getPosn e3)  
  let c_union = c2' : c1' : c1 ++ c2 ++ c3 
  _ <- lift $ traceIfDebug debug ("Constraints(Case): " ++ showConstraints c_union)
  return (TSum (TVar a) (TVar b), c_union)
-- Let 
inferType debug env (Let _ x (Just tx) e1 e2) = do -- Annotated
  (t1, c1) <- inferType debug env e1;
  (t2, c2) <- inferType debug (M.insert x (Type tx) env) e2 
  let c_union = (t1, tx, getPosn e1) : c1 ++ c2 
  _ <- lift $ traceIfDebug debug ("Constraints(Let-Annot): " ++ showConstraints c_union) 
  return (t2, c_union)
-- introduce let-polymorphism here
inferType debug env (Let _ x _ e1 e2) = do 
  (t1, c1) <- inferType debug env e1 
  subst <- lift (unify debug c1)  
  let t1' = applySubst t1 subst
  let s1 = generalize env t1' 
  _ <- lift $traceIfDebug debug ("Generalised type: " ++ showTypeScheme s1)
  (t2, c2) <- inferType debug (M.insert x s1 env) e2 
  let c' = c1 ++ c2 
  _ <- lift $ traceIfDebug debug ("Constraints(Let): " ++ showConstraints c') 
  return (t2, c')
inferType debug env (LetRec _ f x tx tf e1 e2) = do
  a <- freshTVar -- tx
  b <- freshTVar -- tf
  let env' = M.insert x (Type (TVar a)) env
  let env'' = M.insert f (Type (TArrow (TVar a) (TVar b))) env'
  (t1, c1) <- inferType debug env'' e1 
  (t2, c2) <- inferType debug env'' e2 
  let c1' = (t1, TVar b, getPosn e1) 
  let c2' = case (tx, tf) of 
              (Just typx, Just typf) -> [(typx, TVar a, getPosn e1), (typf, TVar b, getPosn e1)] -- Annotated
              (Just typx, _) -> [(typx, TVar a, getPosn e1)] -- parameter given
              (_ , _) -> [] -- all missing
  let c_union = c1': c2' ++ c1 ++ c2 
  _ <- lift $ traceIfDebug debug ("Constraints(LetRec): " ++ showConstraints c_union)  
  return (t2, c_union)


-- Top-level type inference function with an empty context
inferTypeTop :: Exp -> Error TypeScheme
inferTypeTop exp = do 
  let debug = True
  case runStateT (inferType debug M.empty exp) (MkTIState 0) of 
    Left (p, msg) -> Left (p, msg)  -- Report type error
    Right ((t, constraints), _) -> 
      case unify debug constraints of    
        Left (p, msg) -> Left (p, msg)  -- Report unification failure
        Right subst -> do 
          _ <- traceIfDebug debug ("Final Substitution: " ++ show subst ++ " in inferred type " ++ showType t) 
          let inferredType = applySubst t subst in
            Right (Type inferredType)  -- Returns TypeSchme not type (?)

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
  (\(t1, t2, pos) -> (applySubst t1 subst, applySubst t2 subst, pos)) <$> cnstr

-- Apply a substitution to a type scheme
applySubstTypeScheme :: TypeScheme -> Substitution -> TypeScheme
applySubstTypeScheme (Type t) subst = Type $ applySubst t subst
applySubstTypeScheme (Forall xs t) subst = Forall xs $ applySubst t (foldr M.delete subst xs)

-- Apply a substitution to a typing environment
applySubstEnv :: Ctx -> Substitution -> Ctx
applySubstEnv ctx subst = M.map (flip applySubstTypeScheme subst) ctx


-- Extend a substitution. Essentially the composition of a substitution subst
-- with a singleton substitution [x -> typ].
extendSubst :: Substitution -> String -> Type -> Substitution
extendSubst subst var typ = error "Implement me!"


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
  let freeTypVars = nub (getFreeVars typ)  in
    let boundVars = filter (\x -> not (occursFreeCtx x env)) freeTypVars in
      Forall freeTypVars typ
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
