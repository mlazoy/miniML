module MiniML.Typeinf where

import qualified Data.Map as M
import Control.Monad.State
import Data.List (nub, (\\)) -- nub removes duplicates from a list. You may find it helpful.

import MiniML.Syntax
import MiniML.Error
import MiniML.Print -- For better error messages
import Debug.Trace -- Debug.Trace is your friend


-- A Typing context
type Ctx = M.Map String TypeScheme

-- Typing constraints.
-- You may want to change the representation of constraints to use a more
-- efficient data structure.
type Constraints = [(Type, Type, Posn)]

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


-- Constraint unification
unify :: Constraints -> Error Substitution
unify [] = Right M.empty 
unify ((t1, t2, pos):c') = 
    case (t1, t2) of 
        _ | t1 == t2 -> unify c'
        
        (TVar a, _) | not (occursFreeType a t2) -> do 
            let substitution = M.singleton a t2 
            returnSubstitution <- unify (applySubstCnstr c' substitution) 
            let unifiedsubst = M.union substitution returnSubstitution 
            let t' = applySubst t2 unifiedsubst 
            return $ M.insert a t' returnSubstitution 
        
        (_, TVar a) | not (occursFreeType a t1) -> do 
            let substitution = M.singleton a t1 
            returnSubstitution <- unify (applySubstCnstr c' substitution) 
            let unifiedsubst = M.union substitution returnSubstitution 
            let t' = applySubst t2 unifiedsubst 
            return $ M.insert a t' returnSubstitution 

        (TArrow t11 t12, TArrow t21 t22) -> do 
            unify ((t11, t21, pos):(t12, t22, pos):c')

        (TSum t11 t12, TSum t21 t22) -> do 
            unify ((t11, t21, pos):(t12, t22, pos):c')

        (TProd t11 t12, TProd t21 t22) -> do 
            unify ((t11, t21, pos):(t12, t22, pos):c')

        (TList t11, TList t12) -> do 
            unify ((t11, t12, pos):c')

        _ -> Left (pos, "Type mismatch: " <> show t1 <> " vs " <> show t2)
            
-- Constraint and type generation
inferType :: Ctx -> Exp -> TypeInf (Type, Constraints)
-- STLC
inferType ctx (Var pos x) = do 
    case M.lookup x ctx of 
        Nothing -> lift $ typeError pos $ "Unbound variable: " <> x
        Just typeScheme -> do 
            t <- instantiate typeScheme 
            return (t, [])

inferType ctx (Abs _ param _ _ body) = do 
    tParameter <- freshTVar 
    let ctx' = M.insert param (Type (TVar tParameter)) ctx 
    (tBody, cBody) <- inferType ctx' body 
    return (TArrow (TVar tParameter) tBody, cBody)

inferType ctx (App pos e1 e2) = do 
    (te1, ce1) <- inferType ctx e1
    (te2, ce2) <- inferType ctx e2
    t <- freshTVar 

    let nc = (te1, TArrow te2 (TVar t), pos)
    return ((TVar t), nc : ce1 ++ ce2)
    
-- Units 
inferType _ (Unit _) = 
    return (TUnit, [])

-- Integers 
inferType _ (NumLit _ _) = 
    return (TInt, [])

-- Booleans 
inferType _ (BoolLit _ _) = 
    return (TBool, []) 

inferType ctx (ITE pos e1 e2 e3) = do 
    (t1, ce1) <- inferType ctx e1 
    (t2, ce2) <- inferType ctx e2 
    (t3, ce3) <- inferType ctx e3 
    
    let c1 = (t1, TBool, pos)
    let c2 = (t2, t3, pos) 
    return (t2, c1 : c2 : ce1 ++ ce2 ++ ce3)

-- Operators 
inferType ctx (Bop pos bop e1 e2) = do 
    (t1, ce1) <- inferType ctx e1 
    (t2, ce2) <- inferType ctx e2 
    let ic1 = (t1, TInt, pos)
    let ic2 = (t2, TInt, pos) 
    let bc1 = (t1, TBool, pos)
    let bc2 = (t2, TBool, pos)

    case bop of 
        Plus -> return (TInt, ic1 : ic2 : ce1 ++ ce2)
        Minus -> return (TInt, ic1 : ic2 : ce1 ++ ce2)
        Mult -> return (TInt, ic1 : ic2 : ce1 ++ ce2)
        Div -> return (TInt, ic1 : ic2 : ce1 ++ ce2)
        Eq -> return (TBool, ic1 : ic2 : ce1 ++ ce2) 
        Lt  -> return (TBool, ic1 : ic2 : ce1 ++ ce2)
        Le  -> return (TBool, ic1 : ic2 : ce1 ++ ce2)
        Gt  -> return (TBool, ic1 : ic2 : ce1 ++ ce2)
        Ge -> return (TBool, ic1 : ic2 : ce1 ++ ce2)
        And -> return (TBool, bc1 : bc2 : ce1 ++ ce2) 
        Or  -> return (TBool, bc1 : bc2 : ce1 ++ ce2)

inferType ctx (Uop pos _ e) = do 
    (t, c) <- inferType ctx e 
    let ic = (t, TBool, pos)
    return (TBool, ic : c)  


-- Pairs
inferType ctx (Pair _ e1 e2) = do 
    (t1, c1) <- inferType ctx e1 
    (t2, c2) <- inferType ctx e2 

    return (TProd t1 t2, c1 ++ c2)
    
inferType ctx (Fst pos e) = do 
    (t, c) <- inferType ctx e
    t1 <- freshTVar
    t2 <- freshTVar

    let nc = (t, TProd (TVar t1) (TVar t2), pos)

    return ((TVar t1), nc : c)

inferType ctx (Snd pos e) = do 
    (t, c) <- inferType ctx e 
    t1 <- freshTVar 
    t2 <- freshTVar

    let nc = (t, TProd (TVar t1) (TVar t2), pos)

    return ((TVar t2), nc : c)

-- Lists
inferType _ (Nil _) = do 
    t <- freshTVar 
    return (TList (TVar t), [])

inferType ctx (Cons pos e1 e2) = do 
    (t1, c1) <- inferType ctx e1 
    (t2, c2) <- inferType ctx e2 
    
    let nc = (t2, TList t1, pos)
    return (TList t1, nc : c1 ++ c2)

inferType ctx (CaseL pos e e1 x xs e2) = do 
    (te, ce) <- inferType ctx e 
    -- A fresh variable type for the List type
    t <- freshTVar
    (te1, ce1) <- inferType ctx e1 

    let ctx'' = M.insert x (Type (TVar t)) ctx
    let ctx' = M.insert xs (Type (TList (TVar t))) ctx''

    (te2, ce2) <- inferType ctx' e2 

    -- Ensure that the list type matches 
    let c1 = (te, TList (TVar t), pos)

    -- Ensure that the base case and the recursive case return the same type
    let c2 = (te1, te2, pos)

    return (te1, c1 : c2 : ce ++ ce1 ++ ce2) 

-- Sums 
inferType ctx (Case pos e x1 e1 x2 e2) = do 
    (te, ce) <- inferType ctx e 
    t1 <- freshTVar 
    t2 <- freshTVar 

    let ctx1 = M.insert x1 (Type (TVar t1)) ctx
    (te1, ce1) <- inferType ctx1 e1 

    let ctx2 = M.insert x2 (Type (TVar t2)) ctx 
    (te2, ce2) <- inferType ctx2 e2 
    
    let nc = [(te, TSum (TVar t1) (TVar t2), pos), (te1, te2, pos)]
    return (TSum (TVar t1) (TVar t2), nc ++ ce ++ ce1 ++ ce2)

inferType ctx (Inl _ e) = do 
    (t1, c) <- inferType ctx e 
    t2 <- freshTVar 
    return (TSum t1 (TVar t2), c)

inferType ctx (Inr _ e) = do 
    (t2, _) <- inferType ctx e
    t1 <- freshTVar 
    return (TSum (TVar t1) t2, [])

-- Let 
inferType ctx (Let _ x _ e1 e2) = do 
    (t1, ce1) <- inferType ctx e1 
    subst <- lift $ unify ce1 
    let t1' = applySubst t1 subst
    let ctx' = applySubstEnv ctx subst 

    let scheme = generalize ctx' t1' 
    let ctx'' = M.insert x scheme ctx' 

    (t2, ce2) <- inferType ctx'' e2 
    return(t2, ce1 ++ ce2) 


-- LetRec
inferType ctx (LetRec pos f x xType rType e1 e2) = do 
    tx <- case xType of 
        Just typ -> return typ 
        Nothing -> TVar <$> freshTVar 
    tr <- case rType of 
        Just typ -> return typ 
        Nothing -> TVar <$> freshTVar

    let tf = TArrow tx tr 

    let ctxMono = M.insert f (Type tf) ctx 
    let ctx1 = M.insert x (Type tx) ctxMono 

    (t1, ce1) <- inferType ctx1 e1

    let cr = [(t1,  tr, pos)] 
    subst <- lift $ unify (ce1 ++ cr)

    let tf' = applySubst tf subst
    let ctx2 = applySubstEnv ctx subst

    let scheme = generalize ctx2 tf' 
    let ctx3 = M.insert f scheme ctx2 

    (t2, ce2) <- inferType ctx3 e2
    return(t2, ce1 ++ cr ++ ce2)


-- Top-level type inference function with an empty context
inferTypeTop :: Exp -> Error TypeScheme
inferTypeTop e = do 
    let ctx = M.empty 
    let initialState = MkTIState { fresh = 0 }
    ((t, c), _) <- runStateT (inferType ctx e) initialState

    subst <- unify c 
    let t' = applySubst t subst 
    let scheme = generalize ctx t'
    return scheme

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
extendSubst subst x typ = 
    let newsubst = M.insert x typ subst in 
    M.map (\t -> applySubst t newsubst) newsubst

-- Instantiate universal type variables with fresh ones
instantiate :: TypeScheme -> TypeInf Type
instantiate (Type t) = 
    return t 
instantiate (Forall x t) = do 
    freshVars <- mapM (const freshTVar) x 
    let subst = M.fromList (zip x (map TVar freshVars)) 
    return $ applySubst t subst
    

-- Generalize a the free type variables in a type
generalize :: Ctx -> Type -> TypeScheme
generalize ctx t = 
    let 
        free = collectFreeVarsType t 
        bound = collectCtxVars ctx 
        gen = free \\ bound 
    in 
     Forall gen t

collectFreeVarsType :: Type -> [String] 
collectFreeVarsType TUnit = [] 
collectFreeVarsType TInt = []
collectFreeVarsType TBool = []
collectFreeVarsType (TVar x) = [x]
collectFreeVarsType (TArrow t1 t2) =
    nub (collectFreeVarsType t1 ++ collectFreeVarsType t2)
collectFreeVarsType (TProd t1 t2) = 
    nub (collectFreeVarsType t1 ++ collectFreeVarsType t2)
collectFreeVarsType (TSum t1 t2) = 
    nub (collectFreeVarsType t1 ++ collectFreeVarsType t2)
collectFreeVarsType (TList t) = 
    collectFreeVarsType t 

collectCtxVars :: Ctx -> [String]
collectCtxVars ctx = nub $ concatMap collectFreeVarsTypeScheme (M.elems ctx)

collectFreeVarsTypeScheme :: TypeScheme -> [String]
collectFreeVarsTypeScheme (Type t) = collectFreeVarsType t
collectFreeVarsTypeScheme (Forall vars t) = collectFreeVarsType t \\ vars

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

