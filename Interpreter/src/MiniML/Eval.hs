module MiniML.Eval where

import qualified Data.Map as M
import Control.Monad.State

import MiniML.Syntax
import MiniML.Error
import MiniML.Values


-- MiniML evaluation

-- Make sure to look at Values.hs for the associated data types.

-- The evaluation state.
type EvalState = ( Env     -- An environment mapping variables to their values.
                 , Store   -- A store mapping memory locations to values.
                 , Loc     -- The next available memory location. Needed when allocation new references.
                 )

-- The type of the evaluation computation.
type Eval = StateT EvalState (Either (Posn,String))

-- `StateT` is the monad transformer for the State monad. It allows you to put
-- an arbitrary monad inside the State. Here, we put an Error monad inside the
-- result of the state, composing the State monad with the Error monad.

-- The resulting monad, `Eval`, manages both mutable state and error propagation
-- within a single monad.

-- Essentially, the type `Eval a` represents a computation of type `EvalState -> (EvalState, Error a)`

-- Note 1: In the definition of `Eval`, we use `Either (Posn, String)` directly
-- instead of the type synonym `Error` (defined in Error.hs) because Haskell
-- does not allow partially applied type synonyms.

-- Note 2: Technically, we could have used a reader monad for Env, but it makes
-- our definitions simpler to put it in the state and avoid composing too many
-- monads.

-- Useful functions for handling the state.

-- Get the environment
getEnv :: Eval Env
getEnv = do
  (env, _, _) <- get
  return env

-- Update the environment
putEnv :: Env -> Eval ()
putEnv env = do
  (_, store, l) <- get
  put (env, store, l)

-- Get the store
getStore :: Eval Store
getStore = do
  (_, store, _) <- get
  return store

-- Update the store
putStore :: Store -> Eval ()
putStore store = do
  (env, _, l) <- get
  put (env, store, l)

-- Run a computation in the provided environment
localEnv :: Env -> Eval a -> Eval a
localEnv env m = do
  env' <- getEnv
  putEnv env
  x <- m
  putEnv env'
  return x

-- Update the store using the given function and run a computation
withStore :: (Store -> Store) -> Eval a -> Eval a
withStore f m = do
  store <- getStore
  putStore (f store)
  m

-- Return a fresh location and increase the location counter
freshLoc :: Eval Loc
freshLoc = do
  (store, env, l) <- get
  let l' = l + 1
  put (store, env, l')
  return l'

-- Throw an error.
throwErr :: Posn -> String -> Eval a
throwErr p str = lift (throw (p,str))

-- Main evaluation function.

-- TODO 2: Fill in the definition for the evaluation function.

-- Make sure to correctly propagate the types to closure values. This should be
-- available as type annotations in the input program (Do not use the
-- typechecking function in te evaluation function!). You can assume that the
-- input programs will never have the form `Abs p x t Nothing e` (i.e., return
-- type annotations will be filled).

eval :: Exp -> Eval Value
-- Variables
eval (Var p x)               = do 
  env <- getEnv 
  case M.lookup x env of 
    Just v -> return v 
    _ -> throwErr p "Undeclared Variable " 
-- abstraction 
eval (Abs _ x t (Just mt) e) = do
  env <- getEnv
  return (VClo env "_fun" x t mt e)
-- Numbers 
eval (NumLit _ n)            = return (VNum n) 
-- Booleans
eval (BoolLit _ b)           = return (VBool b)
-- Unit
eval (Unit _)                = return VUnit
-- Pairs 
eval (Pair _ e1 e2)          = do 
  v1 <- eval e1 
  v2 <- eval e2
  return (VPair v1 v2) 
eval (Fst _ p)               = do 
  v <- eval p 
  case v of 
    (VPair v1 _) -> return v1 
    _ -> throwErr (getPosn p) "Fst operator must be applied only to value VPair "
eval (Snd _ p)               = do 
  v <- eval p 
  case v of 
    (VPair _ v2) -> return v2
    _ -> throwErr (getPosn p) "Snd operator must be applied only to value VPair"
-- Sums 
eval (Inl _ t e)             = do 
  v <- eval e 
  return (VInl t v)
eval (Inr _ t e)             = do 
  v <- eval e 
  return (VInr t v)
eval (Case _ e x e1 y e2)    = do 
  v <- eval e 
  case v of 
    (VInl tl vl) -> do 
      env <- getEnv
      localEnv (M.insert x vl env) (eval e1)
    (VInr tr vr) -> do 
      env <- getEnv
      localEnv (M.insert y vr env) (eval e2)
    _ -> throwErr (getPosn e) "Expected value VInl or VInr, got expression " 
-- ITE
eval (ITE _ e1 e2 e3)         = do 
  v <- eval e1 
  case v of 
    (VBool True)  -> eval e2  
    (VBool False) -> eval e3 
    _ -> throwErr (getPosn e1) "Expected value VBool ('true' or 'false')"
-- Bop 
eval (Bop p bop e1 e2)        = do
  v1 <- eval e1 
  v2 <- eval e2 
  case (v1,v2) of 
    (VNum n1, VNum n2) -> case bop of 
      Plus -> return (VNum (n1 + n2))
      Minus -> return (VNum (n1 - n2))
      Mult -> return (VNum (n1 * n2))
      Div -> return (VNum (n1 `div` n2))
      Lt -> return (VBool (n1 < n2))
      Gt -> return (VBool (n1 > n2))
      Le -> return (VBool (n1 <= n2))
      Ge -> return (VBool (n1 >= n2))
      Eq -> return (VBool (n1 == n2)) 
      _ -> throwErr p "Expected an arithmetic operator" 
    (VBool b1, VBool b2) -> case bop of 
      And -> return (VBool (b1 && b2))
      Or -> return (VBool (b1 || b2))
      Eq -> return (VBool (b1 == b2))
      _ -> throwErr p "Expected a boolean operator"
    _ -> throwErr p "Expected operands with values either <VNum, VNum> or <VBool, VBool>"
-- Uop 
eval (Uop _ uop e)            = do 
  v <- eval e 
  case v of 
    (VBool b) -> 
      if uop == Not then return (VBool (not b))
      else throwErr (getPosn e) "Expected a unary operator ('Not')"
    _ -> throwErr (getPosn e) "Expected value VBool"
-- let 
eval (Let _ x t e1 e2)        = do 
  env <- getEnv
  v1 <- eval e1  
  localEnv (M.insert x v1 env) (eval e2)
-- app 
eval (App _ e1 e2)            = do 
  v1 <- eval e1 
  case v1 of 
    (VClo fenv _ x _ _ e) -> do 
      v2 <- eval e2 
      localEnv (M.insert x v2 fenv) (eval e)
    _ -> throwErr (getPosn e1) "Expected abstraction as an applicable term" 
-- references 
eval (Ref _ e)               = do
  v <- eval e 
  st <- getStore
  loc <- freshLoc
  withStore (M.insert loc v) (return (Memloc loc))
eval (Deref _ e)             = do 
  v <- eval e 
  case v of 
    (Memloc l) -> do 
      st <- getStore 
      case M.lookup l st of 
        (Just x) -> return x 
        _ -> throwErr (getPosn e) "Segmentation Fault"
    _ -> throwErr (getPosn e) "Expected address (value VNum)"
eval (Asgn _ e1 e2)            = do 
  v1 <- eval e1
  v2 <- eval e2
  case v1 of 
    (Memloc l) -> withStore (M.insert l v2) (return VUnit) 
    _ -> throwErr (getPosn e1) "Expected address (value VNum)" 
-- letrec
eval (LetRec _ f x t1 t2 e1 e2) = do
  env <- getEnv
  let recClo = VClo env' f x t1 t2 e1
      env' = M.insert f recClo env
  putEnv env' 
  eval e2

eval _ =  return VUnit
  

-- Top-level evaluation function. Runs the main evaluation function on an empty
-- state and extracts the value and the store. Note that the store is needed as
-- the value may contain memory locations.
evalTop :: Exp -> Error (Value,Store)
evalTop e = do
  let initState = (M.empty, M.empty, 0)
  (val, (_, store, _)) <- runStateT (eval e) initState
  return (val, store)