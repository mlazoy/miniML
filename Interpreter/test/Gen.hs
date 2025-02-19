module Gen where

import Test.QuickCheck
import Control.Monad
import qualified Data.Map as M

import MiniML.Syntax

-- Generators for random programs

-- Simple random generators of types and terms. No well-formedness invariant.
-- Useful for testing the parser

genTypeSize :: Int -> Gen Type
genTypeSize 0 =
    elements [ TInt, TBool, TUnit ]
genTypeSize s =
    frequency [ (5, elements [ TInt, TBool, TUnit ]) -- increased this to create proper operations 
              , (2, liftM2 TArrow genTypeS genTypeS)
              , (1, liftM2 TSum genTypeS genTypeS)
              , (1, liftM2 TProd genTypeS genTypeS) ]
    where
        genTypeS = genTypeSize (s-1)

genType :: Gen Type
genType = scale (min 10) $ sized genTypeSize

genBop :: Gen Bop
genBop = elements [Plus, Minus, Mult, Div, And, Or, Lt, Gt, Le, Ge, Eq]

genVar :: Gen String
genVar = do
  n <- chooseInt (1, 20000) -- increase this to avoid aliasing
  x <- elements [ "x", "y", "z", "test_42", "foo_", "_bar", "yeah", "yolo", "haskell", "ml_is_fun", "max"
    "lol", "i", "j", "random", "shit", "pff", "z21", "f", "g", "lala", "tralala", "var", "k", "kaka", "min"]
  return (x ++ show n) 


-- Generate an expression of a given size
genExpSize :: Int -> Gen Exp
genExpSize s = case s of
    0 -> baseCases
    _ -> frequency [ (2, baseCases)
                   , (1, liftM2 (App nowhere) genExpS genExpS)
                   , (1, liftM4 (Abs nowhere) genVar genTypeS (return Nothing) genExpS)
                   , (1, liftM3 (ITE nowhere) genExpS genExpS genExpS)
                   , (1, liftM3 (Bop nowhere) genBop genExpS genExpS)
                   , (1, liftM  (Uop nowhere Not) genExpS)
                   , (1, liftM2 (Pair nowhere) genExpS genExpS)
                   , (1, liftM  (Fst nowhere) genExpS)
                   , (1, liftM  (Snd nowhere) genExpS)
                   , (1, liftM2 (Inl nowhere) genTypeS genExpS)
                   , (1, liftM2 (Inr nowhere) genTypeS genExpS)
                   , (1, liftM5 (Case nowhere) genExpS genVar genExpS genVar genExpS)
                   , (1, liftM4 (Let nowhere) genVar genTypeS genExpS genExpS)
                   , (1, do
                           x <- genVar
                           liftM5 (LetRec nowhere x) genVar genTypeS genTypeS genExpS genExpS)
                   , (1, liftM2 (Asgn nowhere) genExpS genExpS)
                   , (1, liftM  (Deref nowhere) genExpS)
                   , (1, liftM  (Ref nowhere) genExpS)
                   ]
  where
    genExpS = genExpSize (s-1)
    genTypeS = genTypeSize (s-1)
    baseCases = oneof [ return (Unit nowhere)
                      , liftM (NumLit nowhere) arbitrary
                      , liftM (BoolLit nowhere) arbitrary ]


-- Generate an expression of an arbitrary
genExp :: Gen Exp
genExp = scale (min 20) $ sized genExpSize



-- A generator for well-typed terms. You may use the generator for STLC programs
-- provided in the course notes as a reference:
-- https://github.com/zoep/PL2/blob/main/lectures/Haskell/src/QuickCheck.hs



genTExpSize :: M.Map Type [String]  -- a map from types to variables with the corresponding types
            -> Int                  -- counter for generating fresh names
            -> Type                 -- the type of the generated terms
            -> Int                  -- The size of the term.
            -> Gen Exp
genTExpSize map n t s =
  case t of
    TBool        -> frequency $ [ (2, genBool) ] 
                    ++ if s <= 0 then [] else 
                      [(5, genComp), (5, genLogic), (4, genNeg), (4, genITE),
                        (2,genLet), (2, genApp), (2, genFst), (2, genSnd),
                        (3, genLetRec), (3, genDeref)] -- ,(1, genCase)]
                    ++ zip [2..] genEnvVar 

    TInt         -> frequency $ [ (2, genNum) ]
                    ++ if s <= 0 then [] else 
                    [(10, genArithm), (3, genLet), (3, genApp),
                    (2, genFst), (2, genSnd), (4 ,genITE),
                    (3, genLetRec), (3, genDeref)] -- ,(1, genCase)]
                    ++ zip [2..] genEnvVar 

    TArrow t1 t2 -> frequency $ [ (2 , genAbs t1 t2)]
                    ++ if s <= 0 then [] else (
                    [(1, genApp), (1, genLet), (1, genLetRec)])
                    ++ zip [1..] genEnvVar
    
    TSum t1 t2  -> frequency $  [(1, genInr t1 t2), (1, genInl t1 t2)]
                                ++ if s <= 0 then [] else
                                [(3, genApp), (4, genLet) ]
                                ++ zip [4..] genEnvVar

    TProd t1 t2 -> frequency $ [(1,genPair t1 t2)] 
                              ++ if s <= 0 then [] else 
                              [(3, genApp), (3, genLet) ]
                              ++ zip [3..] genEnvVar

    TUnit       -> frequency $ [(1, return (Unit nowhere)), (3,genAsgn)]
                              ++ if s <= 0 then [] else 
                                [(1,genApp), (1,genLet), (1, genLetRec)]
                              ++ zip [1..] genEnvVar

    TRef t'     -> frequency $ [(2, genRef t')]
                              ++ if s <= 0 then [] else
                              [(1,genApp), (3,genLet), (1, genLetRec)]
                              ++ zip [3..] genEnvVar

  where 
        -- generate a Boolean 
    genBool = liftM (BoolLit nowhere) arbitrary 
    -- generate an Integer
    genNum = liftM (NumLit nowhere) arbitrary
    -- generate a logical op
    genLogic = liftM3 (Bop nowhere) (elements [And, Or]) 
              (genTExpSize map n TBool (s-1)) (genTExpSize map n TBool (s-1))
    -- generate a comparison 
    genComp = liftM3 (Bop nowhere) (elements [Lt, Le, Gt, Ge, Eq]) 
              (genTExpSize map n TInt (s-1)) (genTExpSize map n TInt (s-1))
    -- generate a Not 
    genNeg = liftM (Uop nowhere Not) (genTExpSize map n TBool (s-1))
    -- generate an arithmetic op
    genArithm = liftM3 (Bop nowhere) (elements [Plus, Minus, Mult])
                (genTExpSize map n TInt (s-1)) (genTExpSize map n TInt (s-1))
     -- generate a let expression of type t 
    genLet = do
      x <- genVar
      tx <- genType
      e1 <- genTExpSize map n tx (s-1)
      e2 <- genTExpSize (addVar x tx map) (n+1) t (s-1)
      return $ Let nowhere x tx e1 e2
    -- generate an application with a random type of input and output t
    genApp = do 
      t1 <- genType 
      e1 <- genTExpSize map n (TArrow t1 t) (s-1)
      e2 <- genTExpSize map n t1 (s-1)
      return $ App nowhere e1 e2
    -- generate a lambda abstraction
    genAbs t1 t2 = do 
      name <- genVar
      let map' = addVar name t1 map 
      e <- genTExpSize map' (n+1) t2 s 
      return $ Abs nowhere name t1 (Just t2) e
    -- generates a pair of type (t1*t2)
    genPair t1 t2 = liftM2 (Pair nowhere) (genTExpSize map n t1 0) (genTExpSize map n t2 0)
    -- generate a first of type t
    genFst = do 
      -- tsz <- elements [0,1] -- don't need more complex pairs
      t2 <- genType
      p <- genPair t t2
      return $ Fst nowhere p
    -- genSnd 
    genSnd = do 
      -- tsz <- elements [0,1] -- don't need more complex pairs
      t1 <- genType
      p <- genPair t1 t
      return $ Snd nowhere p
    -- generate a left injection 
    genInl t1 t2 = liftM (Inl nowhere t2) (genTExpSize map n t1 0)
    -- generate a right injection 
    genInr t1 t2= liftM (Inr nowhere t1) (genTExpSize map n t2 0)
    -- generate a Case of type t1 + t2
    genCase = do
      tx <- genType 
      ty <- genType
      e1 <- genTExpSize map n (TSum tx ty) 0
      x <- genVar
      e2 <- genTExpSize (addVar x tx map) (n+1) t (s `div` 2)
      y <- genVar
      e3 <- genTExpSize (addVar y ty map) (n+2) t (s `div` 2)
      return $ Case nowhere e1 x e2 y e3
    -- generate an if-the-else stmt with type t 
    genITE = liftM3 (ITE nowhere) (genTExpSize map n TBool (s-1)) 
                    (genTExpSize map n t (s-1)) (genTExpSize map n t (s-1))
    -- generate a refernece of simple types (s = 0)
    genRef tr = liftM (Ref nowhere) (genTExpSize map n tr 0) 
    -- generate a dereference 
    genDeref = do
      e <- genRefVar t
      return $ Deref nowhere e
    -- generate an assignment 
    genAsgn = do
      tr <- genType
      e2 <- genTExpSize map n tr (s - 1)
      e1 <- genRefVar tr
      return $ Asgn nowhere e1 e2
    -- generate a recursion 
    genLetRec = do 
      x <- genVar 
      tx <- elements [TInt, TBool]
      f <- genVar 
      tf <- genType 
      let map' = addVar f (TArrow tx tf) map
      let map'' = addVar x tx map'
      e1 <- genTExpSize map'' (n + 2) tf (s-1)
      e2 <- genTExpSize map' (n + 1) t (s-1)
      return $ LetRec nowhere f x tx tf e1 e2
    -- generate an already bound variable of the given type
    genEnvVar = case M.lookup t map of
      Just xs -> [elements (fmap (Var nowhere) xs)]
      Nothing -> [] 
    -- generate en already bound reference 
    genRefVar tr = case M.lookup (TRef tr) map of
      Just xs -> liftM (Var nowhere) (elements xs)  -- Select a random element from the list
      Nothing -> genRef tr
    -- add a variable x with type t to the map
    addVar x typ map = M.insertWith (++) typ [x] map



-- Top-level function for generating well-typed expressions. You may tweak them
-- if you wish, but do not change their types.

-- Generate a well-type term
genWTExp :: Gen Exp
genWTExp = do
  size <- arbitrary
  t <- genType
  genTExpSize M.empty 1 t size

-- Generate a well-type term of a certain type
genExpOfType :: Type -> Gen Exp
genExpOfType t = genTExpSize M.empty 1 t 3

-- Generate a well-type term with its type
genExpType :: Gen (Exp,Type)
genExpType = do
  t <- scale (min 10) $ sized genTypeSize
  e <- scale (min 10) $ sized $ genTExpSize M.empty 1 t
  return (e,t)
