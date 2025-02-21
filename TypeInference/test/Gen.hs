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
    frequency [ (2, elements [ TInt, TBool, TUnit ])
              , (1, liftM2 TArrow genTypeS genTypeS)
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
  n <- chooseInt (1, 200)
  x <- elements [ "x", "y", "z", "test_42", "foo_", "_bar", "z21", "f", "g", "lala"]
  return (x ++ show n)

-- Generate an expression of a given size
genExpSize :: Int -> Gen Exp
genExpSize s = case s of
    0 -> baseCases
    _ -> frequency [ (2, baseCases)
                   , (1, liftM2 (App nowhere) genExpS genExpS)
                   , (1, liftM4 (Abs nowhere) genVar genOptTypeS (return Nothing) genExpS)
                   , (1, liftM3 (ITE nowhere) genExpS genExpS genExpS)
                   , (1, liftM3 (Bop nowhere) genBop genExpS genExpS)
                   , (1, liftM  (Uop nowhere Not) genExpS)
                   , (1, liftM2 (Pair nowhere) genExpS genExpS)
                   , (1, liftM  (Fst nowhere) genExpS)
                   , (1, liftM  (Snd nowhere) genExpS)
                   , (1, liftM (Inl nowhere) genExpS)
                   , (1, liftM (Inr nowhere) genExpS)
                   , (1, liftM5 (Case nowhere) genExpS genVar genExpS genVar genExpS)
                   , (1, liftM4 (Let nowhere) genVar (Just <$> genTypeS) genExpS genExpS)
                   , (1, do
                           x <- genVar
                           liftM5 (LetRec nowhere x) genVar genOptTypeS genOptTypeS genExpS genExpS)
                   , (1, return (Nil nowhere))
                   , (1, liftM2 (Cons nowhere) genExpS genExpS)
                   , (1, liftM5 (CaseL nowhere) genExpS genExpS genVar genVar genExpS)
                   ]
  where
    genExpS = genExpSize (s-1)
    genTypeS = genTypeSize (s-1)
    baseCases = oneof [ return (Unit nowhere)
                      , liftM (NumLit nowhere) arbitrary
                      , liftM (BoolLit nowhere) arbitrary ]
  
    genOptTypeS = oneof [ Just <$> genTypeS
                        , return Nothing ]

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
                        (3, genLetRec)] -- (2, genCase), (2, genCaseL TBool)]
                    ++ zip [2..] genEnvVar 

    TInt         -> frequency $ [ (2, genNum) ]
                    ++ if s <= 0 then [] else 
                    [(10, genArithm), (3, genLet), (3, genApp),
                    (2, genFst), (2, genSnd), (4 ,genITE),
                    (3, genLetRec), (2, genCase), (2, genCaseL)]
                    ++ zip [2..] genEnvVar 

    TArrow t1 t2 -> frequency $ [ (2 , genAbs t1 t2)]
                    ++ if s <= 0 then [] else 
                    [(1, genApp), (1, genLet), (1, genLetRec)]
                    ++ zip [1..] genEnvVar
    
    TSum t1 t2  -> frequency $ [ (1, genInl t1), (1, genInr t2)]
                    ++ if s <= 0 then [] else 
                        [(1, genApp), (4, genLet), (1, genCase), (1, genCaseL)]
                    ++ zip [1..] genEnvVar

    TProd t1 t2 -> frequency $ [(1,genPair t1 t2)] 
                              ++ if s <= 0 then [] else 
                              [(3, genApp), (3, genLet), (1, genCase), (1, genCaseL) ]
                              ++ zip [3..] genEnvVar

    TUnit       -> frequency $ [(1, return (Unit nowhere))]
                              ++ if s <= 0 then [] else 
                                [(1,genApp), (1,genLet), (1, genLetRec), (1, genCaseL)] 
                                ++ zip [2..] genEnvVar                          
    
    TList t' -> frequency $ [(5, genList t'), (1, return (Nil nowhere))]  
                           ++ if s <= 0 then [] else
                              [(1, genLet), (1, genApp)]
                              ++ zip [1..] genEnvVar

  where 
    -- generate a Boolean 
    genBool = liftM (BoolLit nowhere) arbitrary 
    -- generate an Integer
    genNum = liftM (NumLit nowhere) arbitrary
    -- generate a logical op
    genLogic = liftM3 (Bop nowhere) (elements [And, Or]) 
              (genTExpSize map n TBool (s `div` 2)) (genTExpSize map n TBool (s `div` 2))
    -- generate a comparison 
    genComp = liftM3 (Bop nowhere) (elements [Lt, Le, Gt, Ge, Eq]) 
              (genTExpSize map n TInt (s `div` 2)) (genTExpSize map n TInt (s `div` 2))
    -- generate a Not 
    genNeg = liftM (Uop nowhere Not) (genTExpSize map n TBool (s `div` 2))
    -- generate an arithmetic op
    genArithm = liftM3 (Bop nowhere) (elements [Plus, Minus, Mult])
                (genTExpSize map n TInt (s `div` 2)) (genTExpSize map n TInt (s `div` 2))
     -- generate a let expression of type t 
    genLet = do
      x <- genUniqueVar n
      tx <- genType
      e1 <- genTExpSize map n tx (s `div` 2)
      e2 <- genTExpSize (addVar x tx map) (n+1) t (s `div` 2)
      return $ Let nowhere x (Just tx) e1 e2
    -- generate an application with a random type of input and output t
    genApp = do 
      t1 <- genType 
      e1 <- genTExpSize map n (TArrow t1 t) (s `div` 2)
      e2 <- genTExpSize map n t1 (s `div` 2)
      return $ App nowhere e1 e2
    -- generate a lambda abstraction
    genAbs t1 t2 = do 
      name <- genUniqueVar n
      let map' = addVar name t1 map 
      e <- genTExpSize map' (n+1) t2 (s `div` 2) 
      return $ Abs nowhere name (Just t1) (Just t2) e
    -- generates a pair of type (t1*t2)
    genPair t1 t2 = liftM2 (Pair nowhere) (genTExpSize map n t1 0) (genTExpSize map n t2 0)
    -- generate a first of type t
    genFst = do 
      t2 <- genType
      p <- genPair t t2
      return $ Fst nowhere p
    -- genSnd 
    genSnd = do 
      t1 <- genType
      p <- genPair t1 t
      return $ Snd nowhere p
    -- generate an if-the-else stmt with type t 
    genITE = liftM3 (ITE nowhere) (genTExpSize map n TBool (s `div` 2)) 
                    (genTExpSize map n t (s `div` 2)) (genTExpSize map n t (s `div` 2))
    -- generate a recursion 
    genLetRec = do 
      x <- genUniqueVar n
      tx <- elements [TInt, TBool, TUnit] -- inf loop otherwise
      f <- genUniqueVar (n+1)
      tf <- genType 
      let map' = addVar f (TArrow tx tf) map
      let map'' = addVar x tx map'
      e1 <- genTExpSize map'' (n + 2) tf (s `div` 2)
      e2 <- genTExpSize map' (n + 1) t (s `div` 2)
      return $ LetRec nowhere f x (Just tx) (Just tf) e1 e2
    -- generators for list case 
    genCaseL = do
      t_elem <- genType
      scrutinee <- genList t_elem
      nilCase <- genTExpSize map n t 0 -- size 0 is ok here
      headVar   <- genUniqueVar n
      tailVar   <- genUniqueVar (n+1)
      let map' = addVar headVar t_elem (addVar tailVar (TList t_elem) map)
      consCase  <- genTExpSize map' (n+2) t (s `div` 2)
      return $ CaseL nowhere scrutinee nilCase headVar tailVar consCase
-- generators for sum types 
    -- generate a left injection 
    genInl t' = liftM (Inl nowhere) (genTExpSize map n t' 0)
    -- generate a right injection 
    genInr t' = liftM (Inr nowhere) (genTExpSize map n t' 0)
    -- generate a Case of type t
    genCase = do
      tx <- genType 
      ty <- genType
      e1 <- genTExpSize map n (TSum tx ty) 0
      x <- genUniqueVar n
      e2 <- genTExpSize (addVar x tx map) (n+1) t (s `div` 2)
      y <- genUniqueVar (n+1)
      e3 <- genTExpSize (addVar y ty map) (n+1) t (s `div` 2)
      return $ Case nowhere e1 x e2 y e3
    -- generate an already bound variable of the given type
    genEnvVar = case M.lookup t map of
      Just xs -> [elements (fmap (Var nowhere) xs)]
      Nothing -> [] 
    -- create new variable with unique number to prevent same name given to different types
    -- n can be the size of env 
    genUniqueVar n = do
      x <- elements [ "x", "y", "z", "test_42", "foo_", "_bar", "z21", "f", "g", "lala"]
      return (x ++ show n)
    -- add a variable x with type t to the map
    addVar x typ = M.insertWith (++) typ [x]

-- handle lists separately
genList :: Type -> Gen Exp
genList t = 
  case t of
    TUnit      -> return (Nil nowhere)
    TArrow _ _ -> return (Nil nowhere)   -- list of functions ?
    TList _    -> return (Nil nowhere)   -- list of lists ?
    _ -> do
      len <- chooseInt (1, 30)  -- Choose a random length
      elems <- vectorOf len (genElem t) 
      return $ foldr (Cons nowhere) (Nil nowhere) elems  -- Construct the list

  where 
    genElem :: Type -> Gen Exp
    genElem TInt  = liftM (NumLit nowhere) arbitrary
    genElem TBool = liftM (BoolLit nowhere) arbitrary
    genElem (TProd t1 t2) = do
      e1 <- genElem t1
      e2 <- genElem t2
      return $ Pair nowhere e1 e2  
    genElem (TSum t1 t2) = do
      useLeft <- arbitrary  -- Randomly choose between Inl and Inr
      if useLeft
        then liftM (Inl nowhere) (genElem t1)
        else liftM (Inr nowhere) (genElem t2)
    genElem _ = return $ Nil nowhere

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
