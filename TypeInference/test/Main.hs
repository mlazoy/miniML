module Main (main) where

import Test.Tasty
import Test.Tasty.QuickCheck

import qualified Data.Map as M
import qualified Data.Set as S 

import MiniML
import Gen

-- The main testing function. Runs a series of tests. Add as many additional
-- tests as you want.

main :: IO ()
main = defaultMain $ testGroup "act"
  [ testProperty "Parser round trip" parserRoundTrip
  , testProperty "Type inference" testTypeInf
  , testProperty "Placeholder" someProperty ]

-- A property that for a randomly MiniML as pretty-printing it and parsing it
-- produces the original program (i.e., `parse . lex . showExp == id`)
parserRoundTrip :: Property
parserRoundTrip =
  forAll genExp (\e ->
    let txt = showExp e in
    case parse $ lexer txt of
      Left err -> whenFail (prettyErrs txt err) (counterexample "Parsing failed!" False)
      Right e' -> e === e')


testTypeInf :: Property
testTypeInf = forAll genExpType $ \(exp, gen_typ) ->
  case inferTypeTop exp of 
    Left err -> counterexample ("\nType error: " ++ show err) False 
    Right inf_typ_scheme -> do 
          let inf_typ = case inf_typ_scheme of 
                  Type typ -> typ 
                  Forall _ t -> t
                  in 
              case unify False (insertCnstr [(gen_typ, inf_typ, nowhere)] S.empty) of
              Right subst -> applySubst inf_typ subst === gen_typ
              Left err  -> counterexample ("\nUnification error: " ++ show err) False 

someProperty :: Property
someProperty =
  forAll (choose (5,10 :: Int)) (<= 10)
