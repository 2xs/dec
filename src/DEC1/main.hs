module Main where

import Prelude
import Interpreter

main :: IO ()
main = do
  -- cst 2
  print $ (
    (unsafeCoerce (
        extractRunShallow
          undefined undefined undefined undefined undefined 
          (Val_Typing [] [] [] (cst 2) ()) MatchEnvs_NilT [] MatchEnvs_NilT 3)) :: (Int, Int)) 
  -- Test_LEnv.expTypingTest1
  print $ (
    (unsafeCoerce (
        extractRunShallow1
          undefined undefined undefined undefined undefined expTypingTest1 MatchEnvs_NilT [] MatchEnvs_NilT  [("Hello", 4::Int)])) :: (Int,[(String, Int)]))
  -- Test_LEnv.expTypingline1
  print $ (
    (unsafeCoerce (
        extractRunShallow1
          undefined undefined undefined undefined undefined expTypingline0 MatchEnvs_NilT [] MatchEnvs_NilT  [("Hello", 4::Int)])) :: (Int,[(String, Int)]))
  -- Test_LEnv.expTypingline2
  print $ (
    (unsafeCoerce (
        extractRunShallow1
          undefined undefined undefined undefined undefined expTypingline4 MatchEnvs_NilT [] MatchEnvs_NilT  [("Hello", 4::Int)])) :: (Int,[(String, Int)]))
  -- Test_LEnv.expTypingline3
  print $ (
    (unsafeCoerce (
        extractRunShallow1
          undefined undefined undefined undefined undefined expTypingline5 MatchEnvs_NilT [] MatchEnvs_NilT  [("Hello", 4::Int)])) :: (Int,[(String, Int)]))
  -- Test_Nat1.expTypingline1
  print $ (
    (unsafeCoerce (
        extractRunShallow
          undefined undefined undefined undefined undefined expTypingline1 MatchEnvs_NilT [] MatchEnvs_NilT 4)) :: (Int, Int))
  -- Test_Nat1.expTypingline2
  print $ (
    (unsafeCoerce (
        extractRunShallow
          undefined undefined undefined undefined undefined expTypingline2 MatchEnvs_NilT [] MatchEnvs_NilT 4)) :: (Int, Int))
  -- Test_Nat1.expTypingline3
  print $ (
    (unsafeCoerce (
        extractRunShallow
          undefined undefined undefined undefined undefined expTypingline3 MatchEnvs_NilT [] MatchEnvs_NilT 4)) :: (Int, Int))
  -- Convert2.expTypingTestDAppA
  print $ (
    (unsafeCoerce (
        extractRunShallow0
          undefined undefined undefined undefined undefined (expTypingTestDAppA [] [] [] MatchEnvs_NilT) MatchEnvs_NilT [] MatchEnvs_NilT 5)) :: (Int, Int))
