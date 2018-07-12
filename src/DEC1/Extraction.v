(* David Nowak, with Paolo Torrini 
   Universite' Lille-1 - CRIStAL-CNRS
*)
(* Haskell program extraction of the DEC1 interpreter *)

Require Import ExtrHaskellBasic ExtrHaskellString ExtrHaskellNatInt.
Require Import IdModTypeA DetermA Test_Nat1A Test_Convert Test_LEnvA.

Module Import M1 := Determ(Test_LEnv).
Module Import M2 := Determ(Test_Nat1).
Module Import M3 := Determ(Convert2).

Extraction Language Haskell.

Extraction "Interpreter"
  Test_LEnv.expTypingTest1 Test_LEnv.expTypingline3
  Test_Nat1.expTypingline3
  Convert2.expTypingTestDAppA.

(* Note:
   The output - Interpreter.hs - can be compiled with GHC 7.10.3. 

   To compile with GHC 8.2.2, replace 
       type Any = GHC.Prim.Any
   with
       type Any = GHC.Base.Any      
*)
