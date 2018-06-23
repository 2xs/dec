(* David Nowak, with Paolo Torrini 
   Universite' Lille-1 - CRIStAL-CNRS
*)
(* Haskell program extraction of DEC1 interpreter - example *)

Require Import ExtrHaskellBasic ExtrHaskellNatInt.
(*Require Import ExtrOcamlBasic ExtrOcamlNatInt.*)
Require Import ProofIrrelevance PeanoNat.
Require Import IdModTypeA DetermA Test_Nat1A Test_Convert.

Module Import M1 := Determ(Test_Nat1).
Module Import M2 := Determ(Convert2).

Extraction Language Haskell.
(*Extraction Language Ocaml.*)

Extraction "interpreter" ExpEval expTypingline3 expTypingTestDAppA.

(* Note:
   The output - interpreter.hs - can be compiled with GHC 7.10.3. 

   To compile with GHC 8.2.2, replace 
       type Any = GHC.Prim.Any
   with
       type Any = GHC.Base.Any      
*)
