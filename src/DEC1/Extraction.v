Require Import ExtrHaskellBasic ExtrHaskellNatInt.
(*Require Import ExtrOcamlBasic ExtrOcamlNatInt.*)
Require Import ProofIrrelevance PeanoNat.
Require Import IdModTypeA DetermA Test_Nat1A Test_Convert.

Module Import M1 := Determ(Test_Nat1).
Module Import M2 := Determ(Convert2).

Extraction Language Haskell.
(*Extraction Language Ocaml.*)

Extraction "interpreter" ExpEval expTypingline3 expTypingTestDAppA.
