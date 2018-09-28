(* Paolo Torrini, 
   Universite' Lille-1 - CRIStAL-CNRS
*)
(* example of concrete module *)

Require Import AuxLibI1.
Require Import TypSpecI1.
Require Import ModTypI1.
Require Import List.
Require Import String.
Require Import PeanoNat.
Require Import Omega.


Module ModNat1 <: ModTyp.

  Definition Id := string.

  Definition IdEqDec := string_dec.

  Instance IdEq2 : DEq Id :=
  {
  dEq := IdEqDec
  }.

  Definition IdEq := IdEq2.
  

  Definition W := nat.

  Definition BInit := 0.
  
  Instance WP2 : PState W :=
  {  
  b_init := BInit
  }.              

  Definition WP := WP2.
  
End ModNat1.

