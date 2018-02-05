Require Import EnvLibA.
Require Import IdModTypeA.
Require Import PRelLibA.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.


Module ModNat1 <: IdModType.

  Definition Id := string.

  Definition IdEqDec := string_dec.

  Instance IdEq2 : DEq Id :=
  {
  dEq := IdEqDec
  }.

  Definition IdEq := IdEq2.
  
  Definition W := nat.

  Definition Loc_PI := valTyp_irrelevance.

  Definition BInit := 0.

  Instance WP2 : PState W :=
  {
  loc_pi := Loc_PI;
  
  b_init := BInit
  }.              

  Definition WP := WP2.
  
End ModNat1.

