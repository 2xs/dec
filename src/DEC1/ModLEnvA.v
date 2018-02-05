Require Import EnvLibA.
Require Import PRelLibA.
Require Import IdModTypeA.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Export Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.


Module ModLEnv <: IdModType.
  
  Definition Id := string.

  Definition IdEqDec := string_dec.

  Instance IdEq2 : DEq Id :=
  {
  dEq := IdEqDec
  }.

  Definition IdEq := IdEq2.
  
  Definition W := list (Id * nat).

  Definition Loc_PI := valTyp_irrelevance.

  Definition BInit := @nil (Id * nat).

  Instance WP2 : PState W :=
  {
  loc_pi := Loc_PI;
  
  b_init := BInit
  }.              

  Definition WP := WP2.
  
End ModLEnv.

