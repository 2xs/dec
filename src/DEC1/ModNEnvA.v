Require Import EnvLibA.
Require Import PRelLibA.
Require Import IdModTypeA.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.EqNat.

Open Scope nat_scope.

Module ModNEnv <: IdModType.
  
  Definition Id := nat.

  Definition IdEqDec := eq_nat_dec.

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
  
End ModNEnv.

