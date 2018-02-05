Require Import EnvLibA.
Require Import PRelLibA.
Require Import IdModTypeA.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.EqNat.
Require Import Pip_state.

Module IdModP <: IdModType.
 
  Definition Id := string.

  Definition IdEqDec := string_dec.

  Instance IdEq2 : DEq Id :=
  {
  dEq := IdEqDec
  }.
  
  Definition IdEq := IdEq2.
  
  Definition W := state.

  Definition Loc_PI := valTyp_irrelevance.

  Definition BInit := {|
          currentPartition :=  defaultPage;
          memory:= @nil (paddr * value);
                      |}.

  Instance WP2 : PState W :=
  {
  loc_pi := Loc_PI;
 
  b_init := BInit
  }.             

  Definition WP := WP2.

End IdModP.

