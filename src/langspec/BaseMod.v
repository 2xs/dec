(*  DEC 1.0 language specification.
   Paolo Torrini and David Nowak, 
   Universite' Lille-1 - CRIStAL-CNRS
*)

Require Import ProofIrrelevance.
Require Export String.
Require Import DEC.AuxLib.
Require Import DEC.ModTyp.

(** * DEC 1.0 base module *)
(** Defines concretely the type of identifiers and that of states. 
    NOTE: currently used in the translation of Pip, though only for the type of the identifiers. *)

Module BMod <: ModTyp.

(** Identifiers are strings *)

  Definition Id := string.

  Definition IdEqDec := string_dec.

  Instance id_eq : DEq Id :=
  {
  dEq := IdEqDec
  }.

  Definition IdEq := id_eq.

  
(** States are natural numbers (just meant as a dummy definition, as it is not used) *)  

  Definition W := nat.

  Lemma loc_pi : forall (T: Type) (p1 p2: ValTyp T), p1 = p2.
  Proof.
    intros.
    eapply proof_irrelevance.  
  Qed.
  
  Definition Loc_PI := loc_pi.


(** The state is initialised to 0 (as above) *)  
  Definition BInit := 0.

  Instance base_wp : PState W :=
  {
  loc_pi := Loc_PI;
  
  b_init := BInit
  }.              

  Definition WP := base_wp.
  
End BMod.

