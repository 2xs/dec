(* DEC 2.0 language specification.
   Paolo Torrini, 
   Universite' de Lille - CRIStAL-CNRS
*)

Require Import AuxLibI1.
Require Import TypSpecI1.

(** * DEC 2.0 module type *)

(** Abstract specification of the identifier type, 
   the state type and the initial state value *)

Module Type ModTyp.

(** Type of identifiers *)

Parameter Id : Type.

(** Decidable equality for the identifier type *)

Parameter IdEqDec : forall (x y : Id), {x = y} + {x <> y}. 

Instance IdEq : DEq Id :=
{
  dEq := IdEqDec
}.

(** The type of states *)

Parameter W : Type.


(** State initialisation *)

Parameter BInit : W.

(** W is the state type indeed, as it is an instance of the model state class *)

Instance WP : PState W :=
{ 
  b_init := BInit
}.              
  
End ModTyp.

