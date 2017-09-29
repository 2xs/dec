(* DEC 1.0 language specification.
   Paolo Torrini and David Nowak, 
   Universite' Lille-1 - CRIStAL-CNRS
*)

Require Import DEC.AuxLib.

(** * DEC 1.0 module type *)

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

(** Local proof irrelevance assumption *)

Parameter Loc_PI : forall (T: Type) (p1 p2: ValTyp T), p1 = p2.

(** State initialisation *)

Parameter BInit : W.

(** W is the state type indeed, as it is an instance of the model state class *)

Instance WP : PState W :=
{
  loc_pi := Loc_PI;
  
  b_init := BInit
}.              
  
End ModTyp.

