(* DEC 2.0 language specification.
   Paolo Torrini, 
   Universite' de Lille - CRIStAL-CNRS
*)

Require Import List.

Require Export AuxLibI1.
        
Import ListNotations.

Open Scope type_scope.

(** Types *)

(** - The type of C value types *)

Inductive signedness : Type :=
  | Signed: signedness
  | Unsigned: signedness.

Inductive intsize : Type :=
  | I8: intsize
  | I16: intsize
  | I32: intsize      
  | IBool: intsize.

Inductive CTyp (t: Type) : Type :=
                     | CVoid
                     | CBool : (t = bool) -> intsize -> signedness -> CTyp t  
                     | CInt : (t = nat) -> intsize -> signedness -> CTyp t
                     | CPtr : (t = nat) -> CTyp t -> CTyp t.     


(** - The type of value types *)

Inductive VTyp : Type := VT (st: Type) (ct: CTyp st).


(** - Extractors *)

Definition sVTyp (t: VTyp) : Type := match t with
                                     | VT st _ => st
                                     end.               

(** DEC state class *)  

Class PState (W: Type) : Type := {

   b_init : W ;
}.

(***********************************************************************)

(** - Value type abbreviations *)

Definition Unit : VTyp := VT (unit:Type) (CVoid unit).

Definition Nat : VTyp := VT (nat:Type) (CInt nat eq_refl I32 Unsigned).

Definition Bool : VTyp := VT (bool:Type) (CBool bool eq_refl IBool Unsigned).

(*************************************************************************)

(** - Parameter types *)

Inductive PTyp : Type := PT (ts: list VTyp).

(** - Function types *)

Inductive FTyp : Type := FT (prs_type: PTyp) (ret_type: VTyp).

(** - Extractors for function and parameter types *)

Definition ftypPT (ft: FTyp) : PTyp :=
  match ft with FT ps _ => ps end.

Definition ftypVT (ft: FTyp) : VTyp :=
  match ft with FT _ t => t end.

Definition ptypLS (ps: PTyp) : list VTyp :=
  match ps with PT ts => ts end.

Definition sPTyp (pt: PTyp) : Type :=
  tlist2type (map sVTyp (ptypLS pt)).  

Definition VTypLs2Type (ts: list VTyp) : Type :=
  tlist2type (map sVTyp ts).



