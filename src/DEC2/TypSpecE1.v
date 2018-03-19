(* DEC 2.0 language specification.
   Paolo Torrini, 
   Universite' Lille-1 - CRIStAL-CNRS
*)

Require Import List.

Require Export AuxLib.
        
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
  | I64: intsize         
  | IBool: intsize.

Inductive CTyp : Type :=
                     | CVoid
                     | CInt : intsize -> signedness -> CTyp
                     | CPtr : CTyp -> CTyp.                                   


(** - The type of value types *)

Inductive VTyp : Type := VT (st: Type) (ct: CTyp).

(** - Smart value type constructor *)

(* Definition vtyp (T: Type * CTyp) {VT: ValTyp T} : VTyp :=
    @exist (Type * CTyp) ValTyp T VT.
*)
(** - Extractors *)

Definition sVTyp (t: VTyp) : Type := match t with
                                     | VT st _ => st
                                     end.               
                                                                   
Definition cVTyp (t: VTyp) : CTyp := match t with
                                     | VT _ ct => ct 
                                     end.                              
                                                                 

(** Pip state class *)  

Class PState (W: Type) : Type := {

   b_init : W ;
}.

(***********************************************************************)

(** - Value type abbreviations *)

Definition Unit : VTyp := VT (unit:Type) CVoid.

Definition Nat : VTyp := VT (nat:Type) (CInt I32 Unsigned).

Definition Bool : VTyp := VT (bool:Type) (CInt IBool Unsigned).

(*************************************************************************)

(** - Parameter types *)

Inductive PTyp : Type := PT (ts: list VTyp).

(** - Function types *)

Inductive FTyp : Type := FT (prs_type: PTyp) (ret_type: VTyp).

(** - Extractors for function and parameter types *)
(*
Definition prmsTyp (ft: FTyp) : PTyp :=
  match ft with FT ps _ _ => ps end.

Definition retTyp (ft: FTyp) : VTyp :=
  match ft with FT _ t _ => t end.

Definition tagTyp (ft: FTyp) : Tag :=
  match ft with FT _ _ g => g end.

Definition dstPTyp (ps: PTyp) : list VTyp :=
  match ps with PT ts => ts end.
*)

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


(*************************************************************************)
