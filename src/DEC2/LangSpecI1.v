(*  DEC 2.0 language specification.
   Paolo Torrini 
   Universite' Lille-1 - CRIStAL-CNRS
*)

Require Import List.

Require Import ModTypI1. 
Require Import TypSpecI1. 

Import ListNotations.


(** * DEC 2.0 language specification *)

(** Syntax definition *)

Module LangSpec (IdT: ModTyp) <: ModTyp.
Export IdT.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.


(** Generic effect record *)

Record XFun (T1 T2: VTyp) : Type := {
    inpT : Type := sVTyp T1 ;
    outT : Type := sVTyp T2 ;                                 
    x_mod : inpT -> W -> prod outT W ;
    x_eval : inpT -> W -> outT :=
      fun input state => fst (x_mod input state) ;        
    x_exec : inpT -> W -> W :=
      fun input state => snd (x_mod input state) ;
    x_name : Id ;
}.                                                     

(** Value expressions *)

(** - The internal type of values, parametrised by Gallina types *)

Inductive ValueI (T: VTyp) : Type := Cst (v: sVTyp T).

(** - The external type of values, hiding Gallina types *)

Definition Value : Type := sigT ValueI.

(** - Smart value constructor *)

Definition cst (T: VTyp) (v: sVTyp T) : Value :=
           @existT VTyp ValueI T (Cst T v).

(** - Extractors *)

(* Definition ValueI2T (T: VTyp) (v: ValueI T) : sVTyp T := *)
Definition sValueI (t: VTyp) (v: ValueI t) : sVTyp t :=
    match v with Cst _ x => x end.             

(* Definition cstExt (v: Value) : cVTyp (projT1 v) := *)
Definition sValue (v: Value) : sVTyp (projT1 v) :=
    sValueI (projT1 v) (projT2 v).

Definition valueVTyp (v: Value) : VTyp := projT1 v.

Definition valueSTyp (v: Value) : Type :=  sVTyp (projT1 v).

Definition valueCTyp (v: Value) : CTyp :=  cVTyp (projT1 v).


(***********************************************************************)

Definition FCall : Type := Id * nat * FTyp.

Definition callName (c: FCall) : Id := fst (fst c).

Definition callFuel (c: FCall) : nat := snd (fst c).

Definition callFTyp (c: FCall) : FTyp := snd c.
                                       
(*********************************************************************)

(** - Value typing contexts *)

Definition valTC : Type := list (Id * VTyp).


(** - Function typing contexts *)

Definition funTC : Type := list (Id * FTyp).


(** - Value environments *)

Definition valEnv : Type := list (Id * Value).


(** - Local function environment *)

Definition lfEnv : Type := list (Id * Id).


(** - Function call typed environment *)

Definition tfcEnv : Type := list (Id * FCall).


(** - Bounded call environment *)

Definition fcEnv : Type := list (Id * (Id * nat)).


(** Quasi-values *)
(* Inductive QValue : Type := Var (x: Id) | QV (v: Value). *)
  

(*************************************************************************)

(** Program terms *)

(** Syntactic categories defined by mutual induction: 
    functions, quasi-functions, expressions, parameters *)

Inductive Exp : (** - Expressions *)
       Type :=
         | Val (v: Value)
         | Var (x: Id)
         | BindN (e1: Exp) (e2: Exp) 
         | BindS (x: Id) (mt: option VTyp) (e1: Exp) (e2: Exp) 
         | BindMS (venv: valEnv) (e: Exp)
         | IfThenElse (e1: Exp) (e2: Exp) (e3: Exp)       
         | Apply (x: Id) (ps: Prms) (e: Exp)
         | Call (x: Id) (ps: Prms)        
         | Modify (t1 t2: VTyp)
                  (XF: XFun t1 t2) (e: Exp)
with Prms : (** - Parameters *)
   Type := PS (es: list Exp).


Scheme Exp_mut := Induction for Exp Sort Type
with Prms_mut := Induction for Prms Sort Type.


Inductive Fun : (** - Functions *)
  Type := FC (tenv: valTC) (v: Value) (e: Exp).

Definition funVTyp (f: Fun) : VTyp :=
  match f with (FC _ v _) => projT1 v end.

Definition funValTC (f: Fun) : valTC :=
  match f with (FC tenv _ _) => tenv end.

Definition funFTyp (f: Fun) : FTyp :=
  match f with (FC tenv v _) => FT (PT (map snd tenv)) (projT1 v) end.

Definition funTypLS (f: Fun) : list VTyp :=
  match f with (FC tenv _ _) => map snd tenv end.

Definition funArity (f: Fun) : nat :=
  match f with (FC tenv _ _) => length tenv end.

Definition funPTyp (f: Fun) : PTyp :=
  match f with (FC tenv _ _) => PT (map snd tenv) end.


Definition fun0Exp (f: Fun) : Value :=
  match f with (FC _ v _) => v end.

Definition funSExp (f: Fun) : Exp :=
  match f with (FC _ _ e) => e end.


(** Function environments *)

Definition funEnv : Type := Envr Id Fun.


(** Top-level programs *)

Definition Prog : Type := Exp * funEnv.


(** Auxiliary functions *)

(** - Conversion from typing contexts to type lists *)

Definition env2ptyp (m: valTC) : PTyp := PT (map snd m).


(** - Creation of value environments *)

Definition mkVEnv (tenv: valTC) (vs: list Value) : valEnv :=
     interleave (map fst tenv) vs.


(*************************************************************************)

(** Abbreviations *)

Definition NatCst (v: nat) : Value := cst Nat v.

Definition UnitCst (v: unit) : Value := cst Unit v.

Definition BoolCst (v: bool) : Value := cst Bool v.
 
Definition TrueV : Exp := Val (cst Bool true).

Definition FalseV : Exp := Val (cst Bool false).

Definition UnitV : Exp := Val (cst Unit tt).

Definition Skip : Exp := BindN UnitV UnitV.

Definition BindV (x: Id) (mt: option VTyp) (v: Value) : Exp :=
                     BindS x mt (Val v) (Var x).

Definition Return (x: Id) (mt: option VTyp) (e: Exp) : Exp :=
                     BindS x mt e (Var x).

Definition NoRet (e: Exp) : Exp := BindN e Skip. 



Definition PStateV := VT (PState W) (CPtr (CInt I8 Unsigned)).


Definition xf_read {t: VTyp} (f: W -> sVTyp t) (x: Id) : XFun Unit t := {|
   x_mod := fun _ x => (f x, x); x_name := x     
|}.                                                     

Definition xf_write {t: VTyp} (f: sVTyp t -> W) (x: Id) : XFun t Unit := {|
   x_mod := fun x _ => (sValue (cst Unit tt), f x); x_name := x     
|}.                                                     

Definition xf_reset (x: Id) : XFun PStateV Unit := {|
   x_mod := fun _ x => (sValue (cst Unit tt), b_init); x_name := x     
|}.                                                     

Definition Read (t: VTyp) (f: W -> sVTyp t) (x: Id) : Exp :=
  Modify Unit t (xf_read f x) (Val (cst Unit tt)).

Definition Write (t: VTyp) (f: sVTyp t -> W) (e: Exp) (x: Id) : Exp :=
  Modify t Unit (xf_write f x) e.

Definition Reset (x: Id) : Exp :=
  Modify PStateV Unit (xf_reset x) (Val (cst PStateV WP)).


End LangSpec.

