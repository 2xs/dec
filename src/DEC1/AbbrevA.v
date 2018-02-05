Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Require Import Omega.
Require Import Coq.Lists.List.

Require Export EnvLibA.
Require Export RelLibA.
Require Export PRelLibA.

Require Import StaticSemA.
Require Import DynamicSemA.
Require Import TRInductA.
Require Import WeakenA.
Require Import TSoundnessA.
Require Import IdModTypeA.
Require Import DetermA.
Require Import STypingA.

Module Abbrev (IdT: IdModType) <: IdModType.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module STypingI := STyping IdT.
Export STypingI.

Open Scope string_scope.
Import ListNotations.


(** special value constructors *)

Definition NatCst (v: nat) : Value := cst nat v.

Definition UnitCst (v: unit) : Value := cst unit v.

Definition BoolCst (v: bool) : Value := cst bool v.
 
Definition TrueV : Exp := Val (cst bool true).

Definition FalseV : Exp := Val (cst bool false).

Definition UnitV : Exp := Val (cst unit tt).

Definition VLift := Return LL.

Definition Skip : Exp := VLift (QV (cst unit tt)).

Definition NoRet (e: Exp) : Exp := BindN e Skip. 


(**************************************************************************)

Instance PState_ValTyp : ValTyp (PState W).


Definition xf_read {T: Type} (f: W -> T) : XFun unit T := {|
   b_mod := fun x _ => (x, f x)     
|}.                                                     

Definition xf_write {T: Type} (f: T -> W) : XFun T unit := {|
   b_mod := fun _ x => (f x, tt)     
|}.                                                     

Definition xf_reset : XFun (PState W) unit := {|
   b_mod := fun x _ => (b_init, tt)     
|}.                                                     


Definition Read {T: Type} (VT: ValTyp T) (f: W -> T) : Exp :=
  Modify unit T UnitVT VT (xf_read f) (QV (cst unit tt)).

Definition Write {T: Type} (VT: ValTyp T) (f: T -> W) (x: T) : Exp :=
  Modify T unit VT UnitVT (xf_write f) (QV (cst T x)).

Definition Reset : Exp :=
  Modify (PState W) unit PState_ValTyp UnitVT xf_reset
         (QV (cst (PState W) WP)).

(*
Definition ReadA (VT: ValTyp Value) (f: W -> Value) : Exp :=
  Modify unit Value UnitVT VT (xf_read f) (QV (cst unit tt)).

Definition WriteA (VT: ValTyp Value) (f: Value -> W) (v: Value) : Exp :=
  Modify Value unit VT UnitVT (xf_write f) (QV (cst Value x)).

Definition CReturn (VT: ValTyp Value)
           (toStack: Value -> W) (fromStack: W -> Value) (e: Exp) : Exp :=
  BindN (NoRet (BindS x e (WriteA toStack x))) (Read fromStack).  
*)

(**********************************************************************)

Lemma emptyFTyping : FEnvTyping emptyE emptyE.
  constructor.
Defined.

Lemma emptyVTyping : EnvTyping emptyE emptyE.
  constructor.
Defined.


Definition expTypingTest (e: Exp) (t: VTyp): Type :=
  ExpTyping emptyE emptyE emptyE e t.

Definition runTest (e: Exp) (t: VTyp)
 (k: expTypingTest e t) (s: W) :=  projT1 (sigT_of_sigT2 
 (ExpEval emptyE emptyE emptyE e t k emptyFTyping emptyE emptyVTyping s)).


End Abbrev.