Require Export Basics.

Require Export EnvLibA.
Require Export RelLibA.
Require Export PRelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Import StaticSemA.
Require Import DynamicSemA.
Require Import TRInductA.
Require Import WeakenA.
Require Import TSoundnessA.
Require Import IdModTypeA.
Require Import AbbrevA.
Require Import ModNat1A.


Module Test_Nat1 <: IdModType.


Module LM := Abbrev ModNat1.
Export LM.

Definition Id := LM.Id.
Definition IdEqDec := LM.IdEqDec.
Definition IdEq := LM.IdEq.
Definition W := LM.W.
Definition Loc_PI := LM.Loc_PI.
Definition BInit := LM.BInit.
Definition WP := LM.WP.

Open Scope string_scope.
Import ListNotations.


Definition nat_read : XFun unit nat := xf_read id. 

Definition nat_write : XFun nat unit := xf_write id.        

Definition nat_reset : XFun (PState nat) unit := xf_reset.                  

Definition nat_incr : XFun nat unit := {|
   b_mod := fun x y => (x + 1, tt)     
|}.                                                     


Definition ReadN : Exp := Read NatVT id.

Definition WriteN (x: nat) : Exp := Write NatVT id x.

Definition ResetN : Exp := Reset.

Definition Incr (x: nat) : Exp :=
  Modify nat unit NatVT UnitVT nat_incr (QV (cst nat x)).



Lemma expTypingTest1 : expTypingTest (BindN ResetN ReadN) Nat.
  econstructor.
  econstructor.
  econstructor.
  constructor.
  simpl.
  auto.
  simpl.
  apply PState_ValTyp.
  constructor.
  constructor.
  constructor.
  simpl.
  auto.
  simpl.
  apply UnitVT.
Defined.


Definition Test1 (n: nat) := runTest (BindN ResetN ReadN) Nat
  expTypingTest1 n.

Lemma Test1L (n: nat) : Test1 n = cst nat 0.
  auto.
Qed.


(**************************************************)

(* line 1 : if true then 3 else 3) *)

Definition three : Exp := Val (cst nat 3).
Definition line1 : Exp := IfThenElse TrueV three three.
Lemma expTypingline1 : ExpTyping emptyE emptyE emptyE line1 Nat.
Proof.
  repeat constructor.
Defined.  


Definition line1Test (n: nat) := runTest line1 Nat expTypingline1 n.

Lemma Test2 (n: nat) : line1Test n = cst nat 3.
  auto.
Defined.  

Lemma Test3 (n: nat) : exists x:nat, line1Test n = cst nat x.
  eexists.
  compute.
  reflexivity.
Defined.  

Eval compute in (line1Test 0).


(***********************************************)
(* binds1 : ... *)

Definition binds1 : Exp := BindS "x" (Val (cst nat 0)) (Return RR (Var "x")).

Definition expTypingTest (e: Exp) (t: VTyp): Type :=
  ExpTyping emptyE emptyE emptyE e t.

Lemma binds1typing: expTypingTest binds1 Nat.
  econstructor.
  instantiate (1:= Nat).
  constructor.
  constructor.
  reflexivity.
  repeat constructor.
  repeat constructor.
Defined.
  
Definition binds1Test (n: nat) := runTest binds1 Nat binds1typing n.

Lemma binds1Test_proof : binds1Test 0 = cst nat 0.
  auto.
Qed.  
  
(*********************************************************)
(* line 2 : apply add3 to 0*)

Definition zero: Exp := Val (cst nat 0).

Definition xf_add3 : XFun nat nat := {|
   b_mod := fun st x => (st, x+3)
|}.

Definition add3': Exp := Modify nat nat NatVT NatVT xf_add3 (Var "x").
Definition add3: QFun := QF (FC emptyE [("x",Nat)] add3' zero "add3" 0).

Definition line2: Exp := Apply add3 (PS [zero]). 
  
Lemma expTypingline2 : ExpTyping emptyE emptyE emptyE line2 Nat.
Proof.
  repeat econstructor.
Defined.  

Definition line2Test (n: nat) := runTest line2 Nat
  expTypingline2 n.


Lemma line2Test_lemma1 :
  EClosure emptyE emptyE (Conf Exp 0 line2) (Conf Exp 0 three).
  unfold line2, three.
  unfold add3.
  unfold add3'.
  unfold xf_add3.
  unfold cst.
  econstructor.
  econstructor.
  econstructor.
  instantiate (1:= [(existT ValueI nat (Cst nat 0))]).
  auto. 
  reflexivity.
  simpl.
  reflexivity.
  econstructor.
  econstructor.
  reflexivity.
  reflexivity.
  simpl.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  reflexivity.
  reflexivity.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
Defined.  

Lemma line2Test_lemma2 : 
  EClosure emptyE emptyE (Conf Exp 0 line2) (Conf Exp 0 three).
  econstructor.
  econstructor.
  econstructor.
  instantiate (1:= [(existT ValueI nat (Cst nat 0))]).
  auto.
  auto.
  auto.
  repeat econstructor.
Defined.

(*  Watch out!!

Lemma lin2Test_lemma : EClosure emptyE emptyE (Conf Exp 0 (Apply add3 (PS [zero])))
        (Conf Exp 0 (Val (existT ValueI nat (Cst nat 3)))).
  repeat econstructor. 
  instantiate (1:= [(existT ValueI nat (Cst nat 0))]).
  auto.
  auto.
  simpl.
  unfold cst.
  eauto.
  repeat econstructor.
*)


Lemma line2ExpTyping : forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
  (k1: MatchEnvsT FunTyping fenv ftenv), 
  ExpTyping ftenv tenv fenv line2 Nat.
Proof.
  intros.
  econstructor.
  reflexivity.
  assumption.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor. 
  reflexivity. 
  econstructor.
  econstructor.
  econstructor.
  constructor.
  reflexivity.
  constructor.
  constructor.
Defined.
  

(*
Lemma Test2s :
      ExpTyping emptyE emptyE emptyE line2 Nat ->
      FEnvTyping emptyE emptyE ->                   
      EnvTyping emptyE emptyE ->
      forall n: W,
      exists (v: nat) (p: (SoundExpA emptyE emptyE line2 Nat n)), 
        projT1 (sigT_of_sigT2 p) =
        (cst nat v).
Proof.
  intros.
  eexists.
  exists (WellTypedEvalM emptyE emptyE emptyE line2 Nat X X0 emptyE X1 n).
  unfold cst.
  simpl.
  compute.
Require Import EqdepFacts.
  
eapply inj_pair2.

  
  eapply expTypingline2.
  eapply fenvTypingline2.
  eapply envTypingline2.
Qed.

Lemma Test2s :
  forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv),
      ExpTyping ftenv tenv fenv line2 Nat ->
      FEnvTyping fenv ftenv ->
      forall env: valEnv,                      
      EnvTyping env tenv ->
      forall n: W, SoundExpA fenv env line2 Nat n.
Proof.
  intros.
  eapply WellTypedEvalM.
  eapply  
  


Lemma Test2a : line2Test 0 = cst nat 3.
unfold line2Test.

                                       
simpl.
unfold cst.
destruct expTypingline2.

Admitted.

Lemma Test2b : exists n:nat, line2Test 0 = cst nat n.
eexists.
unfold line2Test.
simpl.
unfold cst.
simpl.
Admitted.

Lemma expTypingline2A : forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
  (k1: MatchEnvsT FunTyping fenv ftenv), 
  ExpTyping ftenv tenv fenv line2 Nat.
Proof.
  econstructor.
  reflexivity.
  exact k1.
  econstructor.
  econstructor.
  econstructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
Defined.  


Lemma line2TestA (n: nat) : exists
  (ftenv: funTC) (tenv: valTC) (fenv: funEnv) (env: valEnv)
  (k1: MatchEnvsT FunTyping fenv ftenv)
  (k2: MatchEnvsT ValueTyping env tenv), 
  projT1 (sigT_of_sigT2 
 (WellTypedEvalM ftenv tenv fenv line2 Nat
  (expTypingline2A ftenv tenv fenv k1) k1 env k2 n)) = cst nat 3.
eexists.
eexists.
eexists.
eexists.
eexists.
eexists.
simpl.
destruct expTypingline2A.


destruct expTypingline2.



destruct expTypingline2.
unfold expTypingline2.

  

  
Eval compute in (line2Test 0).



  simpl.

Qed.
*)

(**************************************************)


Definition line3: Exp := BindN line1 line2.
Lemma expTypingline3 : ExpTyping emptyE emptyE emptyE line3 Nat.
Proof.
econstructor.
eapply expTypingline1.
apply expTypingline2.
Defined.


Definition line3Test (n: nat) := runTest line3 Nat
  expTypingline3 n.


(*
Lemma Test3a (n: nat) : line3Test n = cst nat 3.
compute.
  
auto.
Qed.
*)

(******************)

(*
Open Scope string_scope.
Import ListNotations.


Definition xf_add3 : XFun nat nat := {|
   b_mod := fun st x => (st,x+3)
|}.
Definition add3':Exp := Modify nat nat NatV NatV xf_add3 (Var "x").
Definition add3:QFun := QF(FC emptyE [("x",Nat)] add3' zero "add3" 0).
Definition line2:Exp := Apply add3 (PS [zero]). 
*)  


End Test_Nat1.