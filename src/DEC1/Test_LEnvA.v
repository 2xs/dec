Require Export Basics.

Require Export EnvLibA.
Require Export RelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Import Coq.Logic.ProofIrrelevance.

Require Import IdModTypeA.
Require Import StaticSemA.
Require Import DynamicSemA.
Require Import TRInductA.
Require Import WeakenA.
Require Import TSoundnessA.
Require Import AbbrevA.
Require Import ModLEnvA.


Module Test_LEnv <: IdModType.
  
Module TS := Abbrev ModLEnv.
Export TS.

Definition Id := TS.Id.
Definition IdEqDec := TS.IdEqDec.
Definition IdEq := TS.IdEq.
Definition W := TS.W.
Definition Loc_PI := TS.Loc_PI.
Definition BInit := TS.BInit.
Definition WP := TS.WP.

Open Scope string_scope.
Import ListNotations.


(**************************************************)

Fixpoint findD {K V: Type} {h: DEq K} (m: list (K * V)) (d: V) (k: K) : V :=
  match m with
     | nil => d
     | cons (k', x) ls => match (dEq k k') with
                            | left _ => x
                            | right _ => findD ls d k
                            end               
    end.

Fixpoint update1 {K V: Type} {h: DEq K} (m: list (K * V)) (k: K) (v: V) :
  list (K * V) :=
  match m with
     | nil => [(k,v)]
     | cons (k', x) ls => match (dEq k k') with
                            | left _ => (k',v):: ls
                            | right _ => (k',x) :: update1 ls k v
                            end               
    end.

Fixpoint update0 {K V: Type} {h: DEq K} (m: list (K * V)) (k: K) (v: V) :
  list (K * V) :=
  match m with
     | nil => nil
     | cons (k', x) ls => match (dEq k k') with
                            | left _ => (k',v):: ls
                            | right _ => (k',x) :: update1 ls k v
                            end               
    end.


Fixpoint increase1 {K: Type} {h: DEq K} (m: list (K * nat)) (k: K) (v: nat) :
  list (K * nat) :=
  match m with
     | nil => nil
     | cons (k', x) ls => match (dEq k k') with
                            | left _ => (k',v):: ls
                            | right _ => (k',x+v) :: update1 ls k v
                            end               
    end.


Definition lenv_read : XFun Id nat := {|
   b_mod := fun s x => (s, findD s 0 x)     
|}.                                                     

Definition lenv_write : XFun (Id * nat) unit := {|
   b_mod := fun s x => (update1 s (fst x) (snd x), tt)     
|}.                                                     

Definition lenv_reset : XFun (PState W) unit := {|
   b_mod := fun x _ => (b_init, tt)     
|}.                                                     

Definition lenv_incr : XFun (Id * nat) unit := {|
   b_mod := fun s x => (increase1 s (fst x) (snd x), tt)     
|}.                                                     



Instance VT_Id : ValTyp Id.

Instance VT_IdNat : ValTyp (Id * nat).


Definition ReadL (x: Id) : Exp :=
  Modify Id nat VT_Id NatVT lenv_read (QV (cst Id x)).

Definition WriteL (x: Id) (v: nat) : Exp :=
  Modify (Id * nat) unit VT_IdNat UnitVT lenv_write (QV (cst (Id * nat) (x,v))).

Definition ResetL : Exp :=
  Modify (PState W) unit PState_ValTyp UnitVT xf_reset
         (QV (cst (PState W) WP)).

Definition Incr (x: Id) (v: nat) : Exp :=
  Modify (Id * nat) unit VT_IdNat UnitVT lenv_incr
         (QV (cst (Id * nat) (x, v))).



Lemma read_nat_1 (P0: Value -> Prop) 
           (fenv: funEnv) (env: valEnv):  
  forall (s s': W) (v: Value) (x: Id),
    EClosure fenv env (Conf Exp s (ReadL x))
             (Conf Exp s' (Val v)) ->
    P0 (cst nat (findD s 0 x)) -> P0 v.
  intros.
  inversion X; subst.
  inversion X0; subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6.
  subst.
  clear H7.
  eapply inj_pair2 in H8.
  subst.
  clear XF1.
  inversion X1; subst.
  unfold xf_read in *.
  unfold b_exec, b_eval in *.
  simpl in *.
  auto.
  inversion X2.
  inversion X2.
Qed.  
  

Lemma expTypingTest1 : ExpTyping emptyE emptyE emptyE
                                 (BindN ResetL (ReadL "x")) Nat.
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
  apply VT_Id.
Defined.


Definition Test1 (n: W) :=  runTest (BindN ResetL (ReadL "x")) Nat
  expTypingTest1 n. 

Lemma Test1L (n: W) : Test1 n = cst nat 0.
  auto.
Qed.


(**************************************************)

(* line 1 : if true then 3 else 3) *)


Definition three : Exp := Val(cst nat 3).
Definition line1 : Exp := IfThenElse TrueV three three.
Lemma expTypingline1 : ExpTyping emptyE emptyE emptyE line1 Nat.
Proof.
  repeat constructor.
Defined.  


Definition line1Test (n: W) := runTest line1 Nat expTypingline1 n.

Lemma Test2 (n: W) : line1Test n = cst nat 3.
  auto.
Defined.  

Lemma Test3 (n: W) : exists x:nat, line1Test n = cst nat x.
  eexists.
  compute.
  reflexivity.
Defined.  

Eval compute in (line1Test nil).


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
  
Definition binds1Test (n: W) := runTest binds1 Nat binds1typing n.


Lemma binds1Test_proof : binds1Test nil = cst nat 0.
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


Definition line2Test (n: W) := runTest line2 Nat
  expTypingline2 n.



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


Definition line3Test (n: W) := runTest line3 Nat
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


End Test_LEnv.