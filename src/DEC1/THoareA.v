(* Paolo Torrini and Mohamed Sami Cherif, 
   Universite' Lille-1 - CRIStAL-CNRS
*)
(* Hoare logic for DEC1 *)

Require Export EnvLibA.
Require Export RelLibA.
Require Export PRelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Import Coq.Logic.ProofIrrelevance.

Require Import StaticSemA.
Require Import DynamicSemA.
Require Import TRInductA.
Require Import WeakenA.
Require Import TSoundnessA.
Require Import IdModTypeA.
Require Import DetermA.
Require Import AbbrevA.
Require Import HoareA.

Module THoare (IdT: IdModType) <: IdModType.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module HoareI := Hoare IdT.
Export HoareI.

Import ListNotations.


Definition THoareTriple_Eval
           (P : W -> Prop) (Q : Value -> W -> Prop)
           (fenv: funEnv) (env: valEnv)
           (e: Exp) : Prop :=
  forall (ftenv: funTC) (tenv: valTC) 
         (k1: FEnvTyping fenv ftenv)
         (k2: EnvTyping env tenv)
         (t: VTyp)
         (k3: ExpTyping ftenv tenv fenv e t) 
         (s s': W) (v: Value),
    EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v)) ->
    P s -> Q v s'.


Definition THoarePrmsTriple_Eval
           (P : W -> Prop) (Q : list Value -> W -> Prop)
           (fenv: funEnv) (env: valEnv)
           (ps: Prms) : Prop :=
  forall (ftenv: funTC) (tenv: valTC) 
         (k1: FEnvTyping fenv ftenv)
         (k2: EnvTyping env tenv)
         (pt: PTyp)
         (k3: PrmsTyping ftenv tenv fenv ps pt)
         (s s': W) (vs: list Value),
    PrmsClosure fenv env (Conf Prms s ps) (Conf Prms s'
                                               (PS (map Val vs))) ->
    P s -> Q vs s'.

Inductive QFClosure :
     funEnv -> AConfig QFun -> AConfig QFun -> Type :=
  | QFC_Base : forall (fenv: funEnv) (p: AConfig QFun), 
              QFClosure fenv p p 
  | QFC_Step : forall (fenv: funEnv) (p1 p2: AConfig QFun),
           QFStep fenv p1 p2 ->
           QFClosure fenv p1 p2.


Definition THoareFunTripleA_Eval
      (P: W -> Prop) (Q: Value -> W -> Prop)  
      (fenv: funEnv) 
      (qf: QFun) : Prop := 
  forall (ftenv: funTC) 
         (k1: FEnvTyping fenv ftenv)
         (ft: FTyp)
         (k2: QFunTyping ftenv fenv qf ft)
         (s s': W) (f: Fun),
  QFClosure fenv (Conf QFun s qf) (Conf QFun s' (QF f)) -> 
  match f with
    | FC fenv' tenv' e0 e1 x n =>
      forall vs: list Value,
        let env' := mkVEnv tenv' vs in        
        EnvTyping env' tenv' ->   
    match n with
      | 0 =>        
        THoareTriple_Eval P Q fenv' (mkVEnv tenv' vs) e0
      | S n' =>        
        THoareTriple_Eval P Q ((x,FC fenv' tenv' e0 e1 x n')::fenv')
                           (mkVEnv tenv' vs) e1
    end
  end.


Definition THoareFunTriple_Eval
      (P: W -> Prop) (Q: Value -> W -> Prop)  
      (fenv: funEnv) (env: valEnv)
      (qf: QFun) : Prop := 
  forall (ftenv: funTC) 
         (k1: FEnvTyping fenv ftenv)
         (ft: FTyp)
         (k2: QFunTyping ftenv fenv qf ft)
         (s s': W) (f: Fun),
  QFClosure fenv (Conf QFun s qf) (Conf QFun s' (QF f)) -> 
  match f with
    | FC fenv' tenv' e0 e1 x n =>  
    EnvTyping env tenv' ->   
    match n with
      | 0 =>        
        THoareTriple_Eval P Q fenv' env e0
      | S n' =>        
        THoareTriple_Eval P Q ((x,FC fenv' tenv' e0 e1 x n')::fenv')
                           env e1
    end
  end.

(***********************************************************************)


Definition IHoareTriple_Eval
           (P : W -> Prop) (Q : Value -> W -> Prop)
           (e: Exp) : Prop :=
  forall (ftenv: funTC) (tenv: valTC) 
         (fenv: funEnv) (env: valEnv)
         (k1: FEnvTyping fenv ftenv)
         (k2: EnvTyping env tenv)
         (t: VTyp) 
         (k3: ExpTyping ftenv tenv fenv e t)
         (s: W), 
  P s -> Q (extractRunValue ftenv tenv fenv e t k3 k1 env k2 s)
           (extractRunState ftenv tenv fenv e t k3 k1 env k2 s).


Definition IHoarePrmsTriple_Eval
           (P : W -> Prop) (Q : list Value -> W -> Prop)
           (ps: Prms) : Prop :=
  forall (ftenv: funTC) (tenv: valTC) 
         (fenv: funEnv) (env: valEnv)
         (k1: FEnvTyping fenv ftenv)
         (k2: EnvTyping env tenv)
         (pt: PTyp)
         (k3: PrmsTyping ftenv tenv fenv ps pt)
         (s: W), 
  P s -> Q (extractPRunValue ftenv tenv fenv ps pt k3 k1 env k2 s)
           (extractPRunState ftenv tenv fenv ps pt k3 k1 env k2 s).


(*************************************************************************)


Lemma BindN_VHTT1 (P0 P1: W -> Prop) (P2: Value -> W -> Prop)
      (fenv: funEnv) (env: valEnv)
      (e1 e2: Exp) :
  THoareTriple_Eval P0 (fun _ => P1) fenv env e1 ->
  THoareTriple_Eval P1 P2 fenv env e2 ->
  THoareTriple_Eval P0 P2 fenv env (BindN e1 e2) .
  unfold THoareTriple_Eval.
  intros.
  eapply BindN_BStepT1 in X.
  destruct X as [s1 X].
  destruct X as [v1 X].
  inversion k3; subst.
  eapply (H0 ftenv tenv).
  auto.
  auto.
  eauto.
  eauto.
  eapply (H ftenv tenv).
  auto. 
  auto.
  eauto.
  eauto.
  auto.
  eauto.
  eauto.
  eauto.
Qed.



Lemma BindN_VHTT2 (P0: W -> Prop) (P1 P2: Value -> W -> Prop)
      (fenv: funEnv) (env: valEnv)
      (e1 e2: Exp) :
  THoareTriple_Eval P0 P1 fenv env e1 ->
  (forall v: Value, THoareTriple_Eval (P1 v) P2 fenv env e2) ->
  THoareTriple_Eval P0 P2 fenv env (BindN e1 e2) .
  unfold THoareTriple_Eval.
  intros.
  eapply BindN_BStepT1 in X.
  destruct X as [s1 X].
  destruct X as [v1 X].
  inversion k3; subst.
  eapply (H0 v1 ftenv tenv).
  auto.
  auto.
  eauto.
  eauto.
  eapply (H ftenv tenv).
  auto. 
  auto.
  eauto.
  eauto.
  auto.
  eauto.
  eauto.
  eauto.
Qed.

 
Lemma BindS_VHTT1 (P0: W -> Prop) (P1 P2: Value -> W -> Prop)
        (fenv: funEnv) (env: valEnv)     
        (e1 e2: Exp) (x: Id) :
  THoareTriple_Eval P0 P1 fenv env e1 ->
  (forall v, THoareTriple_Eval (P1 v) P2 fenv ((x,v)::env) e2) ->
  THoareTriple_Eval P0 P2 fenv env (BindS x e1 e2).
Proof.
  unfold THoareTriple_Eval.
  intros.
  eapply BindS_BStepT1 in X.
  destruct X as [s1 X].
  destruct X as [v1 X].
  inversion k3; subst.
  eapply (H0 v1 ftenv tenv').
  auto.
  econstructor.
  assert (v1 = extractRunValue ftenv tenv fenv e1 t1 X0 k1 env k2 s).
  eapply (proj2 (EvalElim ftenv tenv fenv e1 t1 X0 k1 env k2 s s1 v1 X)).
  rewrite H2.
  exact (extractRunTyping ftenv tenv fenv e1 t1 X0 k1 env k2 s).
  auto.
  eauto.
  eauto.
  eapply (H ftenv tenv).
  auto.
  auto.
  eauto.
  eauto.
  auto.
  eauto.
  eauto.
  eauto.
Qed.  
  
  
Lemma Apply_VHTT1 (P0: W -> Prop) (P1: list Value -> W -> Prop)
                 (P2: Value -> W -> Prop)  
   (fenv: funEnv) (env: valEnv) (f: Fun) (es: list Exp) : 
  THoarePrmsTriple_Eval P0 P1 fenv env (PS es) ->
  match f with
  | FC fenv' tenv' e0 e1 x n => 
    length tenv' = length es /\     
    match n with
    | 0 => (forall vs: list Value,  
          THoareTriple_Eval (P1 vs) P2 fenv' (mkVEnv tenv' vs) e0)
    | S n' => (forall vs: list Value,
          THoareTriple_Eval (P1 vs) P2 ((x,FC fenv' tenv' e0 e1 x n')::fenv')
                           (mkVEnv tenv' vs) e1)
    end
  end ->             
  THoareTriple_Eval P0 P2 fenv env (Apply (QF f) (PS es)).
Proof.
  unfold THoareTriple_Eval, THoarePrmsTriple_Eval.
  intros.
  generalize (Apply_BStepT1 ftenv tenv fenv env f es v s s' k1 k2 t k3).
  intro P.
  destruct f.
  destruct H0.
  specialize (P H0 X).
  destruct P as [s1 P].
  destruct P as [vs P].
  inversion k3; subst.
  inversion X1; subst.
  specialize (H ftenv tenv k1 k2 (PT (map snd fps)) X2 s s1 vs P H1).

  assert (tenv0 = fps).
  inversion X3; subst.
  auto.
  auto.
  inversion H3; subst.
  clear H4.

  assert (length es = length (map Val vs)) as W.
  eapply PrmsClos_aux0.
  eauto.
  rewrite map_length with (f:=Val) in W. 
  
  assert (EnvTyping (mkVEnv fps vs) fps) as Q.
  eapply mkEnvTyping_aux0.
  rewrite <- W.
  auto.

  eapply prmsTyping_aux4.
  eauto.
  eauto.
  eauto.
  eauto.
  
  destruct n.

  inversion X3; subst.  
  eapply H2.
  eauto.
  eauto.
  eauto.
  eauto.
  auto.

  inversion X3; subst.
  eapply H2.
  eauto.
  instantiate (1:= (x, FT fps t) :: ftenv0).
  econstructor.
  auto.
  auto.
  eauto.
  eauto.
  auto.
  eauto.
  auto.
Qed.



Lemma Apply_VHTT2 (P0: W -> Prop) (P1: list Value -> W -> Prop)
                 (P2: Value -> W -> Prop)
                 (fenv: funEnv) (env: valEnv) (f: Fun) (es: list Exp) :
   THoarePrmsTriple_Eval P0 P1 fenv env (PS es) ->
   (forall vs,  
       THoareTriple_Eval (P1 vs) P2 fenv env
                                 (Apply (QF f) (PS (map Val vs)))) ->
   THoareTriple_Eval P0 P2 fenv env (Apply (QF f) (PS es)).
Proof.
  unfold THoareTriple_Eval, THoarePrmsTriple_Eval.
  intros.
  
  inversion k3; subst.
  generalize (Apply_BStepT2t ftenv tenv fenv env f es v s s' k1 k2 t
                             (PT (map snd fps)) k3 X2).
  intro P.

  specialize (P X).
  destruct P as [s1 P].
  destruct P as [vs P].
  inversion k3; subst.
  destruct P as [Q1 Q2].

  specialize (H ftenv tenv k1 k2 (PT (map snd fps)) X2 s s1 vs Q2 H1).
  assert (ExpTyping ftenv tenv fenv (Apply (QF f) (PS (map Val vs))) t).
  econstructor.
  reflexivity.
  auto.
  eauto.

  assert (FT fps t = FT fps0 t). 
  eapply QFunStrongTyping.
  eauto.
  auto.
  eauto.
  auto.
  inversion H2; subst.
  auto.
  
  eapply H0.
  eauto.
  eauto.
  eauto.
  eauto.
  auto.
Qed.



Lemma QFun_VHTT (P1: W -> Prop) (P2: Value -> W -> Prop)
      (fenv: funEnv) (env: valEnv) (x: Id) (f: Fun) (es: list Exp) :  
  findET fenv x f ->
  THoareTriple_Eval P1 P2 fenv env (Apply (QF f) (PS es))  ->
  THoareTriple_Eval P1 P2 fenv env (Apply (FVar x) (PS es)).
Proof.  
  unfold THoareTriple_Eval.
  intros.
  assert (sigT2 (findET ftenv x) (fun t: FTyp => FunTyping f t)).
  {- eapply ExRelValT1.
     eassumption.
     assumption.
  }  
  destruct X1 as [ft Z1 Z2].
  inversion k3; subst.  
  inversion X2; subst.

  eapply MatchEnvs2BT_find1 in X4.
  destruct X4 as [Z3 Z4].

  destruct ft.
  inversion Z1; subst.
  inversion Z4; subst.
  rewrite H1 in H2.
  inversion H2; subst.
  
  eapply H.
  - exact k1.
  - exact k2.
  - instantiate (1:=t).
    econstructor.
    + reflexivity.
    + assumption.
    + instantiate (1:=fps).
      econstructor.
      auto.
    + auto.

  - clear H2.
    instantiate (1:=s).
    inversion X0; subst.
    inversion X4; subst.
    inversion X6; subst.
    inversion X7; subst.
    inversion X; subst. 
    rewrite H2 in H3.
    inversion H3; subst.
    auto.
  - auto.
Qed.  


Lemma Apply_VHTT3 (P0: W -> Prop) (P1: list Value -> W -> Prop)
                 (P2: Value -> W -> Prop)
                 (fenv: funEnv) (env: valEnv) (x: Id) (f: Fun)
                 (es: list Exp) :
   THoarePrmsTriple_Eval P0 P1 fenv env (PS es) ->
   findET fenv x f->
   (forall vs ,
       THoareTriple_Eval (P1 vs) P2 fenv env
                         (Apply (QF f) (PS (map Val vs))))  -> 
   THoareTriple_Eval P0 P2 fenv env (Apply (FVar x) (PS es)).
Proof.
   intros.  
   eapply QFun_VHTT.
   eauto.
   eapply Apply_VHTT2.
   eauto.
   auto.
Qed.



Lemma Prms_VHTT1 (P0: W -> Prop) (P1: Value -> W -> Prop)
                  (P2: list Value -> W -> Prop) 
        (fenv: funEnv) (env: valEnv)     
        (e: Exp) (es: list Exp) :
  THoareTriple_Eval P0 P1 fenv env e ->
  (forall v: Value,
     THoarePrmsTriple_Eval (P1 v) (fun vs => P2 (v::vs)) fenv env (PS es)) ->
  THoarePrmsTriple_Eval P0 P2 fenv env (PS (e::es)).
Proof.
  unfold THoareTriple_Eval, THoarePrmsTriple_Eval.
  intros.
  inversion k3; subst.
  inversion X0; subst.
  rename y into t.
  rename l' into ts.
  
  destruct vs.
  eapply PrmsClos_aux0 in X.
  simpl in X.
  intuition.

  eapply Prms_BStepT2 in X.
  destruct X as [s1 X].
  specialize (H ftenv tenv k1 k2 t X1 s s1 v X H1).
  assert (PrmsTyping ftenv tenv fenv (PS es) (PT ts)).
  constructor.
  auto.
  specialize (H0 v ftenv tenv k1 k2 (PT ts) X3 s1 s' vs p H).
  auto.
  eauto.
  eauto.
  eauto.
Qed.  
  

Lemma IfThenElse_VHTT1 (P0: W -> Prop) (P1 P2: Value -> W -> Prop) 
        (fenv: funEnv) (env: valEnv)     
        (e1 e2 e3: Exp) :
  THoareTriple_Eval P0 P1 fenv env e1 ->
  THoareTriple_Eval (P1 (cst bool true)) P2 fenv env e2 ->
  THoareTriple_Eval (P1 (cst bool false)) P2 fenv env e3 ->
  THoareTriple_Eval P0 P2 fenv env (IfThenElse e1 e2 e3).
Proof.
  unfold THoareTriple_Eval.
  intros.
  generalize (IfThenElse_BStepT1
                ftenv tenv fenv env e1 e2 e3 v s s' k1 k2 t k3 X).
  intro.
  inversion k3; subst.
  specialize (H ftenv tenv k1 k2 Bool X1 s).
  specialize (H0 ftenv tenv k1 k2 t X2).
  specialize (H1 ftenv tenv k1 k2 t X3).
  destruct X0.

  destruct s0 as [s1 X0 X4].
  eapply H0.
  exact X4.
  eapply H.
  exact X0.
  exact H2.

  destruct s0 as [s1 X0 X4].
  eapply H1.
  exact X4.
  eapply H.
  exact X0.
  exact H2.
Qed.  


Lemma Modify_VHTT1 (P: Value -> W -> Prop) 
        (fenv: funEnv) (env: valEnv)     
        (T1 T2: Type) (VT1: ValTyp T1) (VT2: ValTyp T2)
        (XF: XFun T1 T2) (v: T1) :
  THoareTriple_Eval (fun s => P (cst T2 (b_eval T1 T2 XF s v))
                                ((b_exec T1 T2 XF s v)))
            P fenv env (Modify T1 T2 VT1 VT2 XF (QV (cst T1 v))).
  unfold THoareTriple_Eval.
  intros.
  inversion k3; subst.
  eapply inj_pair2 in H6; subst.
  eapply inj_pair2 in H6; subst.

  assert (EStep fenv env (Conf Exp s (Modify T1 T2 VT1 VT2 XF (QV (cst T1 v))))
    (Conf Exp (b_exec T1 T2 XF s v) (Val (cst T2 (b_eval T1 T2 XF s v))))).
  constructor.
  eapply StepIsEClos in X1.
  assert (s' = (b_exec T1 T2 XF s v) /\ v0 = (cst T2 (b_eval T1 T2 XF s v))).
  eapply ExpConfluence.
  exact k3.
  auto.
  eauto.
  eassumption.
  assumption.
  destruct H0.
  rewrite H0.
  rewrite H1.
  assumption.
Qed.  


(****** Hoare logic notation ***************************************)


Notation "{{ P }} fenv >> env >> e {{ Q }}" :=
  (THoareTriple_Eval P Q fenv env e ) (at level 90) : state_scope.

Notation "{{ P }}' fenv >> env >> ps {{ Q }}'" :=
  (THoarePrmsTriple_Eval P Q fenv env ps ) (at level 90) : state_scope.

Open Scope state_scope.



Definition wp (P : Value -> W -> Prop)
           (fenv: funEnv) (env: valEnv) (e : Exp) :
      W -> Prop := fun s => forall (v:Value) (s': W),
EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v)) -> P v s'.

Lemma wpIsPrecondition (P : Value -> W -> Prop)
      (fenv: funEnv) (env: valEnv) (e : Exp) :
  {{ wp P fenv env e }} fenv >> env >> e {{ P }}.
Proof.
unfold THoareTriple_Eval.
intros ftenv tenv k1 k2 t k3 s s' v H1 H2.
unfold wp in H2.
eapply H2.
auto.
Qed.

Lemma weakenEval (P Q : W -> Prop) (R : Value -> W -> Prop)
                  (fenv: funEnv) (env: valEnv) (e : Exp) :
  {{ Q }} fenv >> env >> e {{ R }} -> (forall s, P s -> Q s) ->
  {{ P }} fenv >> env >> e {{ R }}.
Proof.
intros.
unfold THoareTriple_Eval in *.
intros.
eapply H;
eauto.
Qed.

Definition wpPrms (P : list Value -> W -> Prop)
                   (fenv: funEnv) (env: valEnv) (ps: Prms):
  W -> Prop := fun s => forall (vs: list Value) (s': W),
  PrmsClosure fenv env (Conf Prms s ps) (Conf Prms s' (PS (map Val vs))) ->
                   P vs s'.

Lemma wpIsPreconditionPrms (P : list Value -> W -> Prop)
                             (fenv: funEnv) (env: valEnv) (ps: Prms):
  THoarePrmsTriple_Eval (wpPrms P fenv env ps) P fenv env ps.
Proof.
unfold THoarePrmsTriple_Eval.
intros ftenv tenv k1 k2 t k3 s s' v H1 H2.
unfold wpPrms in H2.
eapply H2.
auto.
Qed.

Lemma weakenPrms (P Q : W -> Prop) (R : list Value -> W -> Prop)
                  (fenv: funEnv) (env: valEnv) (ps: Prms):
  THoarePrmsTriple_Eval Q R fenv env ps ->
 (forall s, P s -> Q s) -> THoarePrmsTriple_Eval P R fenv env ps .
Proof.
intros.
unfold THoarePrmsTriple_Eval in *.
intros.
eapply H;
eauto.
Qed.


(**********************************************************************)


Lemma BindN_HoareRule (P0 P1: W -> Prop) (P2: Value -> W -> Prop)
        (fenv: funEnv) (env: valEnv)     
        (e1 e2: Exp) :
  {{ P0 }} fenv >> env >> e1 {{ fun _ => P1 }} -> 
  {{ P1 }} fenv >> env >> e2 {{ P2 }} ->
  {{ P0 }} fenv >> env >> (BindN e1 e2) {{ P2 }}.
Proof.
  eapply BindN_VHTT1.
Qed.


Lemma BindS_HoareRule (P0: W -> Prop) (P1 P2: Value -> W -> Prop)
        (fenv: funEnv) (env: valEnv)     
        (e1 e2: Exp) (x: Id) :
  {{ P0 }} fenv >> env >> e1 {{ P1 }} -> 
  (forall v, {{ P1 v }} fenv >> ((x,v)::env) >> e2 {{ P2 }}) ->
  {{ P0 }} fenv >> env >> (BindS x e1 e2) {{ P2 }}.
Proof.
  eapply BindS_VHTT1.
Qed.


Lemma Apply0_HoareRule (P0: W -> Prop) (P1: list Value -> W -> Prop)
                 (P2: Value -> W -> Prop)  
                 (fenv fenv': funEnv) (env: valEnv) (tenv: valTC) (e0 e1: Exp)
                 (es: list Exp) (x: Id) :
  length tenv = length es ->
  {{ P0 }}' fenv >> env >> PS es {{ P1 }}' ->
  (forall vs, {{ P1 vs }} fenv' >> (mkVEnv tenv vs) >> e0 {{ P2 }}) ->
  {{ P0 }} fenv >> env >>
           (Apply (QF (FC fenv' tenv e0 e1 x 0)) (PS es)) {{ P2 }}.
Proof.
  generalize (Apply_VHTT1 P0 P1 P2 fenv env (FC fenv' tenv e0 e1 x 0) es).
  intros.
  eapply H.
  auto.
  auto.
Qed.  


Lemma Apply1_HoareRule (P0: W -> Prop) (P1: list Value -> W -> Prop)
                 (P2: Value -> W -> Prop)  
                 (fenv fenv': funEnv) (env: valEnv) (tenv: valTC) (e0 e1: Exp)
                 (es: list Exp) (x: Id) (n: nat) :
  length tenv = length es ->
  {{ P0 }}' fenv >> env >> PS es {{ P1 }}' ->
  (forall vs, {{ P1 vs }} (x, FC fenv' tenv e0 e1 x n)::fenv' >>
                          (mkVEnv tenv vs) >> e1 {{ P2 }}) ->
  {{ P0 }} fenv >> env >>
           (Apply (QF (FC fenv' tenv e0 e1 x (S n))) (PS es)) {{ P2 }}.
Proof.
  generalize (Apply_VHTT1 P0 P1 P2 fenv env (FC fenv' tenv e0 e1 x (S n)) es).
  intros.
  eapply H.
  auto.
  auto.
Qed.  


Lemma Modify_HoareRule (P: Value -> W -> Prop) 
        (fenv: funEnv) (env: valEnv)     
        (T1 T2: Type) (VT1: ValTyp T1) (VT2: ValTyp T2)
        (XF: XFun T1 T2) (v: T1) :
 {{ fun s => P (cst T2 (b_eval T1 T2 XF s v))
               ((b_exec T1 T2 XF s v)) }} fenv >> env >>
        (Modify T1 T2 VT1 VT2 XF (QV (cst T1 v))) {{ P }}.
Proof.
  eapply Modify_VHTT1.
Qed.



(***********************************************************************)

Ltac HoareTac :=
  match goal with
  | [ |- THoareTriple_Eval ?P0 ?P1 ?fenv ?env ?e ] =>                
    match e with
    | BindN ?e1 ?e2 => eapply (BindN_VHTT2 P0 _ P1 fenv env e1 e2)
    | BindS ?x ?e1 ?e2 => eapply (BindS_VHTT1 P0 _ P1 fenv env e1 e2 x)
    | Apply (FVar ?x) (PS ?es) =>
      match constr:(findE fenv x) with
      | Some ?f => eapply (Apply_VHTT3 P0 _ P1 fenv env x f es)
      | None => fail                   
      end
    | Apply (QF ?f) (PS ?es) =>
        eapply (Apply_VHTT1 P0 _ P1 fenv env f es)
    | IfThenElse ?e1 ?e2 ?e3 =>
        eapply (IfThenElse_VHTT1 P0 _ P1 fenv env e1 e2 e3)
    | _ => fail
    end  
  | [ |- THoarePrmsTriple_Eval ?P0 ?P1 ?fenv ?env ?ps ] =>
    match ps with
    | PS (?e :: ?es) =>   
      eapply (Prms_VHTT1 P0 _ P1 fenv env e es)
    end         
  end. 


End THoare.

