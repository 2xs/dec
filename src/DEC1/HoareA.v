Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Require Import Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Logic.ProofIrrelevance.

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
Require Import AbbrevA.
Require Import InvertA.

Module Hoare (IdT: IdModType) <: IdModType.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module InvertI := Invert IdT.
Export InvertI.

Open Scope string_scope.
Import ListNotations.


Definition HoareTriple_Step
           (P : W -> Prop) (Q : Exp -> W -> Prop)
           (fenv: funEnv) (env: valEnv)
           (e: Exp) : Prop :=  
  forall (s s': W) (e': Exp),
    EStep fenv env (Conf Exp s e) (Conf Exp s' e') ->
    P s -> Q e' s'.

Definition HoareTriple_ExtendedStep
           (P : W -> Prop) (Q : Exp -> W -> Prop)
           (fenv: funEnv) (env: valEnv)
           (e: Exp) : Prop :=  
  forall (s s': W) (e': Exp),
    EClosure fenv env (Conf Exp s e) (Conf Exp s' e') ->
    P s -> Q e' s'.

Definition HoareTriple_Eval
           (P : W -> Prop) (Q : Value -> W -> Prop)
           (fenv: funEnv) (env: valEnv)
           (e: Exp) : Prop :=  
  forall (s s': W) (v: Value),
    EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v)) ->
    P s -> Q v s'.

Definition HoarePrmsTriple_Eval
           (P : W -> Prop) (Q : list Value -> W -> Prop)
           (fenv: funEnv) (env: valEnv)
           (es: list Exp) : Prop :=  
  forall (s s': W) (vs: list Value),
    PrmsClosure fenv env (Conf Prms s (PS es)) (Conf Prms s'
                                                     (PS (map Val vs))) ->
    P s -> Q vs s'.

(************************************************************************)

Lemma write_T_1 {T: Type} (VT: ValTyp T) (f: T -> W)
      (P0: W -> Prop) 
      (fenv: funEnv) (env: valEnv) (x: T):  
  forall (s s': W) (e: Exp),
    EStep fenv env (Conf Exp s (Write VT f x))
                   (Conf Exp s' e) ->
  P0 (f x) -> P0 s'.
  intros.
  inversion X; subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.  
  unfold b_exec.
  unfold b_mod.
  unfold xf_write.
  simpl.
  eapply inj_pair2 in H8.
  rewrite H8.
  exact H.  
  inversion X0.
Qed.  

Definition WriteT1SHT {T: Type} (VT: ValTyp T) (f: T -> W)
           (P0: W -> Prop)
           (fenv: funEnv) (env: valEnv) (x: T) :=
  HoareTriple_Step (fun _ => P0 (f x)) (fun _ s => P0 s)
                   fenv env (Write VT f x).

Lemma write_T_1_sht {T: Type} (VT: ValTyp T) (f: T -> W)
      (P0: W -> Prop) 
      (fenv: funEnv) (env: valEnv) (x: T):  
  forall (s s': W) (e: Exp),
    WriteT1SHT VT f P0 fenv env x.
  unfold WriteT1SHT.
  unfold HoareTriple_Step.
  intros.
  eapply write_T_1.
  eauto.
  auto.
Qed.


(**********************************************************************)  


Lemma bindn_congruence0 (P P1: W -> Prop) 
      (fenv: funEnv) (env: valEnv) (e e': Exp) :
    (forall s, P s -> P1 s) -> 
    HoareTriple_Step P (fun _ => P1) fenv env e ->
    forall e1: Exp,
    HoareTriple_Step P (fun _ => P1) fenv env (BindN e e1).
  unfold HoareTriple_Step, HoareTriple_Eval.
  intros E H e1 s1 s2 e2.
  intros H0 H1.
  inversion H0; subst.
  eapply E.
  auto.
  eapply H in X.
  auto.
  auto.
Qed.  


Lemma bindn_congruence1 (P: W -> Prop) 
      (fenv: funEnv) (env: valEnv) (e e': Exp) :
    HoareTriple_Step P (fun _ => P) fenv env e ->
    forall e1: Exp,
    HoareTriple_Step P (fun _ => P) fenv env (BindN e e1).
  unfold HoareTriple_Step, HoareTriple_Eval.
  intros H e1 s1 s2 e2.
  intros H0 H1.
  inversion H0; subst.
  auto.
  eapply H in X.
  auto.
  auto.
Qed.  


Lemma bindn_congruence2 (P P1: W -> Prop) 
      (fenv: funEnv) (env: valEnv) (e e': Exp) :
    HoareTriple_Step P (fun _ => P1) fenv env e ->
    (forall (e1: Exp) (v: Value),
       HoareTriple_Step P (fun _ => P1) fenv env (BindN (Val v) e1)) ->
    forall e1: Exp,
    HoareTriple_Step P (fun _ => P1) fenv env (BindN e e1).
  unfold HoareTriple_Step, HoareTriple_Eval.
  intros H K e1 s1 s2 e2.
  intros H0 H1.
  inversion H0; subst.
  eapply K.
  eauto.
  auto.
  eapply H in X.
  auto.
  auto.
Qed.  

(*************************************************************************)

Lemma BindN_VHT1 (P0 P1: W -> Prop) (P2: Value -> W -> Prop) 
      (fenv: funEnv) (env: valEnv) (e1 e2: Exp) 
      (k1: forall (e:Exp) (s: W), sigT (fun v: Value =>
                 sigT (fun s': W => 
             EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v)))))
      (k2: forall (e:Exp) (s s1 s2: W) (v1 v2: Value), 
          EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
          EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) -> 
                (s1 = s2) /\ (v1 = v2)) :
  HoareTriple_Eval P0 (fun _ => P1) fenv env e1 ->
  HoareTriple_Eval P1 P2 fenv env e2 ->
  HoareTriple_Eval P0 P2 fenv env (BindN e1 e2).
  unfold HoareTriple_Eval.
  intros.
  eapply BindN_BStep1 in X.
  destruct X as [s1 X].
  destruct X as [v1 X].
  eapply H0.
  eauto.  
  eapply H.
  eauto. 
  auto.
  auto.
  auto.  
Qed.


Lemma BindS_VHT1 (P0: W -> Prop) (P1 P2: Value -> W -> Prop)

(fenv: funEnv) (env: valEnv) (e1 e2: Exp) (x: Id)

(k1: forall (fenv: funEnv) (env: valEnv) (e:Exp) (s: W),
       sigT (fun v: Value =>
                 sigT (fun s': W =>
             EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v)))))

      (k2: forall (e:Exp) (s s1 s2: W) (v1 v2: Value),
          EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
          EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) ->
                (s1 = s2) /\ (v1 = v2)) :

  HoareTriple_Eval P0 P1 fenv env e1 ->
  (forall v, HoareTriple_Eval (P1 v) P2 fenv ((x,v)::env) e2) ->
  HoareTriple_Eval P0 P2 fenv env (BindS x e1 e2).
Proof.
  unfold HoareTriple_Eval.
  intros.
  eapply BindS_BStep1 in X.
  destruct X as [s1 X].
  destruct X as [v1 X].
  eapply H0.
  eauto.  
  eapply H.
  eauto. 
  auto.
  auto.
  auto.  
Qed.


Lemma Apply_VHT1 (P0: W -> Prop) (P1: list Value -> W -> Prop)
                 (P2: Value -> W -> Prop)  
   (fenv: funEnv) (env: valEnv) (f: Fun) (es: list Exp) 
     (k1: forall (fenv: funEnv) (env: valEnv) (e:Exp) (s: W),
       sigT (fun v: Value =>
                 sigT (fun s': W =>
             EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v)))))

     (k2: forall (fenv: funEnv) (env: valEnv) (es:list Exp) (s: W),
      sigT (fun vs: list Value =>
                 sigT (fun s': W => 
      PrmsClosure fenv env (Conf Prms s (PS es))
                           (Conf Prms s' (PS (map Val vs))))))
 
     (k3: forall (e:Exp) (s s1 s2: W) (v1 v2: Value),
          EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
          EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) ->
          (s1 = s2) /\ (v1 = v2)) :

  HoarePrmsTriple_Eval P0 P1 fenv env es ->
  match f with
  | FC fenv' tenv' e0 e1 x n => 
    length tenv' = length es /\     
    match n with
    | 0 => (forall vs: list Value,  
          HoareTriple_Eval (P1 vs) P2 fenv' (mkVEnv tenv' vs) e0)
    | S n' => (forall vs: list Value,
          HoareTriple_Eval (P1 vs) P2 ((x,FC fenv' tenv' e0 e1 x n')::fenv')
                           (mkVEnv tenv' vs) e1)
    end
  end ->             
  HoareTriple_Eval P0 P2 fenv env (Apply (QF f) (PS es)).
Proof.
  unfold HoareTriple_Eval, HoarePrmsTriple_Eval.
  intros.
  generalize (Apply_BStep1 fenv env f es v s s' k1 k2 k3).
  intro P.
  destruct f.
  destruct H0.
  specialize (P H0 X).
  destruct P as [s1 P].
  destruct P as [vs P].
  specialize (H s s1 vs P H1).
  destruct n.
  specialize (H2 vs s1 s' v y H).
  exact H2.
  specialize (H2 vs s1 s' v y H).
  exact H2.
Qed.  
  

End Hoare.