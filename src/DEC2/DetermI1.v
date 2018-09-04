(*  DEC 2.0 language specification.
   Paolo Torrini  
   Universite' de Lille - CRIStAL-CNRS
*)

Require Import List.
Require Import Equality.
Require Import Eqdep.
Require Import PeanoNat.
Require Import Omega.
Require Import Eqdep FunctionalExtensionality Tactics.
Require Import JMeq.
Require Import ProofIrrelevance.


Require Import AuxLibI1.
Require Import TypSpecI1. 
Require Import ModTypI1. 
Require Import LangSpecI1. 
Require Import StaticSemI1.
Require Import DynamicSemI1.
Require Import WeakenI1.
Require Import UniqueTypI1.
Require Import DerivDynI1.
Require Import TransPrelimI1.
Require Import TSoundnessI1.
Require Import SReducI1.


Import ListNotations.


Module Determ (IdT: ModTyp) <: ModTyp.

Module SReducL := SReduc IdT.
Export SReducL.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Open Scope type_scope.


(** stepwise determinism *)

Definition UniqueEStep 
                     (fenv: funEnv) (env: valEnv)
                     (s s1 s2: W) (n n1 n2: nat) (e e1 e2: Exp) :=
    EStep fenv env (Conf Exp s n e) ((Conf Exp s1 n1 e1)) ->
    EStep fenv env (Conf Exp s n e) ((Conf Exp s2 n2 e2)) -> 
        (s1 = s2) /\ (n1 = n2) /\ (e1 = e2).


Definition UniquePStep
                     (fenv: funEnv) (env: valEnv)
                     (s s1 s2: W) (n n1 n2: nat) (ps ps1 ps2: Prms) := 
    PStep fenv env (Conf Prms s n ps) ((Conf Prms s1 n1 ps1)) ->
    PStep fenv env (Conf Prms s n ps) ((Conf Prms s2 n2 ps2)) -> 
       (s1 = s2) /\ (n1 = n2) /\ (ps1 = ps2).



(*******************************************************)

Definition DPar_E (n9: nat) :=
  fun (ftenv: funTC) (tenv: valTC) 
      (e: Exp) (t: VTyp) 
      (p: ExpTyping ftenv tenv e t) =>
  forall (fenv: funEnv) (env: valEnv),                      
    FEnvTyping fenv ftenv ->
    EnvTyping env tenv ->
  forall (n: nat), n <= n9 ->   
  forall (s s1 s2: W) (n1 n2: nat) (e1 e2: Exp), 
         UniqueEStep fenv env s s1 s2 n n1 n2 e e1 e2.


Definition DPar_P (n9: nat) :=
  fun (ftenv: funTC) (tenv: valTC) 
                (ps: Prms) (pt: PTyp) 
                (p: PrmsTyping ftenv tenv ps pt) => 
  forall (fenv: funEnv) (env: valEnv),                      
    FEnvTyping fenv ftenv ->
    EnvTyping env tenv ->
  forall (n: nat), n <= n9 -> 
  forall (s s1 s2: W) (n1 n2: nat) (ps1 ps2: Prms),  
          UniquePStep fenv env s s1 s2 n n1 n2 ps ps1 ps2.


Definition ExpTypingDet_mut (n: nat) :=
  ExpTyping_mut (DPar_E n) (DPar_P n).

Definition PrmsTypingDet_mut (n: nat) :=
  PrmsTyping_mut (DPar_E n) (DPar_P n).


(************************************************************************)

Lemma deterAux1 (s1 s2: W) (n1 n2: nat) (v1 v2: Value) (e3 e4 e5 e6: Exp) :
  Conf Exp s1 n1 (IfThenElse (Val v1) e3 e4) =
  Conf Exp s2 n2 (IfThenElse (Val v2) e5 e6) ->
  v1 = v2.
  intros.
  inversion H; subst.
  auto.
 Defined.

Lemma deterAux2 (s1 s2: W) (n1 n2: nat) (e1 e2 e3 e4 e5 e6: Exp) :
  Conf Exp s1 n1 (IfThenElse e1 e3 e4) =
  Conf Exp s2 n2 (IfThenElse e2 e5 e6) ->
  e1 = e2.
  intros.
  inversion H; subst.
  auto.
 Defined.


Lemma ExpDeterm_Val (n: nat) :
  forall (ftenv : funTC) (tenv : valTC) (v : Value) 
    (t : VTyp) (v0 : VTyping v t),
  DPar_E n ftenv tenv (Val v) t (Val_Typing ftenv tenv v t v0).
  unfold DPar_E.
  unfold UniqueEStep.
  intros.
  inversion X0.
Defined.

Lemma ExpDeterm_Var (n: nat) :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (t : VTyp) (i : IdTyping tenv x t),
    DPar_E n ftenv tenv (Var x) t (Var_Typing ftenv tenv x t i).
  unfold DPar_E, UniqueEStep.
  intros.
  inversion X; subst.
  inversion X0; subst.
  rewrite H5 in H6.
  inversion H6; subst.
  auto.
Defined.  

Lemma ExpDeterm_BindN (n: nat) :
  forall (ftenv : funTC) (tenv : valTC) (e1 e2 : Exp) 
    (t1 t2 : VTyp) (e : ExpTyping ftenv tenv e1 t1),
  DPar_E n ftenv tenv e1 t1 e ->
  forall e0 : ExpTyping ftenv tenv e2 t2,
  DPar_E n ftenv tenv e2 t2 e0 ->
  DPar_E n ftenv tenv (BindN e1 e2) t2
    (BindN_Typing ftenv tenv e1 e2 t1 t2 e e0).
  unfold DPar_E, UniqueEStep.
  intros.
  inversion X; subst.
  inversion X0; subst.
  auto.
  inversion X1.
  inversion X0; subst.
  inversion X1.
  specialize (H fenv env H1 H2 n0 H3 s s1 s2 n1 n2 e1' e1'0 X1 X2).
  destruct H as [c1 H].
  destruct H as [c2 c3].
  inversion c1; subst.
  auto.
Defined.


Lemma ExpDeterm_BindS (n: nat) :
  forall (ftenv : funTC) (tenv tenv' : valTC) (x : StaticSemL.Id)
    (e1 e2 : Exp) (t1 t2 : VTyp) (m : option VTyp) 
    (m0 : Maybe t1 m) (e : tenv' = (x, t1) :: tenv)
    (e0 : ExpTyping ftenv tenv e1 t1),
  DPar_E n ftenv tenv e1 t1 e0 ->
  forall e3 : ExpTyping ftenv tenv' e2 t2,
  DPar_E n ftenv tenv' e2 t2 e3 ->
  DPar_E n ftenv tenv (BindS x m e1 e2) t2
         (BindS_Typing ftenv tenv tenv' x e1 e2 t1 t2 m m0 e e0 e3).
  unfold DPar_E, UniqueEStep.
  intros.
  inversion X; subst.
  inversion X0; subst.
  auto.
  inversion X1.
  inversion X0; subst.
  inversion X1.
  specialize (H fenv env H1 H2 n0 H3 s s1 s2 n1 n2 e1' e1'0 X1 X2).
  destruct H as [c1 H].
  destruct H as [c2 c3].
  inversion c1; subst.
  auto.
Defined.  

Lemma ExpDeterm_BindMS (n: nat) :
  forall (ftenv : funTC) (tenv tenv0 tenv1 : valTC) 
    (env0 : valEnv) (e : Exp) (t : VTyp) (e0 : EnvTyping env0 tenv0)
    (e1 : tenv1 = tenv0 ++ tenv) (e2 : ExpTyping ftenv tenv1 e t),
  DPar_E n ftenv tenv1 e t e2 ->
  DPar_E n ftenv tenv (BindMS env0 e) t
    (BindMS_Typing ftenv tenv tenv0 tenv1 env0 e t e0 e1 e2).
  unfold DPar_E, UniqueEStep.
  intros.
  inversion X; subst.
  inversion X0; subst.
  auto.
  inversion X1.
  inversion X0; subst.
  inversion X1.
  assert (EnvTyping (env0 ++ env) (tenv0 ++ tenv)) as H1'.
  eapply overrideEnvLemma.
  assumption.
  assumption.
  specialize (H fenv (env0 ++ env) H0 H1' n0 H2 s s1 s2 n1 n2 e' e'0 X1 X2).
  destruct H as [c1 H].
  destruct H as [c2 c3].
  inversion c1; subst.
  auto.
Defined.


Lemma ExpDeterm_IfThenElse (n: nat) :
  forall (ftenv : funTC) (tenv : valTC) (e1 e2 e3 : Exp) 
    (t : VTyp) (e : ExpTyping ftenv tenv e1 Bool),
  DPar_E n ftenv tenv e1 Bool e ->
  forall e0 : ExpTyping ftenv tenv e2 t,
  DPar_E n ftenv tenv e2 t e0 ->
  forall e4 : ExpTyping ftenv tenv e3 t,
  DPar_E n ftenv tenv e3 t e4 ->
  DPar_E n ftenv tenv (IfThenElse e1 e2 e3) t
         (IfThenElse_Typing ftenv tenv e1 e2 e3 t e e0 e4).
  unfold DPar_E, UniqueEStep.
  intros.
  inversion X; subst.
  inversion X0; subst.
  auto.
  eapply deterAux1 in H7.
  unfold cst in H7.
  eapply inj_pair2 in H7.
  inversion H7.
  inversion X0; subst.
  rewrite <- H14.
  rewrite <- H14.
  auto.
  inversion X1.
  inversion X2.

  inversion X0; subst.
  eapply deterAux1 in H7.
  unfold cst in H7.
  eapply inj_pair2 in H7.
  inversion H7.
  auto.
  inversion X1.
  inversion X0; subst.
  inversion X1.
  inversion X1.
  assert (s1 = s2 /\ n1 = n2 /\ e' = e'0).
  eapply H.
  exact H2.
  exact H3.
  exact H4.
  exact X1.
  exact X2.
  destruct H5.
  destruct H6.
  rewrite H7.
  auto.
Defined.  


Lemma ExpDeterm_Apply0 :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (e : Exp) (ps : Prms) (pt : PTyp) (t : VTyp) (p : Pure e)
    (i : IdFTyping ftenv x (FT pt t)) (p0 : PrmsTyping ftenv tenv ps pt),
  DPar_P 0 ftenv tenv ps pt p0 ->
  forall e0 : ExpTyping ftenv tenv e Nat,
  DPar_E 0 ftenv tenv e Nat e0 ->
  DPar_E 0 ftenv tenv (Apply x ps e) t
    (Apply_Typing ftenv tenv x e ps pt t p i p0 e0).
  unfold DPar_E, DPar_P, UniqueEStep, UniquePStep.
  intros.  
  assert (n = 0) as q.
  omega.
  inversion q; subst.
  clear H4.
  inversion X0; subst.
  inversion X; subst.
  assert ( s1 = s2 /\ n1 = n2 /\ e'0 = e').
  eapply H0.
  exact H1.
  exact H2.
  exact H3.
  exact X2.
  exact X1.
  destruct H4.
  destruct H5.
  inversion H6; subst.
  auto.
  inversion X1.
  inversion X1.
  
  inversion X; subst.
  inversion X2.

  assert (s1 = s2 /\ n1 = n2 /\ ps'0 = ps').
  eapply H.
  exact H1.
  exact H2.
  exact H3.
  exact X2.
  exact X1.
  destruct H4.
  destruct H5.
  inversion H6; subst.
  auto.
  assert (False).
  destruct ps'.
  eapply (NoPrmsStep fenv env (s1,0) (s2,n2)).
  simpl.
  exact X1.
  exact X2.
  inversion H4.

  inversion X; subst.
  inversion X2.

  assert (False).
  destruct ps'.
  eapply (NoPrmsStep fenv env (s2,0) (s1,n1)).
  simpl.
  exact X2.
  exact X1.
  inversion H4.
  unfold cst in H8.
  eapply inj_pair2 in H8.
  inversion H8; subst.
  auto.
Defined.  


Lemma ExpDeterm_Call0 :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  DPar_P 0 ftenv tenv (PS ls) pt p ->
  DPar_E 0 ftenv tenv (Call x (PS ls)) t
         (Call_Typing ftenv tenv x ls pt t i p).
  unfold DPar_E, DPar_P, UniqueEStep, UniquePStep.
  intros.  
  assert (n = 0) as q.
  omega.
  inversion q; subst.
  clear H3.
  inversion X0; subst.
  inversion X; subst.
  assert (s1 = s2 /\ n1 = n2 /\ ps'0 = ps').
  eapply H.
  exact H0.
  exact H1.
  exact H2.
  exact X2.
  exact X1.
  destruct H3.
  destruct H4.
  inversion H5; subst.
  auto.

  eapply isValueList2IsValueT in X2.
  assert (False).
  destruct ps'.
  eapply (NoPrmsStep fenv env (s1,0) (s2,n2)).
  simpl.
  exact X1.
  exact X2.
  inversion H3.

  inversion X; subst.  
  eapply isValueList2IsValueT in X1.
  assert (False).
  destruct ps'.
  eapply (NoPrmsStep fenv env (s2,0) (s1,n1)).
  simpl.
  exact X2.
  exact X1.
  inversion H3.

  rewrite H10 in H11.
  inversion H11; subst.
  auto.
Defined.


Lemma ExpDeterm_Modify (n: nat) :
  forall (ftenv : funTC) (tenv : valTC) (t1 t2 : VTyp) 
    (XF : XFun t1 t2) (e : Exp) (e0 : ExpTyping ftenv tenv e t1),
  DPar_E n ftenv tenv e t1 e0 ->
  DPar_E n ftenv tenv (Modify t1 t2 XF e) t2
         (Modify_Typing ftenv tenv t1 t2 XF e e0).
  unfold DPar_E, UniqueEStep.
  intros.
  inversion X; subst.
  eapply inj_pair2 in H10.
  eapply inj_pair2 in H10.
  inversion H10; subst.
  clear H3.

  inversion X0; subst.
  eapply inj_pair2 in H12.
  inversion H12; subst.
  clear H11 H3.
  eapply inj_pair2 in H10.
  eapply inj_pair2 in H10.
  inversion H10; subst.
  clear H3.
  auto.
  
  inversion X1.

  eapply inj_pair2 in H10.
  eapply inj_pair2 in H10.
  inversion H10; subst.
  clear H3.
  
  inversion X0; subst.

  eapply inj_pair2 in H10.
  eapply inj_pair2 in H10.
  inversion H10; subst.
  clear H3.

  inversion X1.
  
  eapply inj_pair2 in H10.
  eapply inj_pair2 in H10.
  inversion H10; subst.
  clear H3.

  assert (s1 = s2 /\ n1 = n2 /\ e' = e'0).
  eapply H.
  exact H0.
  exact H1.
  exact H2.
  exact X1.
  exact X2.
  destruct H3.
  destruct H4.
  inversion H5; subst.
  auto.
Defined.


Lemma ExpDeterm_Nil (n: nat) :
  forall (ftenv : funTC) (tenv : valTC),
  DPar_P n ftenv tenv (PS []) (PT []) (PSNil_Typing ftenv tenv).
  unfold DPar_P, UniquePStep.
  intros.
  inversion X0.
Defined.


Lemma ExpDeterm_Cons (n: nat) :
  forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp) 
    (es : list Exp) (ts : list VTyp) (e0 : ExpTyping ftenv tenv e t),
  DPar_E n ftenv tenv e t e0 ->
  forall p : PrmsTyping ftenv tenv (PS es) (PT ts),
  DPar_P n ftenv tenv (PS es) (PT ts) p ->
  DPar_P n ftenv tenv (PS (e :: es)) (PT (t :: ts))
         (PSCons_Typing ftenv tenv e t es ts e0 p).
  unfold DPar_P, UniquePStep, DPar_E, UniqueEStep.
  intros.
  inversion X; subst.
  inversion X0; subst.
  assert (s1 = s2 /\ n1 = n2 /\ PS es' = PS es'0).
  eapply H0.
  exact H1.
  exact H2.
  exact H3.
  exact X1.
  exact X2.
  destruct H4.
  destruct H5.
  inversion H6; subst.
  auto.

  inversion X2.
  inversion X0; subst.
  inversion X1.
  
  assert (s1 = s2 /\ n1 = n2 /\ e' = e'0).
  eapply H.
  exact H1.
  exact H2.
  exact H3.
  exact X1.
  exact X2.

  destruct H4.
  destruct H5.
  inversion H6; subst.
  auto.
Defined.


Lemma ExpDeterm_CallS (n: nat) 
  (IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
         ExpTyping ftenv tenv e t ->
         forall (fenv : funEnv) (env : valEnv),
         FEnvTyping fenv ftenv ->
         EnvTyping env tenv ->
         forall n0 : nat,
         n0 <= n ->
         forall (s s1 s2 : W) (n1 n2 : nat) (e1 e2 : Exp),
         UniqueEStep fenv env s s1 s2 n0 n1 n2 e e1 e2) : 
  forall (ftenv : funTC) (tenv : valTC) (x : Id) 
    (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  DPar_P (S n) ftenv tenv (PS ls) pt p ->
  DPar_E (S n) ftenv tenv (Call x (PS ls)) t
         (Call_Typing ftenv tenv x ls pt t i p).
  unfold DPar_E, DPar_P, UniqueEStep, UniquePStep.
  intros.  

  inversion X0; subst.
  inversion X; subst.
  assert (s1 = s2 /\ n1 = n2 /\ ps'0 = ps').
  eapply H.
  exact H0.
  exact H1.
  exact H2.
  exact X2.
  exact X1.
  destruct H3.
  destruct H4.
  inversion H5; subst.
  auto.

  eapply isValueList2IsValueT in X2.
  assert (False).
  destruct ps'.
  eapply (NoPrmsStep fenv env (s1,0) (s2,n2)).
  simpl.
  exact X1.
  exact X2.
  inversion H3.

  eapply isValueList2IsValueT in X2.
  assert (False).
  destruct ps'.
  eapply (NoPrmsStep fenv env (s1,(S n1)) (s2,n2)).
  simpl.
  exact X1.
  exact X2.
  inversion H3.
  
  inversion X; subst.  
  eapply isValueList2IsValueT in X1.
  assert (False).
  destruct ps'.
  eapply (NoPrmsStep fenv env (s2,0) (s1,n1)).
  simpl.
  exact X2.
  exact X1.
  inversion H3.

  rewrite H10 in H11.
  inversion H11; subst.
  auto.
 
  inversion X; subst.
  eapply isValueList2IsValueT in X1.
  assert (False).
  destruct ps'.
  eapply (NoPrmsStep fenv env (s2,(S n2)) (s1,n1)).
  simpl.
  exact X2.
  exact X1.
  inversion H3.

  rewrite H10 in H11.
  inversion H11; subst.

  inversion X1; subst.
  inversion X2; subst.

  eapply mapEq in H4.
  inversion H4; subst.
  auto.
Defined.

  
Lemma ExpDeterm_ApplyS (n: nat) 
  (IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
         ExpTyping ftenv tenv e t ->
         forall (fenv : funEnv) (env : valEnv),
         FEnvTyping fenv ftenv ->
         EnvTyping env tenv ->
         forall n0 : nat,
         n0 <= n ->
         forall (s s1 s2 : W) (n1 n2 : nat) (e1 e2 : Exp),
         UniqueEStep fenv env s s1 s2 n0 n1 n2 e e1 e2) :
  forall (ftenv : funTC) (tenv : valTC) (x : Id) 
    (e : Exp) (ps : Prms) (pt : PTyp) (t : VTyp) (p : Pure e)
    (i : IdFTyping ftenv x (FT pt t)) (p0 : PrmsTyping ftenv tenv ps pt),
  DPar_P (S n) ftenv tenv ps pt p0 ->
  forall e0 : ExpTyping ftenv tenv e Nat,
  DPar_E (S n) ftenv tenv e Nat e0 ->
  DPar_E (S n) ftenv tenv (Apply x ps e) t
         (Apply_Typing ftenv tenv x e ps pt t p i p0 e0).
  unfold DPar_E, DPar_P, UniqueEStep, UniquePStep.
  intros.  

  inversion X0; subst.
  inversion X; subst.
  assert ( s1 = s2 /\ n1 = n2 /\ e'0 = e').
  eapply H0.
  exact H1.
  exact H2.
  exact H3.
  exact X2.
  exact X1.
  destruct H4.
  destruct H5.
  inversion H6; subst.
  auto.
  inversion X1.
  inversion X1.
  
  inversion X; subst.
  inversion X2.

  assert (s1 = s2 /\ n1 = n2 /\ ps'0 = ps').
  eapply H.
  exact H1.
  exact H2.
  exact H3.
  exact X2.
  exact X1.
  destruct H4.
  destruct H5.
  inversion H6; subst.
  auto.
  assert (False).
  destruct ps'.
  eapply (NoPrmsStep fenv env (s1,n0) (s2,n2)).
  simpl.
  exact X1.
  exact X2.
  inversion H4.

  inversion X; subst.
  inversion X2.

  assert (False).
  destruct ps'.
  eapply (NoPrmsStep fenv env (s2,n0) (s1,n1)).
  simpl.
  exact X2.
  exact X1.
  inversion H4.
  unfold cst in H8.
  eapply inj_pair2 in H8.
  inversion H8; subst.
  auto.
Defined.  
  

Lemma ExpDeterm (n9: nat) :
  forall (ftenv: funTC) (tenv: valTC) 
         (e: Exp) (t: VTyp),   
      ExpTyping ftenv tenv e t -> 
  forall (fenv: funEnv) (env: valEnv),                      
    FEnvTyping fenv ftenv ->
    EnvTyping env tenv ->
  forall (n: nat), n <= n9 ->   
  forall (s s1 s2: W) (n1 n2: nat) (e1 e2: Exp), 
         UniqueEStep fenv env s s1 s2 n n1 n2 e e1 e2.
Proof.
induction n9.
eapply (ExpTypingDet_mut 0).
- (* Val *)
  eapply (ExpDeterm_Val 0).
- (* Var *)
  eapply (ExpDeterm_Var 0).
- (* BindN *)
  eapply (ExpDeterm_BindN 0).
- (* BindS *)  
  eapply (ExpDeterm_BindS 0).
-  (* BindMS *)  
  eapply (ExpDeterm_BindMS 0).
-   (* IfThenElse *)
  eapply (ExpDeterm_IfThenElse 0).
-   (* Apply *)  
  eapply ExpDeterm_Apply0. 
-   (* Call *)  
  eapply ExpDeterm_Call0. 
- (* Modify *)
  eapply (ExpDeterm_Modify 0).
- eapply (ExpDeterm_Nil 0).
- eapply (ExpDeterm_Cons 0).
- eapply (ExpTypingDet_mut (S n9)).
  * eapply (ExpDeterm_Val (S n9)).
  * eapply (ExpDeterm_Var (S n9)).
  * eapply (ExpDeterm_BindN (S n9)).
  * eapply (ExpDeterm_BindS (S n9)).
  * eapply (ExpDeterm_BindMS (S n9)).
  * eapply (ExpDeterm_IfThenElse (S n9)).
  * eapply (ExpDeterm_ApplyS n9).
    assumption.
  * eapply (ExpDeterm_CallS n9).
    assumption.
  * eapply (ExpDeterm_Modify (S n9)).
  * eapply (ExpDeterm_Nil (S n9)).
  * eapply (ExpDeterm_Cons (S n9)).
Defined.


Lemma ExpDeterm_aux1 (n9 : nat)
  (IHn9 : forall (ftenv : funTC) (tenv : valTC) (ps : Prms) (pt : PTyp),
         PrmsTyping ftenv tenv ps pt ->
         forall (fenv : funEnv) (env : valEnv),
         FEnvTyping fenv ftenv ->
         EnvTyping env tenv ->
         forall n : nat,
         n <= n9 ->
         forall (s s1 s2 : W) (n1 n2 : nat) (ps1 ps2 : Prms),
         UniquePStep fenv env s s1 s2 n n1 n2 ps ps1 ps2) : 
  forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
  ExpTyping ftenv tenv e t ->
  forall (fenv : funEnv) (env : valEnv),
  FEnvTyping fenv ftenv ->
  EnvTyping env tenv ->
  forall n0 : nat,
  n0 <= n9 ->
  forall (s s1 s2 : W) (n1 n2 : nat) (e1 e2 : Exp),
    UniqueEStep fenv env s s1 s2 n0 n1 n2 e e1 e2.
  unfold UniquePStep, UniqueEStep in *.
  intros.
  assert (s1 = s2 /\ n1 = n2 /\ PS [e1] = PS [e2]).
  eapply (IHn9 ftenv tenv (PS [e]) (PT [t])).
  constructor.
  assumption.
  constructor.
  eassumption.
  eassumption.
  exact H1.
  econstructor.
  exact X0.
  econstructor.
  exact X1.
  destruct H2.
  destruct H3.
  inversion H4; subst.
  auto.
Defined.

  
Lemma PrmsDeterm (n9: nat) :
  forall (ftenv: funTC) (tenv: valTC) 
         (ps: Prms) (pt: PTyp),   
      PrmsTyping ftenv tenv ps pt -> 
  forall (fenv: funEnv) (env: valEnv),                      
    FEnvTyping fenv ftenv ->
    EnvTyping env tenv ->
  forall (n: nat), n <= n9 ->   
  forall (s s1 s2: W) (n1 n2: nat) (ps1 ps2: Prms), 
         UniquePStep fenv env s s1 s2 n n1 n2 ps ps1 ps2.
Proof.
induction n9.
eapply (PrmsTypingDet_mut 0).
- (* Val *)
  eapply (ExpDeterm_Val 0).
- (* Var *)
  eapply (ExpDeterm_Var 0).
- (* BindN *)
  eapply (ExpDeterm_BindN 0).
- (* BindS *)  
  eapply (ExpDeterm_BindS 0).
-  (* BindMS *)  
  eapply (ExpDeterm_BindMS 0).
-   (* IfThenElse *)
  eapply (ExpDeterm_IfThenElse 0).
-   (* Apply *)  
  eapply ExpDeterm_Apply0. 
-   (* Call *)  
  eapply ExpDeterm_Call0. 
- (* Modify *)
  eapply (ExpDeterm_Modify 0).
- eapply (ExpDeterm_Nil 0).
- eapply (ExpDeterm_Cons 0).
- eapply (PrmsTypingDet_mut (S n9)).
  * eapply (ExpDeterm_Val (S n9)).
  * eapply (ExpDeterm_Var (S n9)).
  * eapply (ExpDeterm_BindN (S n9)).
  * eapply (ExpDeterm_BindS (S n9)).
  * eapply (ExpDeterm_BindMS (S n9)).
  * eapply (ExpDeterm_IfThenElse (S n9)).
  * eapply (ExpDeterm_ApplyS n9).
    eapply (ExpDeterm_aux1 n9 IHn9).   
  * eapply (ExpDeterm_CallS n9).
    eapply (ExpDeterm_aux1 n9 IHn9).   
  * eapply (ExpDeterm_Modify (S n9)).
  * eapply (ExpDeterm_Nil (S n9)).
  * eapply (ExpDeterm_Cons (S n9)).
Defined.

(*********************************************************************)

(** Confluence of evaluation *)

Definition UniqueEClos (fenv: funEnv) (env: valEnv)
           (s s1 s2: W) (n n1 n2: nat)
           (e : Exp) (v1 v2: Value) :=
    EClosure fenv env (Conf Exp s n e) ((Conf Exp s1 n1 (Val v1))) ->
    EClosure fenv env (Conf Exp s n e) ((Conf Exp s2 n2 (Val v2))) -> 
        (n1 = n2) /\ (s1 = s2) /\ (v1 = v2).

Definition UniquePClos (fenv: funEnv) (env: valEnv)
           (s s1 s2: W) (n n1 n2: nat)
           (ps : Prms) (vs1 vs2: list Value) :=
  PClosure fenv env (Conf Prms s n ps)
              ((Conf Prms s1 n1 (PS (map Val vs1)))) ->
  PClosure fenv env (Conf Prms s n ps)
              ((Conf Prms s2 n2 (PS (map Val vs2)))) -> 
        (n1 = n2) /\ (s1 = s2) /\ (vs1 = vs2).


Lemma ExpConfluence (n: nat) :
  forall (ftenv: funTC) (tenv: valTC) 
         (e: Exp) (t: VTyp),   
      ExpTyping ftenv tenv e t -> 
  forall (fenv: funEnv) (D: FEnvWT fenv) (env: valEnv),                      
    FEnvTyping fenv ftenv ->
    EnvTyping env tenv ->
  forall (n0: nat), n0 <= n ->   
  forall (s s1 s2: W) (n1 n2: nat) (v1 v2: Value), 
         UniqueEClos fenv env s s1 s2 n0 n1 n2 e v1 v2.
Proof.
  unfold UniqueEClos.
  intros.  
  dependent induction X0.
  intros.
  dependent destruction X1.
  auto.
  inversion e.
  destruct p2.

  assert (ExpTyping ftenv tenv qq t) as K1.
  {- eapply (ExpSubjectRed fenv D ftenv tenv).
     exact X.
     exact H.
     exact H0.
     exact e0.
  }
  assert (fuel <= n) as q.
  {- eapply StepIsEClos in e0.
     eapply ExpDecrease in e0.
     omega.
  }   
  assert (EClosure fenv env (Conf Exp state fuel qq)
                   (Conf Exp s2 n2 (Val v2))) as K2.
  {- inversion X1; subst.
     inversion e0.
     destruct p2.
     assert (state0 = state /\ fuel0 = fuel /\ qq0 = qq).
     {+ eapply ExpDeterm.
        exact X.
        exact H.
        exact H0.
        exact H1.
        exact X2.
        exact e0.
     }
     destruct H2.
     destruct H3.
     inversion H4; subst.
     exact X3.
  }
  specialize (IHX0 qq K1 D H H0 fuel q state s1 n1 v1
                   eq_refl eq_refl K2).
  auto.
Defined.
  

Lemma PrmsConfluence (n: nat) :
  forall (ftenv: funTC) (tenv: valTC) 
         (ps: Prms) (pt: PTyp),   
      PrmsTyping ftenv tenv ps pt -> 
  forall (fenv: funEnv) (D: FEnvWT fenv) (env: valEnv),                      
    FEnvTyping fenv ftenv ->
    EnvTyping env tenv ->
  forall (n0: nat), n0 <= n ->   
  forall (s s1 s2: W) (n1 n2: nat) (vs1 vs2: list Value), 
         UniquePClos fenv env s s1 s2 n0 n1 n2 ps vs1 vs2.
Proof.
  unfold UniquePClos.
  intros.  
  dependent induction X0.
  intros.
  dependent destruction X1.
  eapply mapEq in x.
  inversion x; subst.
  auto.
  destruct p2.
  assert (isValueList2T (map Val vs1) vs1) as u1.
  constructor.
  eapply isValueList2IsValueT in u1.
  assert (False).
  destruct qq.
  eapply (NoPrmsStep fenv env (s1,n1) (state,fuel)).
  simpl.
  exact p.
  exact u1.
  inversion H2.

  destruct p2.
  assert (PrmsTyping ftenv tenv qq pt) as K1.
  {- eapply (PrmsSubjectRed fenv D ftenv tenv).
     exact X.
     exact H.
     exact H0.
     exact p. }
  assert (fuel <= n) as q.
  {- eapply StepIsPClos in p.
     eapply PrmsDecrease in p.
     omega.
  }   
  assert (PClosure fenv env (Conf Prms state fuel qq)
                   (Conf Prms s2 n2 (PS (map Val vs2)))) as K2.
  {- inversion X1; subst.
     + assert (isValueList2T (map Val vs2) vs2) as u1.
       constructor.
       eapply isValueList2IsValueT in u1.
       assert (False).
       destruct qq.
       eapply (NoPrmsStep fenv env (s2,n2) (state,fuel)).
       simpl.
       exact p.
       exact u1.
       inversion H2.
     + 
     destruct p2.
     assert (state0 = state /\ fuel0 = fuel /\ qq0 = qq).
     {+ eapply PrmsDeterm.
        exact X.
        exact H.
        exact H0.
        exact H1.
        exact X2.
        exact p.
     }
     destruct H2.
     destruct H3.
     inversion H4; subst.
     exact X3. 
  }   
  specialize (IHX0 qq K1 D H H0 fuel q state s1 n1 vs1
                   eq_refl eq_refl K2).
  auto.
Defined.  
  
    
End Determ.
