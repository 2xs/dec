(*  DEC 2.0 language specification.
   Paolo Torrini  
   Universite' de Lille - CRIStAL-CNRS
*)

Require Import List.

Require Import AuxLibI1.
Require Import TypSpecI1. 
Require Import ModTypI1. 
Require Import LangSpecI1. 
Require Import StaticSemI1.
Require Import DynamicSemI1.
Require Import WeakenI1.

Import ListNotations.

(** Type uniqueness *)

Module UniqueTyp (IdT: ModTyp) <: ModTyp.

Module WeakenL := Weaken IdT.
Export WeakenL.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.


Definition UniETyping_def :=
  fun (ftenv: funTC) (tenv: valTC)
      (e: Exp) (t1: VTyp) (k: ExpTyping ftenv tenv e t1) => 
  forall (t2: VTyp),       
    ExpTyping ftenv tenv e t2 -> 
        t1 = t2.

Definition UniPTyping_def :=
  fun (ftenv: funTC) (tenv: valTC)
      (ps: Prms) (pt1: PTyp) (k: PrmsTyping ftenv tenv ps pt1) => 
    forall (pt2: PTyp),  
      PrmsTyping ftenv tenv ps pt2 -> 
        pt1 = pt2.

Definition UniType_ExpTyping_mut :=
                      ExpTyping_mut UniETyping_def UniPTyping_def.
  
Definition UniType_PrmsTyping_mut :=
                      PrmsTyping_mut UniETyping_def UniPTyping_def.

(****************************************************************************)

Lemma UniVTyping :
  forall (v: Value) (t1 t2: VTyp),
    VTyping v t1 -> 
    VTyping v t2 ->
    t1 = t2.
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  reflexivity.
Defined.  

Lemma UniIdTyping :
  forall (tenv: valTC) (x: Id) (t1 t2: VTyp),
    IdTyping tenv x t1 -> 
    IdTyping tenv x t2 ->
    t1 = t2.
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  destruct (findE tenv x).
  inversion H2; subst.
  inversion H3; subst.
  reflexivity.
  inversion H2.
Defined.  

Lemma UniIdFTyping :
  forall (ftenv: funTC) (x: Id) (ft1 ft2: FTyp),
    IdFTyping ftenv x ft1 -> 
    IdFTyping ftenv x ft2 ->
    ft1 = ft2.
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  destruct (findE ftenv x).
  inversion H2; subst.
  inversion H3; subst.
  reflexivity.
  inversion H2.
Defined.  

Lemma UniEnvTyping :
  forall (env: valEnv) (tenv1 tenv2: valTC),
    EnvTyping env tenv1 -> 
    EnvTyping env tenv2 ->
    tenv1 = tenv2.
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  reflexivity.
Defined.

Lemma UniFEnvTyping :
  forall (fenv: funEnv) (ftenv1 ftenv2: funTC),
    FEnvTyping fenv ftenv1 -> 
    FEnvTyping fenv ftenv2 ->
    ftenv1 = ftenv2.
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  reflexivity.
Defined.


Lemma UniETyping :
  forall (ftenv: funTC) (tenv: valTC)
         (e: Exp) (t1: VTyp),   
      ExpTyping ftenv tenv e t1 -> 
      forall (t2: VTyp), 
         ExpTyping ftenv tenv e t2 -> 
         t1 = t2.
Proof.
  intros.
  eapply UniType_ExpTyping_mut.
  - intros.
    unfold UniETyping_def.
    intros.
    inversion X1; subst.
    eapply UniVTyping.
    exact v0.
    assumption.
  - intros.
    unfold UniETyping_def.
    intros.
    inversion X1; subst.
    eapply UniIdTyping.
    exact i.
    assumption.
  - intros.
    unfold UniETyping_def in *.
    intros.
    inversion X1; subst.
    eapply H0 in X3.
    exact X3.
  - intros.
    unfold UniETyping_def in *.
    intros.
    inversion X1; subst.
    inversion m0; subst.
    + inversion X2; subst.
      eapply H0 in X4.
      exact X4.
    + eapply H in X3.
      rewrite <- X3 in X4.
      eapply H0 in X4.
      exact X4.
  - intros.
    unfold UniETyping_def in *.
    intros.
    inversion X1; subst.
    assert (tenv1 = tenv4).
    eapply UniEnvTyping.
    exact e1.
    assumption.
    rewrite <- H0 in X2.
    eapply H in X2.
    assumption.
  - intros.
    unfold UniETyping_def in *.
    intros.
    inversion X1; subst.
    eapply H0 in X3.
    assumption.
  - intros.
    unfold UniETyping_def in *.
    intros.
    inversion X1; subst.
    assert (FT pt t = FT pt0 t0).
    eapply UniIdFTyping.
    exact i.
    assumption.
    inversion H1; subst.
    reflexivity.
  - intros.
    unfold UniETyping_def, UniPTyping_def in *.
    intros.
    inversion X1; subst.
    assert (FT pt t = FT pt0 t0).
    eapply UniIdFTyping.
    exact i.
    assumption.
    inversion H0; subst.
    reflexivity.
  - intros.
    unfold UniETyping_def, UniPTyping_def in *.
    intros.
    inversion X1; subst.
    reflexivity.
  - intros.
    unfold UniETyping_def, UniPTyping_def in *.
    intros.
    inversion X1; subst.
    reflexivity.
  - intros.
    unfold UniETyping_def, UniPTyping_def in *.
    intros.
    inversion X1; subst.  
    eapply H in X2.
    eapply H0 in X3.
    inversion X3; subst.
    reflexivity.
  - exact X.
  - exact X0.
Defined.    

Lemma UniPTyping :
  forall (ftenv: funTC) (tenv: valTC)
         (ps: Prms) (pt1: PTyp),   
      PrmsTyping ftenv tenv ps pt1 -> 
      forall (pt2: PTyp), 
         PrmsTyping ftenv tenv ps pt2 -> 
         pt1 = pt2.
Proof.
  intros.
  eapply UniType_PrmsTyping_mut.
  - intros.
    unfold UniETyping_def.
    intros.
    inversion X1; subst.
    eapply UniVTyping.
    exact v0.
    assumption.
  - intros.
    unfold UniETyping_def.
    intros.
    inversion X1; subst.
    eapply UniIdTyping.
    exact i.
    assumption.
  - intros.
    unfold UniETyping_def in *.
    intros.
    inversion X1; subst.
    eapply H0 in X3.
    exact X3.
  - intros.
    unfold UniETyping_def in *.
    intros.
    inversion X1; subst.
    inversion m0; subst.
    + inversion X2; subst.
      eapply H0 in X4.
      exact X4.
    + eapply H in X3.
      rewrite <- X3 in X4.
      eapply H0 in X4.
      exact X4.
  - intros.
    unfold UniETyping_def in *.
    intros.
    inversion X1; subst.
    assert (tenv1 = tenv4).
    eapply UniEnvTyping.
    exact e0.
    assumption.
    rewrite <- H0 in X2.
    eapply H in X2.
    assumption.
  - intros.
    unfold UniETyping_def in *.
    intros.
    inversion X1; subst.
    eapply H0 in X3.
    assumption.
  - intros.
    unfold UniETyping_def in *.
    intros.
    inversion X1; subst.
    assert (FT pt t = FT pt0 t2).
    eapply UniIdFTyping.
    exact i.
    assumption.
    inversion H1; subst.
    reflexivity.
  - intros.
    unfold UniETyping_def, UniPTyping_def in *.
    intros.
    inversion X1; subst.
    assert (FT pt t = FT pt0 t2).
    eapply UniIdFTyping.
    exact i.
    assumption.
    inversion H0; subst.
    reflexivity.
  - intros.
    unfold UniETyping_def, UniPTyping_def in *.
    intros.
    inversion X1; subst.
    reflexivity.
  - intros.
    unfold UniETyping_def, UniPTyping_def in *.
    intros.
    inversion X1; subst.
    reflexivity.
  - intros.
    unfold UniETyping_def, UniPTyping_def in *.
    intros.
    inversion X1; subst.  
    eapply H in X2.
    eapply H0 in X3.
    inversion X3; subst.
    reflexivity.
  - exact X.
  - exact X0.
Defined.    


End UniqueTyp.

