
Require Export Basics.
Require Export EnvLibA.
Require Export RelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Import IdModTypeA.
Require Import StaticSemA.
Require Import TRInductA.
Require Import WeakenA.
Require Import TSoundnessA.
Require Import IdModTypeA.
Require Import DetermA.
Require Import WeakenA.
Require Import AbbrevA.

Import ListNotations.

Module Invert (IdT: IdModType) <: IdModType.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module AbbrevI := Abbrev IdT.
Export AbbrevI.


(** inverse big-step lemmas (using modules up to Weaken) *)


Lemma BindN_BStep1 (fenv: funEnv) (env: valEnv)
      (e1 e2: Exp) (v: Value) (s s': W) : 
  (forall (e:Exp) (s: W), sigT (fun v: Value =>
                 sigT (fun s': W => 
      EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v))))) ->
  (forall (e:Exp) (s s1 s2: W) (v1 v2: Value), 
      EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
      EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) -> 
        (s1 = s2) /\ (v1 = v2)) ->
  EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s' (Val v)) ->
  (sigT2 (fun s1 : W =>
            (sigT (fun v1: Value =>
                     EClosure fenv env (Conf Exp s e1) (Conf Exp s1 (Val v1)))))
         (fun s1 : W =>
            EClosure fenv env (Conf Exp s1 e2) (Conf Exp s' (Val v)))).
  intros X K.
  intros.
  generalize X.
  intro X1.
  specialize (X e1 s).
  destruct X as [v1 X].
  destruct X as [s1 X].
  specialize (X1 e2 s1).  
  destruct X1 as [v2 X1].
  destruct X1 as [s2 X1].

  generalize X.
  intro K1.
  eapply BindN_extended_congruence in X.
  instantiate (1:=e2) in X.
  
  assert (EStep fenv env (Conf Exp s1 (BindN (Val v1) e2)) (Conf Exp s1 e2)).
  constructor.
  eapply StepIsEClos in X2.
  
  assert (EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s1 e2)).
  eapply EClosConcat.
  exact X.
  assumption.  

  assert (EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X3.
  assumption.

  assert (s' = s2 /\ v = v2).
  eapply K.
  eauto.
  assumption.
  destruct H.
  subst.

  econstructor.
  econstructor.  
  eauto. 
  auto.
Defined.
  

Lemma BindN_BStep2 (fenv: funEnv) (env: valEnv)
      (e1 e2: Exp) (v: Value) (s s': W) : 
  (forall (e:Exp) (s: W), sigT (fun v: Value =>
                 sigT (fun s': W => 
      EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v))))) ->
  (forall (e:Exp) (s s1 s2: W) (v1 v2: Value), 
      EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
      EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) -> 
        (s1 = s2) /\ (v1 = v2)) ->
  EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s' (Val v)) ->
  forall (s1 : W) (v1: Value),
    EClosure fenv env (Conf Exp s e1) (Conf Exp s1 (Val v1)) ->
    EClosure fenv env (Conf Exp s1 e2) (Conf Exp s' (Val v)).
  intros.
  generalize X1.
  intro X2.
  eapply BindN_extended_congruence in X1.
  instantiate (1:= e2) in X1.

  assert (EStep fenv env (Conf Exp s1 (BindN (Val v1) e2)) (Conf Exp s1 e2)).
  constructor.
  eapply StepIsEClos in X3.
  assert (EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s1 e2)).
  eapply EClosConcat.
  exact X1.
  auto.
  specialize (X e2 s1).
  destruct X as [v2 X].
  destruct X as [s2 X].
  assert (EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X4.
  auto.
  assert (s' = s2 /\ v = v2).
  eapply H.
  exact X0.
  auto.
  destruct H0.
  subst.
  auto.
Defined.



Lemma BindS_BStep1 (fenv: funEnv) (env: valEnv)
      (e1 e2: Exp) (x: Id) (v: Value) (s s': W) : 
  (forall (fenv: funEnv) (env: valEnv) (e:Exp) (s: W), sigT (fun v: Value =>
                 sigT (fun s': W => 
      EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v))))) ->
  (forall (e:Exp) (s s1 s2: W) (v1 v2: Value), 
      EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
      EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) -> 
        (s1 = s2) /\ (v1 = v2)) ->
  EClosure fenv env (Conf Exp s (BindS x e1 e2)) (Conf Exp s' (Val v)) ->
  sigT (fun s1 : W =>
     (sigT2 (fun v1: Value =>
        EClosure fenv env (Conf Exp s e1) (Conf Exp s1 (Val v1)))
              (fun v1 : Value =>
        EClosure fenv ((x,v1)::env) (Conf Exp s1 e2) (Conf Exp s' (Val v))))).
  intros X K.
  intros.
  generalize X.
  intro X1.
  specialize (X fenv env e1 s).
  destruct X as [v1 X].
  destruct X as [s1 X].
  generalize X.
  intro K1.
  eapply BindS_extended_congruence in X.
  instantiate (1:=e2) in X.
  instantiate (1:=x) in X.
  
  assert (EStep fenv env (Conf Exp s1 (BindS x (Val v1) e2))
                         (Conf Exp s1 (BindMS emptyE [(x,v1)] e2))).
  constructor.
  eapply StepIsEClos in X2.
  
  assert (EClosure fenv env (Conf Exp s (BindS x e1 e2))
                            (Conf Exp s1 (BindMS emptyE [(x,v1)] e2))).
  eapply EClosConcat.
  exact X.
  assumption.  

  specialize (X1 fenv ((x,v1)::env) e2 s1).  
  destruct X1 as [v2 X1].
  destruct X1 as [s2 X1].

  assert (EClosure fenv env (Conf Exp s (BindS x e1 e2))
                            (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X3.

  assert (EClosure fenv env (Conf Exp s1 (BindMS emptyE [(x, v1)] e2))
                            (Conf Exp s2 (BindMS emptyE [(x, v1)] (Val v2)))).
  eapply BindMS_extended_congruence.
  reflexivity.
  reflexivity.
  assumption.
  
  eapply EClosConcat.
  exact X4.
  eapply StepIsEClos.
  constructor.
  
  assert (s' = s2 /\ v = v2).
  eapply K.
  eauto.
  assumption.
  destruct H.
  subst.

  econstructor.
  econstructor.  
  eauto. 
  auto.
Defined.



Lemma Apply_BStep1 (fenv: funEnv) (env: valEnv)
      (f: Fun) (es: list Exp) (v: Value) (s s': W) : 
  (forall (fenv: funEnv) (env: valEnv) (e:Exp) (s: W), sigT (fun v: Value =>
                 sigT (fun s': W => 
      EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v))))) ->
  (forall (fenv: funEnv) (env: valEnv) (es:list Exp) (s: W),
      sigT (fun vs: list Value =>
                 sigT (fun s': W => 
      PrmsClosure fenv env (Conf Prms s (PS es))
                           (Conf Prms s' (PS (map Val vs)))))) ->
   (forall (e:Exp) (s s1 s2: W) (v1 v2: Value), 
      EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
      EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) -> 
        (s1 = s2) /\ (v1 = v2)) ->

   match f as f with
    | FC fenv' tenv' e0 e1 x n =>
  length tenv' = length es ->     
  EClosure fenv env (Conf Exp s (Apply (QF f) (PS es)))
                                (Conf Exp s' (Val v)) ->
  sigT (fun s1 : W =>
     (sigT2 (fun vs: list Value =>
               PrmsClosure fenv env (Conf Prms s (PS es))
                                    (Conf Prms s1 (PS (map Val vs))))
            (fun vs : list Value =>
    match n with
    | 0 =>   
      EClosure fenv' (mkVEnv tenv' vs) (Conf Exp s1 e0)
                                       (Conf Exp s' (Val v))
    | S n' =>
      EClosure ((x, FC fenv' tenv' e0 e1 x n') :: fenv')
         (mkVEnv tenv' vs) (Conf Exp s1 e1) (Conf Exp s' (Val v))
    end)))
   end.

Proof.  
  intros P1 P2 P3.
  destruct f.
  intros.

  generalize P2.
  intro P0.
  specialize (P0 fenv env es s).
  destruct P0 as [vs P0].
  destruct P0 as [s1 P0].
  generalize P0. 
  intro X0.
  eapply Apply1_extended_congruence with (f:=(FC fenv0 tenv e0 e1 x n)) in X0.
  
  econstructor.
  instantiate (1:=s1). 

  generalize P0.
  intro P6.
  eapply PrmsClos_aux0 in P6.
  rewrite map_length with (f:=Val) in P6.
  rewrite P6 in H.
  clear P6.

  econstructor.
  instantiate (1:=vs).
  exact P0.
  
  destruct n.
(**)
  generalize P1.
  intro P5.
  specialize (P5 fenv0 (mkVEnv tenv vs) e0 s1).
  destruct P5 as [v2 P5].
  destruct P5 as [s2 P5].
  
  assert (EClosure fenv env (Conf Exp s1
            (Apply (QF (FC fenv0 tenv e0 e1 x 0)) (PS (map Val vs))))
                   (Conf Exp s1 (BindMS fenv0 (mkVEnv tenv vs) e0))).             eapply StepIsEClos.
  econstructor.
  econstructor.
  reflexivity.
  exact H.
  reflexivity.

  assert (EClosure fenv env (Conf Exp s1 (BindMS fenv0 (mkVEnv tenv vs) e0))
                       (Conf Exp s2 (BindMS fenv0 (mkVEnv tenv vs) (Val v2)))).
  eapply BindMS_extended_congruence.
  reflexivity.
  reflexivity.
  eapply weaken.
  exact P5.

  assert (EClosure fenv env
                   (Conf Exp s2 (BindMS fenv0 (mkVEnv tenv vs) (Val v2)))
                   (Conf Exp s2 (Val v2))).
  eapply StepIsEClos.
  econstructor.

  assert (EClosure fenv env
        (Conf Exp s (Apply (QF (FC fenv0 tenv e0 e1 x 0)) (PS es)))
        (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X0.
  eapply EClosConcat.
  exact X1.  
  eapply EClosConcat.
  exact X2.
  exact X3.

  assert (s' = s2 /\ v = v2).
  eapply P3.
  exact X.
  exact X4.

  destruct H0. 
  subst.
  exact P5.
(**)
 
  generalize P1.
  intro P5.
  set ((x, FC fenv0 tenv e0 e1 x n) :: fenv0) as fenv'.
  
  specialize (P5 fenv' (mkVEnv tenv vs) e1 s1).
  destruct P5 as [v2 P5].
  destruct P5 as [s2 P5].
  
  assert (EClosure fenv env (Conf Exp s1
            (Apply (QF (FC fenv0 tenv e0 e1 x (S n))) (PS (map Val vs))))
                   (Conf Exp s1
                         (BindMS fenv' (mkVEnv tenv vs) e1))).
  eapply StepIsEClos.
  econstructor.
  econstructor.
  reflexivity.
  exact H.
  reflexivity.

  assert (EClosure fenv env (Conf Exp s1 (BindMS fenv' (mkVEnv tenv vs) e1))
                       (Conf Exp s2 (BindMS fenv' (mkVEnv tenv vs) (Val v2)))).
  eapply BindMS_extended_congruence.
  reflexivity.
  reflexivity.
  eapply weaken.
  exact P5.

  assert (EClosure fenv env
                   (Conf Exp s2 (BindMS fenv' (mkVEnv tenv vs) (Val v2)))
                   (Conf Exp s2 (Val v2))).
  eapply StepIsEClos.
  econstructor.

  assert (EClosure fenv env
        (Conf Exp s (Apply (QF (FC fenv0 tenv e0 e1 x (S n))) (PS es)))
        (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X0.
  eapply EClosConcat.
  exact X1.  
  eapply EClosConcat.
  exact X2.
  exact X3.

  assert (s' = s2 /\ v = v2).
  eapply P3.
  exact X.
  exact X4.

  destruct H0. 
  subst.
  exact P5.
Defined.

(*********************************************************************)

(** further inverse big-step lemmas *)


Lemma BindN_BStepT1 (ftenv: funTC) (tenv: valTC)
      (fenv: funEnv) (env: valEnv) 
      (e1 e2: Exp) (v: Value) (s s': W)
      (k1: FEnvTyping fenv ftenv)
      (k2: EnvTyping env tenv) (t: VTyp)
      (k3: ExpTyping ftenv tenv fenv (BindN e1 e2) t) :
  EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s' (Val v)) ->
  (sigT2 (fun s1 : W =>
            (sigT (fun v1: Value =>
                     EClosure fenv env (Conf Exp s e1) (Conf Exp s1 (Val v1)))))
         (fun s1 : W =>
            EClosure fenv env (Conf Exp s1 e2) (Conf Exp s' (Val v)))).
  intros.
  inversion k3; subst.
  rename X0 into Y1.
  rename X1 into Y2.
  rename t into t2.
  
  assert (ExpSoundness ftenv tenv fenv e1 t1 Y1) as X1.
  eapply (ExpEval ftenv tenv fenv e1 t1 Y1).
  unfold ExpSoundness in X1.
  unfold SoundExp in X1.
  specialize (X1 k1 env k2 s).
  destruct X1 as [v1 k4 X1].
  destruct X1 as [s1 X1].

  generalize X1.
  intro.

  assert (ExpSoundness ftenv tenv fenv e2 t2 Y2) as X2.
  eapply (ExpEval ftenv tenv fenv e2 t2 Y2).
  unfold ExpSoundness in X2.
  unfold SoundExp in X2.
  specialize (X2 k1 env k2 s1).
  destruct X2 as [v2 k5 X2].
  destruct X2 as [s2 X2].
  
  eapply BindN_extended_congruence in X1.
  instantiate (1:=e2) in X1.
  
  assert (EStep fenv env (Conf Exp s1 (BindN (Val v1) e2)) (Conf Exp s1 e2)).
  constructor.
  eapply StepIsEClos in X3.
  
  assert (EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s1 e2)).
  eapply EClosConcat.
  exact X1.
  assumption.  

  assert (EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X4.
  assumption.

  assert (s' = s2 /\ v = v2).
  eapply ExpConfluence. 
  exact k3.
  auto.
  eauto.
  eauto.
  auto.

  destruct H.
  subst.

  econstructor.
  econstructor.  
  eauto. 
  auto.
Defined.


Lemma BindS_BStepT1 (ftenv: funTC) (tenv: valTC)
      (fenv: funEnv) (env: valEnv) 
      (e1 e2: Exp) (x: Id) (v: Value) (s s': W)
      (k1: FEnvTyping fenv ftenv)
      (k2: EnvTyping env tenv) (t: VTyp)
      (k3: ExpTyping ftenv tenv fenv (BindS x e1 e2) t) :
  EClosure fenv env (Conf Exp s (BindS x e1 e2)) (Conf Exp s' (Val v)) ->
  sigT (fun s1 : W =>
     (sigT2 (fun v1: Value =>
        EClosure fenv env (Conf Exp s e1) (Conf Exp s1 (Val v1)))
              (fun v1 : Value =>
        EClosure fenv ((x,v1)::env) (Conf Exp s1 e2) (Conf Exp s' (Val v))))).
  intros.
  inversion k3; subst.
  rename X0 into Y1.
  rename X1 into Y2.
  rename t into t2.
  
  assert (ExpSoundness ftenv tenv fenv e1 t1 Y1) as X1.
  eapply (ExpEval ftenv tenv fenv e1 t1 Y1).
  unfold ExpSoundness in X1.
  unfold SoundExp in X1.
  specialize (X1 k1 env k2 s).
  destruct X1 as [v1 k4 X1].
  destruct X1 as [s1 X1].

  generalize X1.
  intro.

  eapply BindS_extended_congruence in X1.
  instantiate (1:=e2) in X1.
  instantiate (1:=x) in X1.
  
  assert (EStep fenv env (Conf Exp s1 (BindS x (Val v1) e2))
                         (Conf Exp s1 (BindMS emptyE [(x,v1)] e2))).
  constructor.
  eapply StepIsEClos in X2.
  
  assert (EClosure fenv env (Conf Exp s (BindS x e1 e2))
                            (Conf Exp s1 (BindMS emptyE [(x,v1)] e2))).
  eapply EClosConcat.
  exact X1.
  assumption.  

  assert (ExpSoundness ftenv tenv' fenv e2 t2 Y2) as X4.
  eapply (ExpEval ftenv tenv' fenv e2 t2 Y2).
  unfold ExpSoundness in X4.
  unfold SoundExp in X4.

  assert (MatchEnvsT ValueTyping ((x, v1) :: env) tenv').
  econstructor.
  auto.
  auto.
  specialize (X4 k1 ((x,v1)::env) X5 s1).
  destruct X4 as [v2 k5 X4].
  destruct X4 as [s2 X4].

  assert (EClosure fenv env (Conf Exp s (BindS x e1 e2))
                            (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X3.

  assert (EClosure fenv env (Conf Exp s1 (BindMS emptyE [(x, v1)] e2))
                            (Conf Exp s2 (BindMS emptyE [(x, v1)] (Val v2)))).
  eapply BindMS_extended_congruence.
  reflexivity.
  reflexivity.
  assumption.
  
  eapply EClosConcat.
  exact X6.
  eapply StepIsEClos.
  constructor.
  
  assert (s' = s2 /\ v = v2).
  eapply ExpConfluence. 
  exact k3.
  auto.
  eauto.
  eauto.
  auto.
  
  destruct H.
  subst.

  econstructor.
  econstructor.  
  eauto. 
  auto.
Defined.


Lemma Apply_BStepT1 (ftenv: funTC) (tenv: valTC)
      (fenv: funEnv) (env: valEnv)
      (f: Fun) (es: list Exp) (v: Value) (s s': W) 
      (k1: FEnvTyping fenv ftenv)
      (k2: EnvTyping env tenv) (t: VTyp)
      (k3: ExpTyping ftenv tenv fenv (Apply (QF f) (PS es)) t) :
   match f as f with
    | FC fenv' tenv' e0 e1 x n =>
  length tenv' = length es ->     
  EClosure fenv env (Conf Exp s (Apply (QF f) (PS es)))
                                (Conf Exp s' (Val v)) ->
  sigT (fun s1 : W =>
     (sigT2 (fun vs: list Value =>
               PrmsClosure fenv env (Conf Prms s (PS es))
                                    (Conf Prms s1 (PS (map Val vs))))
            (fun vs : list Value =>
    match n with
    | 0 =>   
      EClosure fenv' (mkVEnv tenv' vs) (Conf Exp s1 e0)
                                       (Conf Exp s' (Val v))
    | S n' =>
      EClosure ((x, FC fenv' tenv' e0 e1 x n') :: fenv')
         (mkVEnv tenv' vs) (Conf Exp s1 e1) (Conf Exp s' (Val v))
    end)))
   end.

Proof.
  destruct f.
  intros.
  inversion k3; subst.
  rename X1 into Y2.
  rename X2 into Y1.
  
  assert (PrmsSoundness ftenv tenv fenv (PS es) (PT (map snd fps)) Y1) as X1.
  eapply (PrmsEval ftenv tenv fenv (PS es) (PT (map snd fps)) Y1).
  unfold PrmsSoundness in X1.
  unfold SoundPrms in X1.
  specialize (X1 k1 env k2 s).
  destruct X1 as [es1 X1].
  destruct X1 as [vs k4 X1].
  destruct X1 as [k5 X1].
  destruct X1 as [s1 X1].
  
  generalize X1.
  intro.

  eapply Apply1_extended_congruence with (f:=(FC fenv0 tenv0 e0 e1 x n)) in X1.
  
  econstructor.
  instantiate (1:=s1). 

  generalize X2.
  intro P6.
  eapply PrmsClos_aux0 in P6.
  inversion k4; subst.
  
  rewrite map_length with (f:=Val) in P6.
  rewrite P6 in H.
  clear P6.

  econstructor.
  instantiate (1:=vs).
  auto.
  
  destruct n.
  (**)
  inversion Y2; subst.
  inversion X3; subst.
  
  assert (ExpSoundness ftenv0 fps fenv0 e0 t X5) as X6.
  eapply (ExpEval ftenv0 fps fenv0 e0 t X5).
  unfold ExpSoundness in X6.
  unfold SoundExp in X6.

  assert (MatchEnvsT ValueTyping (mkVEnv fps vs) fps).
  eapply prmsTypingAux_T.
  auto.
  eapply matchListsAux02_T.
  eauto.
  eauto.
  
  specialize (X6 X4 (mkVEnv fps vs) X7 s1).
  destruct X6 as [v2 k7 P5].
  destruct P5 as [s2 P5].
  
  assert (EClosure fenv env (Conf Exp s1
            (Apply (QF (FC fenv0 fps e0 e1 x 0)) (PS (map Val vs))))
                   (Conf Exp s1 (BindMS fenv0 (mkVEnv fps vs) e0))) as A1.        eapply StepIsEClos.
  econstructor.
  econstructor.
  reflexivity.
  exact H.
  reflexivity.

  assert (EClosure fenv env (Conf Exp s1 (BindMS fenv0 (mkVEnv fps vs) e0))
                 (Conf Exp s2 (BindMS fenv0 (mkVEnv fps vs) (Val v2)))) as A2.
  eapply BindMS_extended_congruence.
  reflexivity.
  reflexivity.
  eapply weaken.
  exact P5.

  assert (EClosure fenv env
                   (Conf Exp s2 (BindMS fenv0 (mkVEnv fps vs) (Val v2)))
                   (Conf Exp s2 (Val v2))) as A3.
  eapply StepIsEClos.
  econstructor.

  assert (EClosure fenv env
        (Conf Exp s (Apply (QF (FC fenv0 fps e0 e1 x 0)) (PS es)))
        (Conf Exp s2 (Val v2))) as A4.
  eapply EClosConcat.
  exact X1.
  eapply EClosConcat.
  exact A1.  
  eapply EClosConcat.
  exact A2.
  exact A3.

  assert (s' = s2 /\ v = v2).
  eapply ExpConfluence.
  exact k3.
  auto.
  eauto.
  eauto.
  auto.

  destruct H0. 
  subst.
  exact P5.
(**)
  
  inversion Y2; subst.
  inversion X3; subst.
  
  assert (ExpSoundness ftenv' fps fenv' e1 t X5) as X06.
  eapply (ExpEval ftenv' fps fenv' e1 t X5).
  unfold ExpSoundness in X06.
  unfold SoundExp in X06.

  assert (MatchEnvsT ValueTyping (mkVEnv fps vs) fps).
  eapply prmsTypingAux_T.
  auto.
  eapply matchListsAux02_T.
  eauto.
  eauto.

  assert (MatchEnvsT FunTyping fenv' ftenv').
  econstructor.
  auto.
  auto.
  
  specialize (X06 X8 (mkVEnv fps vs) X7 s1).
  destruct X06 as [v2 k7 P5].
  destruct P5 as [s2 P5].
  
  assert (EClosure fenv env (Conf Exp s1
            (Apply (QF (FC fenv0 fps e0 e1 x (S n))) (PS (map Val vs))))
                   (Conf Exp s1 (BindMS fenv' (mkVEnv fps vs) e1))) as A1.        eapply StepIsEClos.
  econstructor.
  econstructor.
  reflexivity.
  exact H.
  reflexivity.

  assert (EClosure fenv env (Conf Exp s1 (BindMS fenv' (mkVEnv fps vs) e1))
                 (Conf Exp s2 (BindMS fenv' (mkVEnv fps vs) (Val v2)))) as A2.
  eapply BindMS_extended_congruence.
  reflexivity.
  reflexivity.
  eapply weaken.
  exact P5.

  assert (EClosure fenv env
                   (Conf Exp s2 (BindMS fenv' (mkVEnv fps vs) (Val v2)))
                   (Conf Exp s2 (Val v2))) as A3.
  eapply StepIsEClos.
  econstructor.

  assert (EClosure fenv env
        (Conf Exp s (Apply (QF (FC fenv0 fps e0 e1 x (S n))) (PS es)))
        (Conf Exp s2 (Val v2))) as A4.
  eapply EClosConcat.
  exact X1.
  eapply EClosConcat.
  exact A1.  
  eapply EClosConcat.
  exact A2.
  exact A3.

  assert (s' = s2 /\ v = v2).
  eapply ExpConfluence.
  exact k3.
  auto.
  eauto.
  eauto.
  auto.

  destruct H0. 
  subst.
  exact P5.
Defined.



Lemma Prms_BStepT1 (ftenv: funTC) (tenv: valTC)
      (fenv: funEnv) (env: valEnv) 
      (e: Exp) (es: list Exp) (v: Value) (vs: list Value) (s s': W)
      (k1: FEnvTyping fenv ftenv)
      (k2: EnvTyping env tenv) (pt: PTyp)
      (k3: PrmsTyping ftenv tenv fenv (PS (e::es)) pt) :
  PrmsClosure fenv env (Conf Prms s (PS (e::es)))
                       (Conf Prms s' (PS (map Val (v::vs)))) ->
  (sigT2 (fun s1 : W =>
            (sigT (fun v1: Value =>
                     EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)))))
         (fun s1 : W =>
            PrmsClosure fenv env (Conf Prms s1 (PS es))
                                 (Conf Prms s' (PS (map Val vs))))).
  intros.
  inversion k3; subst.
  inversion X0; subst.
  rename X1 into Y1.
  rename X2 into Y3.
  rename y into t.
  rename l' into ts.
  
  assert (ExpSoundness ftenv tenv fenv e t Y1) as X1.
  eapply (ExpEval ftenv tenv fenv e t Y1).
  unfold ExpSoundness in X1.
  unfold SoundExp in X1.
  specialize (X1 k1 env k2 s).
  destruct X1 as [v1 k4 X1].
  destruct X1 as [s1 X1].

  generalize X1.
  intro Y4.

  assert (PrmsTyping ftenv tenv fenv (PS es) (PT ts)) as Y2.
  constructor.
  auto.
  
  assert (PrmsSoundness ftenv tenv fenv (PS es) (PT ts) Y2) as X2.
  eapply (PrmsEval ftenv tenv fenv (PS es) (PT ts) Y2).
  unfold PrmsSoundness in X2.
  unfold SoundPrms in X2.
  specialize (X2 k1 env k2 s1).
  destruct X2 as [es1 X2].
  destruct X2 as [vs1 Y5 X2].
  destruct X2 as [Y6 X2].
  destruct X2 as [s2 X2].

  inversion Y5; subst.

(**)
  assert (PrmsClosure fenv env (Conf Prms s (PS (e :: es)))
        (Conf Prms s2 (PS (map Val (v1 :: vs1))))).
  eapply Pars_extended_congruence4.
  eauto.
  exact X2.
  
  constructor 1 with (x:=s1).
  constructor 1 with (x:=v1).
  exact X1.

  assert (s' = s2 /\ vs = vs1).
  eapply PrmsConfluence in X.
  specialize (X X3).
  destruct X.
  split.
  exact H.
  inversion H0; subst.
  auto.
  eauto.
  auto.
  auto.
  destruct H.
  rewrite H.
  rewrite H0.
  auto.
Defined.  



Lemma Prms_BStepT2 (ftenv: funTC) (tenv: valTC)
      (fenv: funEnv) (env: valEnv) 
      (e: Exp) (es: list Exp) (v: Value) (vs: list Value) (s s': W)
      (k1: FEnvTyping fenv ftenv)
      (k2: EnvTyping env tenv) (pt: PTyp)
      (k3: PrmsTyping ftenv tenv fenv (PS (e::es)) pt) :
  PrmsClosure fenv env (Conf Prms s (PS (e::es)))
                       (Conf Prms s' (PS (map Val (v::vs)))) ->
  (sigT2 (fun s1 : W =>
            (EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v))))
         (fun s1 : W =>
            PrmsClosure fenv env (Conf Prms s1 (PS es))
                                 (Conf Prms s' (PS (map Val vs))))).
  intros.
  inversion k3; subst.
  inversion X0; subst.
  rename X1 into Y1.
  rename X2 into Y3.
  rename y into t.
  rename l' into ts.
  
  assert (ExpSoundness ftenv tenv fenv e t Y1) as X1.
  eapply (ExpEval ftenv tenv fenv e t Y1).
  unfold ExpSoundness in X1.
  unfold SoundExp in X1.
  specialize (X1 k1 env k2 s).
  destruct X1 as [v1 k4 X1].
  destruct X1 as [s1 X1].
 
(*
  generalize X1.
  intro Y4.
*)
  assert (PrmsTyping ftenv tenv fenv (PS es) (PT ts)) as Y2.
  constructor.
  auto.
  
  assert (PrmsSoundness ftenv tenv fenv (PS es) (PT ts) Y2) as X2.
  eapply (PrmsEval ftenv tenv fenv (PS es) (PT ts) Y2).
  unfold PrmsSoundness in X2.
  unfold SoundPrms in X2.
  specialize (X2 k1 env k2 s1).
  
  destruct X2 as [es1 X2].
  destruct X2 as [vs1 Y5 X2].
  destruct X2 as [Y6 X2].
  destruct X2 as [s2 X2].
  inversion Y5; subst.

  assert (PrmsClosure fenv env (Conf Prms s (PS (e :: es)))
        (Conf Prms s2 (PS (map Val (v1 :: vs1))))).
  eapply Pars_extended_congruence4.
  eauto.
  exact X2.
  
  
  (**)
  assert (s' = s2 /\ (v::vs) = (v1::vs1)).
  eapply PrmsConfluence in X.
  specialize (X X3).
  exact X.

  eauto.
  auto.
  auto.
  destruct H.
  injection H0.
  intros.
  
  constructor 1 with (x:=s1).
  rewrite H2.
  auto.
  rewrite H.
  rewrite H1.
  auto.
Defined.  


Lemma IfThenElse_BStepT1 (ftenv: funTC) (tenv: valTC)
      (fenv: funEnv) (env: valEnv) 
      (e1 e2 e3: Exp) (v: Value) (s s': W)
      (k1: FEnvTyping fenv ftenv)
      (k2: EnvTyping env tenv) (t: VTyp)
      (k3: ExpTyping ftenv tenv fenv (IfThenElse e1 e2 e3) t) :
  EClosure fenv env (Conf Exp s (IfThenElse e1 e2 e3)) (Conf Exp s' (Val v)) ->
  sum (sigT2 (fun s1 : W =>
        EClosure fenv env (Conf Exp s e1) (Conf Exp s1 (Val (cst bool true))))           (fun s1 : W =>
             (EClosure fenv env (Conf Exp s1 e2) (Conf Exp s' (Val v)))))
      (sigT2 (fun s1 : W =>
      EClosure fenv env (Conf Exp s e1) (Conf Exp s1 (Val (cst bool false))))           (fun s1 : W => 
             (EClosure fenv env (Conf Exp s1 e3) (Conf Exp s' (Val v))))).
Proof.
  intros.
  inversion k3; subst.
  
  assert (ExpSoundness ftenv tenv fenv e1 Bool X0) as Y1.
  eapply (ExpEval ftenv tenv fenv e1 Bool X0).
  unfold ExpSoundness in Y1.
  unfold SoundExp in Y1.
  specialize (Y1 k1 env k2 s).

  assert (ExpSoundness ftenv tenv fenv e2 t X1) as Y2.
  eapply (ExpEval ftenv tenv fenv e2 t X1).
  unfold ExpSoundness in Y2.
  unfold SoundExp in Y2.
  specialize (Y2 k1 env k2).

  assert (ExpSoundness ftenv tenv fenv e3 t X2) as Y3.
  eapply (ExpEval ftenv tenv fenv e3 t X2).
  unfold ExpSoundness in Y3.
  unfold SoundExp in Y3.
  specialize (Y3 k1 env k2).

  destruct Y1 as [v1 H1 Y1].
  destruct Y1 as [s1 Y1].
  specialize (Y2 s1).
  specialize (Y3 s1).
  destruct v1.
  destruct v0. 
  inversion H1; subst.
  simpl in *.
  subst T.
  inversion H; subst.
  clear H2.

  destruct v0.

(**)
  destruct Y2 as [v2 H2 Y2].
  destruct Y2 as [s2 Y2].
  
  assert (EClosure fenv env (Conf Exp s (IfThenElse e1 e2 e3))
                   (Conf Exp s2 (Val v2))).  
  eapply EClosConcat.
  eapply IfThenElse_extended_congruence.
  exact Y1.
  econstructor.
  econstructor.
  exact Y2.

  assert (s' = s2 /\ v = v2).
  eapply (ExpConfluence ftenv tenv fenv (IfThenElse e1 e2 e3) t k3).
  auto.
  eauto.
  exact X.
  auto.
  destruct H.

  constructor.
  econstructor 1 with (x:=s1).
  auto.
  rewrite H.
  rewrite H3.
  exact Y2.

(**)
  clear Y2.
  rename Y3 into Y2.
  destruct Y2 as [v2 H2 Y2].
  destruct Y2 as [s2 Y2].
  
  assert (EClosure fenv env (Conf Exp s (IfThenElse e1 e2 e3))
                   (Conf Exp s2 (Val v2))).  
  eapply EClosConcat.
  eapply IfThenElse_extended_congruence.
  exact Y1.
  econstructor.
  econstructor.
  exact Y2.

  assert (s' = s2 /\ v = v2).
  eapply (ExpConfluence ftenv tenv fenv (IfThenElse e1 e2 e3) t k3).
  auto.
  eauto.
  exact X.
  auto.
  destruct H.

  constructor 2.
  econstructor 1 with (x:=s1).
  auto.
  rewrite H.
  rewrite H3.
  exact Y2.
Qed.
  


Lemma Apply_BStepT2
      (ftenv: funTC) (tenv: valTC)
      (fenv: funEnv) (env: valEnv)
      (f: Fun) (es: list Exp) (v: Value) (s s': W) 
      (k1: FEnvTyping fenv ftenv)
      (k2: EnvTyping env tenv) (t: VTyp)
      (k3: ExpTyping ftenv tenv fenv (Apply (QF f) (PS es)) t) :
  EClosure fenv env (Conf Exp s (Apply (QF f) (PS es)))
                                (Conf Exp s' (Val v)) ->
  sigT (fun s1 : W =>
          (sigT2 (fun vs: list Value =>   
               PrmsClosure fenv env (Conf Prms s (PS es))
                                    (Conf Prms s1 (PS (map Val vs))))
            (fun vs : list Value =>
               EClosure fenv env (Conf Exp s1 (Apply (QF f)
                                                  (PS (map Val vs))))
                                 (Conf Exp s' (Val v))))).
Proof.
  intros.
  inversion k3; subst.
  rename X1 into Y2.
  rename X2 into Y1.
  
  assert (PrmsSoundness ftenv tenv fenv (PS es) (PT (map snd fps)) Y1) as X1.
  eapply (PrmsEval ftenv tenv fenv (PS es) (PT (map snd fps)) Y1).
  unfold PrmsSoundness in X1.
  unfold SoundPrms in X1.
  specialize (X1 k1 env k2 s).
  destruct X1 as [es1 X1].
  destruct X1 as [vs k4 X1].
  destruct X1 as [k5 X1].
  destruct X1 as [s1 X1].
   
  generalize X1.
  intro.

  eapply Apply1_extended_congruence with (f:=f) in X1.
  
  econstructor 1 with (x:=s1).
  
  inversion k4; subst.

  econstructor 1 with (x:=vs).
  auto.

  assert (ExpTyping ftenv tenv fenv (Apply (QF f) (PS (map Val vs))) t).
  econstructor.
  reflexivity.
  auto.
  eauto.
  eapply weakenPrmsTyping in k5.
  instantiate (1:=fenv) in k5.
  instantiate (1:=tenv) in k5.
  instantiate (1:=ftenv) in k5.
  simpl in k5.
  auto.
  constructor.
  auto.

  set (Apply (QF f) (PS (map Val vs))) as e.

  assert (ExpSoundness ftenv tenv fenv e t X3) as X6.
  eapply (ExpEval ftenv tenv fenv e t X3).
  unfold ExpSoundness in X6.
  unfold SoundExp in X6.
  specialize (X6 X0 env k2 s1).
  destruct X6 as [v2 H0 X6].
  destruct X6 as [s2 X6].

  assert (EClosure fenv env (Conf Exp s (Apply (QF f) (PS es)))
                   (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X1.
  auto.

  assert (s' = s2 /\ v = v2).
  eapply ExpConfluence.
  exact k3.
  auto.
  eauto.
  eauto.
  auto.
  destruct H.
  rewrite H.
  rewrite H1.
  auto.
Qed.
  

Lemma Apply_BStepT2t
      (ftenv: funTC) (tenv: valTC)
      (fenv: funEnv) (env: valEnv)
      (f: Fun) (es: list Exp) (v: Value) (s s': W) 
      (k1: FEnvTyping fenv ftenv)
      (k2: EnvTyping env tenv) (t: VTyp) (pt: PTyp)
      (k3: ExpTyping ftenv tenv fenv (Apply (QF f) (PS es)) t)
      (k0: PrmsTyping ftenv tenv fenv (PS es) pt) :
  EClosure fenv env (Conf Exp s (Apply (QF f) (PS es)))
                                (Conf Exp s' (Val v)) ->
  sigT (fun s1 : W =>
          (sigT2 (fun vs: list Value =>
               (PrmsTyping ftenv tenv fenv (PS (map Val vs)) pt *       
               PrmsClosure fenv env (Conf Prms s (PS es))
                                    (Conf Prms s1 (PS (map Val vs))))%type)
            (fun vs : list Value =>
               EClosure fenv env (Conf Exp s1 (Apply (QF f)
                                                  (PS (map Val vs))))
                                 (Conf Exp s' (Val v))))).
Proof.
  intros.
  inversion k3; subst.
  rename X1 into Y2.
  rename X2 into Y1.
  
  assert (PrmsSoundness ftenv tenv fenv (PS es) (PT (map snd fps)) Y1) as X1.
  eapply (PrmsEval ftenv tenv fenv (PS es) (PT (map snd fps)) Y1).
  unfold PrmsSoundness in X1.
  unfold SoundPrms in X1.
  specialize (X1 k1 env k2 s).
  destruct X1 as [es1 X1].
  destruct X1 as [vs k4 X1].
  destruct X1 as [k5 X1].
  destruct X1 as [s1 X1].
   
  generalize X1.
  intro.

  eapply Apply1_extended_congruence with (f:=f) in X1.
  
  econstructor 1 with (x:=s1).
  
  inversion k4; subst.

  econstructor 1 with (x:=vs).
  split.
  
  assert (pt = PT (map snd fps)).
  eapply PrmsStrongTyping.
  exact k0.
  auto.
  eauto.
  auto.
  rewrite H.
  auto.

  eapply weakenPrmsTyping in k5.
  instantiate (1:=fenv) in k5.
  instantiate (1:=tenv) in k5.
  instantiate (1:=ftenv) in k5.
  simpl in k5.
  auto.
  constructor.
  auto.

  exact X2.
    
  assert (ExpTyping ftenv tenv fenv (Apply (QF f) (PS (map Val vs))) t).
  econstructor.
  reflexivity.
  auto.
  eauto.
  eapply weakenPrmsTyping in k5.
  instantiate (1:=fenv) in k5.
  instantiate (1:=tenv) in k5.
  instantiate (1:=ftenv) in k5.
  simpl in k5.
  auto.
  constructor.
  auto.

  set (Apply (QF f) (PS (map Val vs))) as e.

  assert (ExpSoundness ftenv tenv fenv e t X3) as X6.
  eapply (ExpEval ftenv tenv fenv e t X3).
  unfold ExpSoundness in X6.
  unfold SoundExp in X6.
  specialize (X6 X0 env k2 s1).
  destruct X6 as [v2 H0 X6].
  destruct X6 as [s2 X6].

  assert (EClosure fenv env (Conf Exp s (Apply (QF f) (PS es)))
                   (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X1.
  auto.

  assert (s' = s2 /\ v = v2).
  eapply ExpConfluence.
  exact k3.
  auto.
  eauto.
  eauto.
  auto.
  destruct H.
  rewrite H.
  rewrite H1.
  auto.
Qed.
  

End Invert.


(*
Lemma BStep_convert 
      (fenv: funEnv) (env: valEnv)
      (e1 e2: Exp) (v: Value) (s s': W) :
  forall P, 
    (forall 
        (w1: forall (fenv: funEnv) (env: valEnv) (e:Exp) (s: W),
             sigT (fun v: Value =>
                 sigT (fun s': W => 
          EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v))))) 
        (w2: forall (e:Exp) (s s1 s2: W) (v1 v2: Value), 
           EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
           EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) -> 
           (s1 = s2) /\ (v1 = v2)),
      P fenv env e1 e2 v s s') ->
    (forall 
        (ftenv: funTC) (tenv: valTC) 
        (k1: FEnvTyping fenv ftenv)
        (k2: EnvTyping env tenv) (t: VTyp)
        (k3: ExpTyping ftenv tenv fenv e1 t),
      P fenv env e1 e2 v s s').
  intros.
  eapply X.
  intros.
  econstructor.
  instantiate (1:= extractRunValue ftenv tenv fenv e1 t k3 k1 env k2 s).
  econstructor.
  instantiate (1:= extractRunState ftenv tenv fenv e1 t k3 k1 env k2 s).
  eapply EvalIntro.
*)  



