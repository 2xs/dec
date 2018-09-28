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
Require Import GenericMinMax.
Require Import NMaxMin.

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
Require Import DetermI1.
Require Import PreReflI1.
Require Import ReflectI1.
Require Import PreInterI1.
Require Import InterprBaseI1.


Import ListNotations.


Module Interpret (IdT: ModTyp) <: ModTyp.

Module InterprBaseL := InterprBase IdT.
Export InterprBaseL.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Open Scope type_scope.

        
Lemma ExpInterp_Val (fenv : funEnv) (k:  FEnvWT fenv) (n: nat) :
      forall (ftenv : funTC) (tenv : valTC) (v : Value) 
    (t : VTyp) (m : VTyping v t),
  PInterpExp fenv k n ftenv tenv (Val v) t (Val_Typing ftenv tenv v t m).
  unfold PInterpExp.
  intros.
  econstructor 1 with (x:=ExpSoundness_Val fenv k n ftenv tenv v t m).

  econstructor 1 with
      (x:= ExpTrans_Val fenv k n ftenv tenv v t m).
  intros.
  simpl.
  unfold ExpTrans_Val.
  destruct v.
  destruct v.
  inversion m; subst.
  simpl.
  unfold VTyping in m.
  dependent destruction m.
  simpl.
  unfold DenExp_ext.
  unfold sValue.
  simpl.
  reflexivity.
Defined.  


Lemma ExpInterp_Var (fenv : funEnv) (k:  FEnvWT fenv) (n: nat) :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (t : VTyp) (i : IdTyping tenv x t),
    PInterpExp fenv k n ftenv tenv (Var x) t (Var_Typing ftenv tenv x t i).
  unfold PInterpExp.
  intros.

  econstructor 1 with (x:=ExpSoundness_Var fenv k n ftenv tenv x t i). 
  
  econstructor 1 with
      (x:= ExpTrans_Var fenv k n ftenv tenv x t i). 

  intros.
  
  inversion m2; subst.
  remember (ExtRelVal2B env x t i) as K.
  inversion K; subst.

  set (t:=valueVTyp x0).
  set (tenv:=(map (thicken StaticSemL.Id valueVTyp) env)).

  unfold ExpSoundness_Var.
  unfold SOS_Exp1.
  simpl.
  unfold ExtRelVal2B_4.

  unfold ValEnv_agree in kk.
  destruct x0 as [t0 v].
  destruct v.
  specialize (kk x t v i H).
    
  unfold EnvTyping in m2.
  unfold MatchEnvs in m2.
  dependent destruction m2.

  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.

  unfold FEnvTyping in m1.
  unfold MatchEnvs in m1.
  dependent destruction m1.

  assert ((v, (s0, n0)) = DenExp_ext t n0
    (ExpTrans_Var fenv k n (map (thicken StaticSemL.Id funFTyp) fenv)
       (map (thicken StaticSemL.Id valueVTyp) env) x0 t i eq_refl senv
       n0 q s0)) as H0.
  
  unfold DenExp_ext.
  simpl.
  rewrite <- kk.
  reflexivity.
  
  subst tenv.
  subst t.
  
  rewrite <- H0 at 1.
  clear H0.

  simpl.
  f_equal.

  set (vv:=existT ValueI t0 (Cst t0 v)).
  assert (v = sValue vv) as xx.
  unfold sValue.
  unfold sValueI.
  simpl.
  reflexivity.

  rewrite xx at 1.

  unfold ExtRelVal2B_1.

  generalize (ExtRelVal2B env x0 t0 i).
  intro.
  
  destruct s.
  destruct x2.
  destruct t0.
  destruct e0.
  simpl in *.

  unfold sValue.
  unfold sValueI.
  unfold proj1_of_sigT2.
  simpl.

  rewrite H in e.
  injection e.
  intro H2.
  eapply inj_pair2 in H2.
  rewrite <- H2.
  reflexivity.
Defined.  
 


Lemma ExpInterp_BindN (fenv : funEnv) (k:  FEnvWT fenv) (n: nat) :
  forall (ftenv : funTC) (tenv : valTC) (e1 e2 : Exp) 
    (t1 t2 : VTyp) (e : ExpTyping ftenv tenv e1 t1),
  PInterpExp fenv k n ftenv tenv e1 t1 e ->
  forall e0 : ExpTyping ftenv tenv e2 t2,
  PInterpExp fenv k n ftenv tenv e2 t2 e0 ->
  PInterpExp fenv k n ftenv tenv (BindN e1 e2) t2
             (BindN_Typing ftenv tenv e1 e2 t1 t2 e e0).
    unfold PInterpExp.
    intros.

    specialize (X m1).
    specialize (X0 m1).
    destruct X as [k4 X].
    destruct X as [k5 X].

    destruct X0 as [k8 X0].
    destruct X0 as [k9 X0].

    econstructor 1 with (x:=ExpSoundness_BindN fenv k n ftenv tenv 
                                           e1 e2 t1 t2 e k4 e0 k8).
    econstructor 1 with (x:=ExpTrans_BindN fenv k n ftenv tenv e1 e2 t1 t2
                                           e k5 e0 k9).

    intros.
    specialize (X s0 n0 q env m2 senv kk).

    unfold ExpSoundness_BindN.
    destruct (k4 m1 env m2 n0 q s0) as [v1 mm1 C1].
    destruct C1 as [w1 C1].
    destruct w1 as [s1 n1].
    simpl in C1.
    simpl in X.
    simpl.

    assert (n1 <= n0) as q01.
    eapply ExpDecrease in C1.
    exact C1.
    assert (n1 <= n) as q1.
    omega.
    
    specialize (X0 s1 n1 q1 env m2 senv kk).

    assert (q1 =  (Nat.le_trans n1 n0 n
                  (ExpDecrease fenv env s0 s1 n0 n1 e1 (Val v1) C1) q)).
    eapply proof_irrelevance.
    rewrite <- H.
        
    destruct (k8 m1 env m2 n1 q1 s1) as [v2 mm2 C2].
    destruct C2 as [w2 C2].
    destruct w2 as [s2 n2].
    simpl in C2.
    simpl in X0.
    simpl.

    unfold ExpTrans_BindN.

    destruct (k5 m1 senv n0 q s0).
    
    unfold DenExp_ext in X.
    simpl in X.
    unfold VTyping in mm1.
    inversion mm1; subst.
    destruct p.
    inversion X; subst.
    simpl.

    destruct s.
    simpl in X0.

    set (q3:=Nat.le_trans x n0 n
                          (ExpDecrease fenv env s0 w n0 x e1 (Val v1) C1) q).
    assert (q3 = Nat.le_trans x n0 n l q).
    eapply proof_irrelevance.
    rewrite <- H.

    subst q3.
    destruct ( (k9 m1 senv x
            (Nat.le_trans x n0 n
               (ExpDecrease fenv env s0 w n0 x e1 (Val v1) C1) q) w)).

    destruct s.
    unfold DenExp_ext in X0.
    unfold VTyping in mm2.
    inversion mm2; subst.
    destruct p.
    inversion X0; subst.

    unfold DenExp_ext.
    simpl.
    reflexivity.
Defined.


Lemma ValEnv_agree_extend (tenv: valTC) (env: valEnv)
          (senv : valTC_Trans tenv)
          (t1: VTyp) (x: Id) (sv1: sVTyp t1) 
          (m2 : EnvTyping env tenv) 
          (kk : ValEnv_agree tenv env m2 senv)
          (X3 : EnvTyping ((x, existT ValueI t1 (Cst t1 sv1)) :: env)
                          ((x, t1) :: tenv)) : 
      ValEnv_agree ((x, t1) :: tenv)
                   ((x, existT ValueI t1 (Cst t1 sv1)) :: env) X3
                   (ext_senv tenv senv x t1 sv1).
  unfold ValEnv_agree in *.
  intros.
  simpl in k1.
  simpl in k2.
  unfold extract_from_valTC_TransB.
  simpl.
  destruct (IdT.IdEqDec x0 x).
  subst.
  inversion k1; subst.
  dependent destruction k1.
  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  simpl.
  inversion k2; subst.
  eapply inj_pair2 in H0.
  subst.
  reflexivity.
  
  specialize (kk x0 t v k1 k2).  
  subst.
  reflexivity.
Defined.  


Lemma ExpInterp_BindS (fenv : funEnv) (k:  FEnvWT fenv) (n: nat) :
  forall (ftenv : funTC) (tenv tenv' : valTC) (x : StaticSemL.Id)
    (e1 e2 : Exp) (t1 t2 : VTyp) (m : option VTyp) 
    (m0 : Maybe t1 m) (e : tenv' = (x, t1) :: tenv)
    (e0 : ExpTyping ftenv tenv e1 t1),
  PInterpExp fenv k n ftenv tenv e1 t1 e0 ->
  forall e3 : ExpTyping ftenv tenv' e2 t2,
  PInterpExp fenv k n ftenv tenv' e2 t2 e3 ->
  PInterpExp fenv k n ftenv tenv (BindS x m e1 e2) t2
    (BindS_Typing ftenv tenv tenv' x e1 e2 t1 t2 m m0 e e0 e3).
    unfold PInterpExp.
    intros.

    specialize (X m1).
    specialize (X0 m1).
    destruct X as [k4 X].
    destruct X as [k5 X].

    destruct X0 as [k8 X0].
    destruct X0 as [k9 X0].

    econstructor 1 with (x:=ExpSoundness_BindS fenv k n ftenv tenv tenv' 
                                        x e1 e2 t1 t2 m m0 e e0 k4 e3 k8).
    
    econstructor 1 with (x:=ExpTrans_BindS fenv k n ftenv tenv tenv'
                                        x e1 e2 t1 t2 m m0 e e0 
                                           k5 e3 k9).

    intros.
    specialize (X s0 n0 q env m2 senv kk).

    unfold ExpSoundness_BindS.
    destruct (k4 m1 env m2 n0 q s0) as [v1 mm1 C1].
    destruct C1 as [w1 C1].
    destruct w1 as [s1 n1].
    simpl in C1.
    simpl in X.
    simpl.

    assert (n1 <= n0) as q01.
    eapply ExpDecrease in C1.
    exact C1.
    assert (n1 <= n) as q1.
    omega.

    set (env' := (x,v1)::env).
    assert (EnvTyping ((x,v1)::env) ((x,t1)::tenv)) as X3.
    {+ eapply updateEnvLemma.
       assumption.
       eapply mm1.
    }

    unfold VTyping in mm1.
    remember (v1) as v1a.
    destruct v1a as [t1' v1a].
    simpl in mm1.
    subst.
(*    inversion mm1; subst. *)
    destruct v1a as [sv1].
        
    set (senv' := ext_senv tenv senv x t1 sv1).
    set (tenv' := (x, t1) :: tenv).

    assert (ValEnv_agree tenv' env' X3 senv') as X1.
    eapply ValEnv_agree_extend.
    exact kk.

    unfold eq_rect_r.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.

    specialize (X0 s1 n1 q1 env' X3 senv' X1).

    unfold FEnvTyping in m1.
    unfold EnvTyping in m2.
    unfold MatchEnvs in m1, m2.
    subst.

    simpl.
    unfold EnvTyping in X3.
    unfold MatchEnvs in X3.
    simpl.

    assert (q1 = (Nat.le_trans n1 n0 n
            (ExpDecrease fenv env s0 s1 n0 n1 e1
                         (Val (existT ValueI t1 (Cst t1 sv1))) C1) q)) as H.
    eapply proof_irrelevance.

    rewrite <- H.
   
    assert (X3 = (updateEnvLemma valueVTyp env
            (map (thicken StaticSemL.Id valueVTyp) env) x
            (existT ValueI t1 (Cst t1 sv1)) t1 eq_refl eq_refl)) as H1.
    eapply proof_irrelevance.

    assert ( k8 eq_refl env'
         (updateEnvLemma valueVTyp env
            (map (thicken StaticSemL.Id valueVTyp) env) x
            (existT ValueI t1 (Cst t1 sv1)) t1 eq_refl eq_refl) n1 q1 s1 =
           k8 eq_refl env' X3 n1 q1 s1 ) as H4.

    rewrite H1.
    reflexivity.

    rewrite H4 at 1.
    clear H4.
    clear H.
    clear H1.
        
    destruct (k8 eq_refl env' X3 n1 q1 s1) as [v2 mm2 C2].
    destruct C2 as [w2 C2].
    destruct w2 as [s2 n2].
    simpl in C2.
    simpl in X0.
    simpl.

    unfold ExpTrans_BindS.

    destruct (k5 eq_refl senv n0 q s0) as [w1 p1].

    unfold DenExp_ext in X.
    simpl in X.

    destruct w1 as [sv1b s1b].
    destruct p1 as [n1b q1b].
    simpl in X.
    inversion X; subst.

    simpl.
    unfold DenExp_ext.
    
    simpl.
    
    unfold eq_rect_r.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.

    unfold sValue.
    simpl.

    assert (q1 = (Nat.le_trans n1b n0 n q1b q)) as H3.
    eapply proof_irrelevance.

    rewrite <- H3.
    clear H3.
    subst senv'.
    destruct (k9 eq_refl
             (ext_senv (map (thicken StaticSemL.Id valueVTyp) env) senv x t1
                       sv1) n1b q1 s1b).

    unfold DenExp_ext in X0.
    simpl in X0.
    unfold VTyping in mm2.
    destruct v2.
    simpl in mm2.
    inversion mm2; subst.
    destruct p as [sv2 w2].
    destruct s as [n2b q2].
    simpl in X0.
    inversion X0; subst.

    simpl.
    reflexivity.
Defined.    


Lemma ExpInterp_Call_aux1 (n: nat)
          (IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
        ExpTyping ftenv tenv e t ->
        {I1
        : forall fenv : funEnv,
          FEnvWT fenv ->
          FEnvTyping fenv ftenv ->
          forall env : valEnv,
          EnvTyping env tenv ->
          forall n' : nat,
          n' <= n -> forall s : InterprBaseL.W, SoundExp fenv env e t s n' &
        {I2
        : forall fenv : funEnv,
          FEnvWT fenv ->
          FEnvTyping fenv ftenv ->
          valTC_Trans tenv ->
          forall n' : nat,
          n' <= n ->
          InterprBaseL.W -> sVTyp t * InterprBaseL.W * {n1 : nat & n1 <= n'} &
        forall (s0 : InterprBaseL.W) (n0 : nat) (q : n0 <= n) 
          (fenv : funEnv) (k0 : FEnvWT fenv) (m1 : FEnvTyping fenv ftenv)
          (env : valEnv) (m2 : EnvTyping env tenv) 
          (senv : valTC_Trans tenv),
        ValEnv_agree tenv env m2 senv ->
        SOS_Exp1 fenv env e t s0 n0 (I1 fenv k0 m1 env m2 n0 q s0) =
        DenExp_ext t n0 (I2 fenv k0 m1 senv n0 q s0)}}) :
      forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
        ExpTyping ftenv tenv e t ->
        forall fenv : funEnv,
        FEnvWT fenv ->
        FEnvTyping fenv ftenv ->
        forall env : valEnv,
        EnvTyping env tenv ->
        forall n' : nat,
          n' <= n -> forall s : InterprBaseL.W, SoundExp fenv env e t s n'.
    intros.
    specialize (IHn ftenv tenv e t X).
    destruct IHn.
    eapply x.
    exact X0.
    exact H.
    exact H0.
    exact H1.
Defined.    

Lemma ExpInterp_Call_aux2 (n: nat)
          (IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
        ExpTyping ftenv tenv e t ->
        {I1
        : forall fenv : funEnv,
          FEnvWT fenv ->
          FEnvTyping fenv ftenv ->
          forall env : valEnv,
          EnvTyping env tenv ->
          forall n' : nat,
          n' <= n -> forall s : InterprBaseL.W, SoundExp fenv env e t s n' &
        {I2
        : forall fenv : funEnv,
          FEnvWT fenv ->
          FEnvTyping fenv ftenv ->
          valTC_Trans tenv ->
          forall n' : nat,
          n' <= n ->
          InterprBaseL.W -> sVTyp t * InterprBaseL.W * {n1 : nat & n1 <= n'} &
        forall (s0 : InterprBaseL.W) (n0 : nat) (q : n0 <= n) 
          (fenv : funEnv) (k0 : FEnvWT fenv) (m1 : FEnvTyping fenv ftenv)
          (env : valEnv) (m2 : EnvTyping env tenv) 
          (senv : valTC_Trans tenv),
        ValEnv_agree tenv env m2 senv ->
        SOS_Exp1 fenv env e t s0 n0 (I1 fenv k0 m1 env m2 n0 q s0) =
        DenExp_ext t n0 (I2 fenv k0 m1 senv n0 q s0)}}) :
      forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
        ExpTyping ftenv tenv e t ->
        forall fenv : funEnv,
        FEnvWT fenv ->
        FEnvTyping fenv ftenv ->
        valTC_Trans tenv ->
        forall n' : nat,
        n' <= n ->
          InterprBaseL.W -> sVTyp t * InterprBaseL.W * {n1 : nat & n1 <= n'}.
    intros.
    specialize (IHn ftenv tenv e t X).
    destruct IHn.
    destruct s.
    eapply x0.
    exact X0.
    exact H.
    exact X1.
    exact H0.
    exact X2.
Defined.    

(***********************************************************************)

Lemma Eval_vls_ok (tenv: valTC) (x: Id) (t: VTyp) (v: sVTyp t)
      (vs: list Value)
      (k0: vlsTyping vs (map snd tenv))             
      (k1: findE tenv x = Some t)
     (k2: findE (mkVEnv tenv vs) x = Some (cst t v)) :
  v = extract_from_valTC_TransB tenv
                                (Eval_vls (map snd tenv) vs k0) x t k1.
  unfold vlsTyping in k0.
  dependent induction k0.
  symmetry in x1.
  eapply map_eq_nil in x1.
  inversion x1; subst.
  inversion k0.

  destruct tenv.
  simpl in x2.
  inversion x2.
  
  destruct p as [x4 t4].
  unfold VTyping in r.
  destruct x0.
  simpl in r.
  inversion r; subst.

  simpl in x2.
  inversion x2; subst.
  clear H.
  clear x2.

  inversion k1; subst.

  unfold VTyping in H0.
  simpl in H0.
  clear H0.

  assert (X = k0) as pp.
  eapply Forall2T_PI.
  intros.
  eapply proof_irrelevance.

  inversion pp; subst.
  clear H.
  
  rename t into t2.

  intros.
  simpl in k2, k3.

  simpl.
  destruct (IdT.IdEqDec x1 x4).
  inversion e; subst.
  inversion k2; subst.
  clear H. 
  inversion k3; subst.
  eapply inj_pair2 in H0.
  inversion H0; subst.
  clear H.
  
  dependent destruction k2.
  unfold cst in k3.
  dependent destruction k3.
  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  reflexivity.

  clear v0.
  clear t4.
  
  specialize (IHk0 tenv v k0 eq_refl).
  assert (k0 ~= k0).
  auto.
  specialize (IHk0 H k2).
  clear H.
  assert (findE (mkVEnv tenv l) x1 = Some (cst t2 v)) as jj.
  unfold mkVEnv.
  eapply k3.
  specialize (IHk0 jj).

  exact IHk0.
Defined.  


Lemma ExpInterp_CallS (fenv : funEnv) (D:  FEnvWT fenv) (n : nat)
  (IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) 
          (t : VTyp) (k : ExpTyping ftenv tenv e t),
        PInterpExp fenv D n ftenv tenv e t k) :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  PInterpPrms fenv D (S n) ftenv tenv (PS ls) pt p ->
  PInterpExp fenv D (S n) ftenv tenv (Call x (PS ls)) t
    (Call_Typing ftenv tenv x ls pt t i p).
    unfold PInterpExp, PInterpPrms in *.
    intros.

    specialize (X m1).
    destruct X as [k4 X].
    destruct X as [k5 X].

    unfold FEnvTyping in m1.
    unfold MatchEnvs in m1.
    subst.
    
    set (ftenv:= (map (thicken StaticSemL.Id funFTyp) fenv)).

    generalize i.
    intro i2.

    eapply (ExtRelVal2A funFTyp ftenv fenv x (FT pt t)) in i2.
    destruct i2 as [f k1 k2].
    
    Focus 2.
    subst.
    constructor.

    rename i into i1.

    generalize D.
    intro D1.
    
    unfold FEnvWT in D.
    specialize (D ftenv eq_refl x f k1).
    unfold FunWT in D.

    destruct f as [tenv0 v e].

    set (v0:= v).
    destruct v as [x0 v].
    simpl in k2.
    inversion k2; subst.
    clear k2.

    set (pt:= PT (map snd tenv0)).

    unfold SoundExp.

    specialize (IHn ftenv tenv0 e t D eq_refl).

    destruct IHn as [IH1 IH2].

    destruct IH2 as [IH2 IH3].
    
    econstructor 1 with (x :=
                           ExpSoundness_CallX fenv D1 n ftenv tenv tenv0
                                              x v0 e t eq_refl k1 IH1
                                              ls pt i1 p k4).
                                        
    econstructor 1 with (x :=
                           ExpTrans_CallX fenv D1 n ftenv tenv tenv0
                                              x v0 e t eq_refl k1 IH2
                                              ls pt i1 p k5).

    intros.
    
    specialize (X s0 n0 q env m2 senv kk).

    unfold ExpSoundness_CallX.   
    unfold ExpSoundness_CallX_aux1.

    remember (k4 eq_refl env m2 n0 q s0) as JJ.

    set (LL1 := let (es, X0) := k4 eq_refl env m2 n0 q s0 in
     let (vs, k2, X1) := X0 in
     let (k3, X2) := X1 in
     let (w2, H4) := X2 in
     (let
        (s2, n2) as p0
         return
           (PClosure fenv env (Conf Prms s0 n0 (PS ls))
              (Conf Prms (fst p0) (snd p0) (PS es)) ->
            {v1 : Value & VTyping v1 t &
            {x0 : TSoundnessL.W * nat &
            EClosure fenv env (Conf Exp s0 n0 (Call x (PS ls)))
              (Conf Exp (fst x0) (snd x0) (Val v1))}}) := w2 in
      fun
        H0 : PClosure fenv env (Conf Prms s0 n0 (PS ls))
               (Conf Prms (fst (s2, n2)) (snd (s2, n2)) (PS es)) =>
      ExpSoundness_CallX_aux2 fenv n ftenv tenv tenv0 x v0 e t eq_refl k1 IH1
        ls pt i1 p env n0 s0 es vs k2 k3 s2 n2 H0 eq_refl m2 q) H4 ).

    set (LL2 := let (es, X0) := JJ in
     let (vs, k2, X1) := X0 in
     let (k3, X2) := X1 in
     let (w2, H4) := X2 in
     (let
        (s2, n2) as p0
         return
           (PClosure fenv env (Conf Prms s0 n0 (PS ls))
              (Conf Prms (fst p0) (snd p0) (PS es)) ->
            {v1 : Value & VTyping v1 t &
            {x0 : TSoundnessL.W * nat &
            EClosure fenv env (Conf Exp s0 n0 (Call x (PS ls)))
              (Conf Exp (fst x0) (snd x0) (Val v1))}}) := w2 in
      fun
        H0 : PClosure fenv env (Conf Prms s0 n0 (PS ls))
               (Conf Prms (fst (s2, n2)) (snd (s2, n2)) (PS es)) =>
      ExpSoundness_CallX_aux2 fenv n ftenv tenv tenv0 x v0 e t eq_refl k1 IH1
        ls pt i1 p env n0 s0 es vs k2 k3 s2 n2 H0 eq_refl m2 q) H4 ).

    assert (LL1 = LL2) as E1.
    subst LL2.
    rewrite HeqJJ at 1.
    reflexivity.

    assert (SOS_Exp1 fenv env (Call x (PS ls)) t s0 n0 LL1 =
            SOS_Exp1 fenv env (Call x (PS ls)) t s0 n0 LL2) as E2.
    rewrite E1.
    reflexivity.

    set (RR := DenExp_ext t n0
    (ExpTrans_CallX fenv D1 n ftenv tenv tenv0 x v0 e t eq_refl k1 IH2 ls pt
       i1 p k5 eq_refl senv n0 q s0)).
           
    assert ((SOS_Exp1 fenv env (Call x (PS ls)) t s0 n0 LL1 = RR) =
            (SOS_Exp1 fenv env (Call x (PS ls)) t s0 n0 LL2 = RR) ) as E3.
    rewrite E2.
    reflexivity.

    assert (SOS_Exp1 fenv env (Call x (PS ls)) t s0 n0 LL2 = RR) as NE.
    
    Focus 2.
    rewrite <- E3 in NE.
    unfold LL1 in NE.
    unfold RR in NE.
    exact NE.

    clear E3 E2 E1 LL1.

    destruct (k4 eq_refl env m2 n0 q s0) as [vs1 mm1].
    subst RR LL2.
    inversion HeqJJ; subst.
    clear H.
    
(* prepare to get IH3 equality and destruct k5 on the right *)
    
    destruct mm1 as [vvs2 uuA1 uuB1].
    destruct uuB1 as [uuB1 uuC1].
    destruct uuC1 as [ww2 uuC1].
    destruct ww2 as [s2 n2].
    simpl in uuC1.
    inversion uuA1; subst.

    unfold isValueList2T in uuA1.
    dependent destruction uuA1.

    unfold SOS_Prms in X.
    unfold InterprBaseL.PreInterL.SOS_Prms_obligation_1 in X.

    rewrite <- eq_rect_eq in X.

    set (env0 := mkVEnv tenv0 vvs2).

    set (ts0 := map snd tenv0).

    set (vsts0 := matchListsAux02_T (funEnv2funTC fenv) (valEnv2valTC env)
            (map snd tenv0) (map Val vvs2) vvs2 eq_refl uuB1).
    
    set (senv0 := Eval_vls ts0 vvs2 vsts0).

    assert (EnvTyping env0 tenv0) as m4.
    subst env0.
    eapply (mkVEnv_typing_lemma2  (funEnv2funTC fenv) 
             (valEnv2valTC env)).
    eapply uuB1.

    assert (ValEnv_agree tenv0 env0 m4 senv0) as VA2.
    subst senv0.
    subst ts0.
    unfold ValEnv_agree.
    intros.
    eapply Eval_vls_ok.
    exact k2.
    
(* proceed to destruct k5 on the right *)

    unfold ExpTrans_CallX.   
    unfold ExpTrans_CallX_aux1.

    remember (k5 eq_refl senv n0 q s0) as JJ.

    set (RR1 :=  DenExp_ext t n0
    (let (p3, X0) := k5 eq_refl senv n0 q s0 in
     let (svs2, s3) := p3 in
     let (n3, q4) := X0 in
     ExpTrans_CallX_aux2 fenv D1 n ftenv tenv tenv0 x v0 e t eq_refl k1 IH2 ls
                         pt i1 p n0 svs2 s3 n3 q4 eq_refl senv q s0) ).

    set (RR2 :=  DenExp_ext t n0
    (let (p3, X0) := JJ in
     let (svs2, s3) := p3 in
     let (n3, q4) := X0 in
     ExpTrans_CallX_aux2 fenv D1 n ftenv tenv tenv0 x v0 e t eq_refl k1 IH2 ls
                         pt i1 p n0 svs2 s3 n3 q4 eq_refl senv q s0) ).

    assert (RR1 = RR2) as E1.
    subst RR2.
    rewrite HeqJJ at 1.
    reflexivity.
    
    set (LL :=   SOS_Exp1 fenv env (Call x (PS ls)) t s0 n0
    (ExpSoundness_CallX_aux2 fenv n ftenv tenv tenv0 x v0 e t eq_refl k1 IH1
       ls pt i1 p env n0 s0 (map Val vvs2) vvs2 eq_refl uuB1 s2 n2 uuC1
       eq_refl m2 q) ).

    assert ((LL = RR1) = (LL = RR2)) as E2.
    rewrite E1.
    reflexivity.

    assert (LL = RR2) as NE.
    Focus 2.
    rewrite <- E2 in NE.
    assumption.

    subst LL RR2 RR1.
    clear E1 E2. 
    
    destruct (k5 eq_refl senv n0 q s0) as [ws1 hh1].
    destruct ws1 as [vs2d w2d].
    destruct hh1 as [n2d q2d]. 
    inversion HeqJJ; subst.
    clear H.

    (* result boils down to: vs2d, w2d, n2d *)

    unfold DenPrms_ext in X.
    simpl in X.
    unfold vlsTyping in vsts0.

    revert X.
    revert VA2.
    revert senv0.
    subst vsts0.
    generalize ((matchListsAux02_T (funEnv2funTC fenv) (valEnv2valTC env) 
                      (map snd tenv0) (map Val vvs2) vvs2 eq_refl uuB1)).
    intro kk1.
    intro.
    intros VA2 X.
    unfold vlsTyping in kk1.

    inversion X; subst.

    destruct n2d.
    Focus 2.
    
    assert (S n2d <= n0) as q2c.
    eapply PrmsDecrease in uuC1.
    assumption.

    assert (S n2d <= S n) as q2e.
    omega.

    assert (n2d <= n) as q2.
    omega.
    
    specialize (IH3 w2d n2d q2 env0 m4 senv0 VA2).

    unfold ExpSoundness_CallX_aux2.

    unfold eq_rect_r.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.

    clear X.
        
    unfold ExpTrans_CallX_aux2.

    assert (forall RBE,
               SOS_Exp1 fenv env (Call x (PS ls)) t s0 n0
    (ExpSoundness_CallX_aux3 fenv n ftenv tenv tenv0 x v0 e t eq_refl k1 IH1
       ls pt p env n0 s0 vvs2 uuB1 eq_refl w2d (S n2d) uuC1 eq_refl m2 q
       RBE) =
  DenExp_ext t n0
    (ExpTrans_CallX_aux3 fenv D1 n ftenv tenv tenv0 x v0 e t eq_refl k1 IH2 ls
       pt i1 p n0 (Eval_vls (map snd tenv0) vvs2 kk1) w2d 
       (S n2d) q2d eq_refl senv q s0
       RBE)).

    intro RBE.
    simpl in RBE.
    subst pt.
    dependent destruction RBE.

    unfold ExpSoundness_CallX_aux3.
    unfold ExpTrans_CallX_aux3.
    
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    unfold f_equal.

    set (RR :=
             DenExp_ext t n0
    (ExpTrans_CallX_aux4 fenv D1 n ftenv tenv tenv0 x v0 e k1 n2d
       (IH2 eq_refl (Eval_vls (map snd tenv0) vvs2 kk1) n2d
          (le_inject n2d n (Nat.le_trans (S n2d) n0 (S n) q2d q)) w2d) ls p i1
       n0 (Eval_vls (map snd tenv0) vvs2 kk1) w2d q2d eq_refl senv q s0
       eq_refl (le_inject n2d n (Nat.le_trans (S n2d) n0 (S n) q2d q))
       eq_refl)).
    
    assert ((mkVEnv_typing_lemma1 (funEnv2funTC fenv) 
             (valEnv2valTC env) (FC tenv0 v0 e) (PT (map snd tenv0))
             (projT1 v0) vvs2 eq_refl uuB1) = m4) as E1.
    eapply proof_irrelevance.

    assert (le_inject n2d n
             (Nat.le_trans (S n2d) n0 (S n)
                (PrmsDecrease fenv env s0 w2d n0 (S n2d) 
                        (PS ls) (PS (map Val vvs2)) uuC1) q) = q2) as E2.
    eapply proof_irrelevance.
    
    assert ( (IH1 eq_refl (mkVEnv tenv0 vvs2)
          (mkVEnv_typing_lemma1 (funEnv2funTC fenv) 
             (valEnv2valTC env) (FC tenv0 v0 e) (PT (map snd tenv0))
             (projT1 v0) vvs2 eq_refl uuB1) n2d
          (le_inject n2d n
             (Nat.le_trans (S n2d) n0 (S n)
                (PrmsDecrease fenv env s0 w2d n0 (S n2d) 
                              (PS ls) (PS (map Val vvs2)) uuC1) q)) w2d)
             =
             (IH1 eq_refl env0 m4 n2d q2 w2d)
           ) as E3.
    rewrite E1.
    rewrite E2.
    reflexivity.

    remember (IH1 eq_refl env0 m4 n2d q2 w2d) as JJ1.
    remember (IH1 eq_refl (mkVEnv tenv0 vvs2)
          (mkVEnv_typing_lemma1 (funEnv2funTC fenv) 
             (valEnv2valTC env) (FC tenv0 v0 e) (PT (map snd tenv0))
             (projT1 v0) vvs2 eq_refl uuB1) n2d
          (le_inject n2d n
             (Nat.le_trans (S n2d) n0 (S n)
                (PrmsDecrease fenv env s0 w2d n0 (S n2d) 
                              (PS ls) (PS (map Val vvs2)) uuC1) q)) w2d)
      as JJ2.

    assert (JJ1 = JJ2) as E4.
    subst JJ1.
    rewrite <- E1.
    rewrite <- E2.
    subst JJ2.
    reflexivity.
    
    set (LL1 := 
      SOS_Exp1 fenv env (Call x (PS ls)) t s0 n0
    (ExpSoundness_CallX_aux4 fenv n ftenv tenv tenv0 x v0 e eq_refl k1 vvs2
       n2d w2d
       (IH1 eq_refl (mkVEnv tenv0 vvs2)
          (mkVEnv_typing_lemma1 (funEnv2funTC fenv) 
             (valEnv2valTC env) (FC tenv0 v0 e) (PT (map snd tenv0))
             (projT1 v0) vvs2 eq_refl uuB1) n2d
          (le_inject n2d n
             (Nat.le_trans (S n2d) n0 (S n)
                (PrmsDecrease fenv env s0 w2d n0 (S n2d) 
                   (PS ls) (PS (map Val vvs2)) uuC1) q)) w2d) ls p env n0 s0
       uuB1 eq_refl uuC1 eq_refl m2 q
       (eq_sym
          (eq_ind (length (map snd tenv0)) (fun n1 : nat => length vvs2 = n1)
             (eq_ind (length (map Val vvs2))
                (fun n1 : nat => n1 = length (map snd tenv0))
                (PrmsArity_lemma (funEnv2funTC fenv) 
                   (valEnv2valTC env) (map Val vvs2) 
                   (map snd tenv0) uuB1) (length vvs2) 
                (map_length Val vvs2)) (length tenv0) 
             (map_length snd tenv0)))
       (mkVEnv_typing_lemma1 (funEnv2funTC fenv) (valEnv2valTC env)
          (FC tenv0 v0 e) (PT (map snd tenv0)) (projT1 v0) vvs2 eq_refl uuB1)
       (le_inject n2d n
          (Nat.le_trans (S n2d) n0 (S n)
             (PrmsDecrease fenv env s0 w2d n0 (S n2d) 
                (PS ls) (PS (map Val vvs2)) uuC1) q))) ).

    set (LL2 := 
      SOS_Exp1 fenv env (Call x (PS ls)) t s0 n0
    (ExpSoundness_CallX_aux4 fenv n ftenv tenv tenv0 x v0 e eq_refl k1 vvs2
       n2d w2d JJ1 ls p env n0 s0
       uuB1 eq_refl uuC1 eq_refl m2 q
       (eq_sym
          (eq_ind (length (map snd tenv0)) (fun n1 : nat => length vvs2 = n1)
             (eq_ind (length (map Val vvs2))
                (fun n1 : nat => n1 = length (map snd tenv0))
                (PrmsArity_lemma (funEnv2funTC fenv) 
                   (valEnv2valTC env) (map Val vvs2) 
                   (map snd tenv0) uuB1) (length vvs2) 
                (map_length Val vvs2)) (length tenv0) 
             (map_length snd tenv0)))
       (mkVEnv_typing_lemma1 (funEnv2funTC fenv) (valEnv2valTC env)
          (FC tenv0 v0 e) (PT (map snd tenv0)) (projT1 v0) vvs2 eq_refl uuB1)
       (le_inject n2d n
          (Nat.le_trans (S n2d) n0 (S n)
             (PrmsDecrease fenv env s0 w2d n0 (S n2d) 
                (PS ls) (PS (map Val vvs2)) uuC1) q))) ).

    assert (LL1 = LL2) as E5.
    subst LL2.
    rewrite E4.
    subst JJ2.
    subst LL1.
    reflexivity.

    assert ((LL1 = RR) = (LL2 = RR)) as E6.
    rewrite E5.
    reflexivity.

    assert (LL2 = RR) as E7.

    Focus 2.
    rewrite <- E6 in E7.

    unfold LL1 in E7.
    unfold RR in E7.
    assumption.

    unfold LL2.
    unfold RR.

    clear E6 E5 E4 E3 E2 E1.
    subst RR LL1 LL2.
    clear HeqJJ2.
    clear JJ2.
    
    destruct (IH1 eq_refl env0 m4 n2d q2 w2d) as [v5 m5 ww5].
    unfold VTyping in m5.
    destruct ww5 as [w5 ww5].
    destruct w5 as [s5 n5].
    simpl in ww5.

    simpl in HeqJJ1.
    destruct v5 as [t5 v5].
    simpl in m5.
    inversion m5; subst.
    
    simpl.
    unfold sValue.
    unfold sValueI.
    simpl.
    destruct v5 as [sv5].
   
    assert (le_inject n2d n (Nat.le_trans (S n2d) n0 (S n) q2d q) = q2) as E1.
    eapply proof_irrelevance.

    rewrite E1.
    subst senv0.
    subst ts0.

    revert IH3.
    generalize (Eval_vls (map snd tenv0) vvs2 kk1).
    intro ts5.
    intro IH3.

    destruct (IH2 eq_refl ts5 n2d q2 w2d) as [pp5 qq5].
    destruct pp5 as [sv5d w5d].
    destruct qq5 as [n5d q5d].

    simpl in IH3.
    unfold sValue in IH3.
    unfold sValueI in IH3.
    simpl in IH3.

    unfold DenExp_ext in IH3.
    simpl in IH3.

    inversion IH3; subst.
    unfold DenExp_ext.
    simpl.
    reflexivity.

    eapply H.


    (* case 0 *)

    assert (0 <= n) as q2.
    omega.

    specialize (IH3 w2d 0 q2 env0 m4 senv0 VA2).

    unfold ExpSoundness_CallX_aux2.

    unfold eq_rect_r.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.

    clear X.
    
    unfold ExpTrans_CallX_aux2.
    
    assert (forall RBE, 
        SOS_Exp1 fenv env (Call x (PS ls)) t s0 n0
    (ExpSoundness_CallX_aux3 fenv n ftenv tenv tenv0 x v0 e t eq_refl k1 IH1
       ls pt p env n0 s0 vvs2 uuB1 eq_refl w2d 0 uuC1 eq_refl m2 q
       RBE) =
  DenExp_ext t n0
    (ExpTrans_CallX_aux3 fenv D1 n ftenv tenv tenv0 x v0 e t eq_refl k1 IH2 ls
       pt i1 p n0 (Eval_vls (map snd tenv0) vvs2 kk1) w2d 0 q2d eq_refl senv q
       s0
       RBE)).

    intro RBE.
    simpl in RBE.
    subst pt.
    dependent destruction RBE.

    unfold ExpSoundness_CallX_aux3.
    unfold ExpTrans_CallX_aux3.
    
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.

    simpl.
    unfold ExpTrans_CallX_aux4_0.
    simpl.
    rename v into v5.
    destruct v5.
    simpl.

    unfold eq_rect_r.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    unfold DenExp_ext.
    simpl.
    reflexivity.

    eapply H.
Defined.    


Lemma ExpInterp_Call0 (fenv : funEnv) (D:  FEnvWT fenv) :
         forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  PInterpPrms fenv D 0 ftenv tenv (PS ls) pt p ->
  PInterpExp fenv D 0 ftenv tenv (Call x (PS ls)) t
             (Call_Typing ftenv tenv x ls pt t i p).
    unfold PInterpExp, PInterpPrms in *.
    intros.

    specialize (X m1).
    destruct X as [k4 X].
    destruct X as [k5 X].

    unfold FEnvTyping in m1.
    unfold MatchEnvs in m1.
    subst.
    
    set (ftenv:= (map (thicken StaticSemL.Id funFTyp) fenv)).

    generalize i.
    intro i2.

    eapply (ExtRelVal2A funFTyp ftenv fenv x (FT pt t)) in i2.
    destruct i2 as [f k1 k2].

    Focus 2.
    subst.
    constructor.

    rename i into i1.

    generalize D.
    intro D1.
    
    unfold FEnvWT in D.
    specialize (D ftenv eq_refl x f k1).
    unfold FunWT in D.

    destruct f.

    set (v0:= v).
    destruct v.
    simpl in k2.
    inversion k2; subst.
    clear k2.

    set (pt:= PT (map snd tenv0)).

    unfold SoundExp.
    
    econstructor 1 with (x :=
                           ExpSoundness_CallX0 fenv D1 ftenv tenv tenv0
                                              x v0 e t eq_refl k1
                                              ls pt i1 p k4).

    econstructor 1 with (x :=
                           ExpTrans_CallX0 fenv D1 ftenv tenv tenv0
                                              x v0 e t eq_refl k1
                                              ls pt i1 p k5).

    intros.

    specialize (X s0 n0 q env m2 senv kk).
    
    unfold ExpSoundness_CallX0.

    assert (n0 = 0) as qq.
    omega.
    inversion qq; subst.
    clear H.

    assert (q = le_n 0) as gg.
    eapply proof_irrelevance.

    inversion gg; subst.
    clear H.

    remember (k4 eq_refl env m2 0 (le_n 0) s0) as JJ.

    set (LL1 := SOS_Exp1 fenv env (Call x (PS ls)) t s0 0
    (ExpSoundness_CallX0_aux1 fenv D1 ftenv tenv tenv0 x v0 e t eq_refl k1 ls
       pt i1 p env s0 (k4 eq_refl env m2 0 (le_n 0) s0) eq_refl m2 0 
       (le_n 0))).

    set (LL2 := SOS_Exp1 fenv env (Call x (PS ls)) t s0 0
    (ExpSoundness_CallX0_aux1 fenv D1 ftenv tenv tenv0 x v0 e t eq_refl k1 ls
       pt i1 p env s0 JJ eq_refl m2 0 
       (le_n 0))).

    assert (LL1 = LL2) as E1.
    subst LL2.
    unfold ExpSoundness_CallX0_aux1.
    rewrite HeqJJ at 1.
    subst LL1.
    reflexivity.

    set (RR := DenExp_ext t 0
    (ExpTrans_CallX0 fenv D1 ftenv tenv tenv0 x v0 e t eq_refl k1 ls pt i1 p
                     k5 eq_refl senv 0 (le_n 0) s0)).

    assert ((LL1 = RR) = (LL2 = RR)) as E2.
    rewrite E1.
    reflexivity.

    assert (LL2 = RR) as NE.
    Focus 2.
    rewrite <- E2 in NE.
    exact NE.

    clear E2 E1 LL1.
    subst RR.

    unfold ExpTrans_CallX0.   
    unfold ExpTrans_CallX0_aux1.

    remember (k5 eq_refl senv 0 (le_n 0) s0) as JJ2.
    
    set (RR1 := DenExp_ext t 0
    (let (p3, X0) := k5 eq_refl senv 0 (le_n 0) s0 in
     let (svs2, s3) := p3 in
     let (n3, _) := X0 in
     ExpTrans_CallX_aux4_0 fenv D1 ftenv tenv tenv0 x v0 e t eq_refl k1 ls pt
       i1 p 0 svs2 s3 (Nat.le_0_l 0) eq_refl senv s0
       (RelatedByEnv funFTyp fenv ftenv x (FC tenv0 v0 e) 
                     (FT pt t) eq_refl k1 i1))).

    set (RR2 := DenExp_ext t 0
    (let (p3, X0) := JJ2 in
     let (svs2, s3) := p3 in
     let (n3, _) := X0 in
     ExpTrans_CallX_aux4_0 fenv D1 ftenv tenv tenv0 x v0 e t eq_refl k1 ls pt
       i1 p 0 svs2 s3 (Nat.le_0_l 0) eq_refl senv s0
       (RelatedByEnv funFTyp fenv ftenv x (FC tenv0 v0 e) 
                     (FT pt t) eq_refl k1 i1))).

    assert (RR1 = RR2) as E1.
    subst RR2.
    rewrite HeqJJ2.
    subst RR1.
    reflexivity.

    assert ((LL2 = RR1) = (LL2 = RR2)) as E2.
    rewrite E1.
    reflexivity.

    assert (LL2 = RR2) as NE.
    Focus 2.
    rewrite <- E2 in NE.
    exact NE.
    
    subst LL2 RR2.
    clear E1 E2 RR1.
    
    destruct (k4 eq_refl env m2 0 (le_n 0) s0) as [vs1 mm1].
    destruct (k5 eq_refl senv 0 (le_n 0) s0) as [ws1 hh1].
    
    inversion HeqJJ; subst.
    clear H.

    destruct mm1 as [vvs2 uuA1 uuB1].
    destruct uuB1 as [uuB1 uuC1].
    destruct uuC1 as [ww2 uuC1].
    destruct ww2 as [s2 n2].
    simpl in uuC1.
    inversion uuA1; subst.

    unfold isValueList2T in uuA1.
    dependent destruction uuA1.
    
    unfold SOS_Prms in X.
    unfold InterprBaseL.PreInterL.SOS_Prms_obligation_1 in X.

    rewrite <- eq_rect_eq in X.

    destruct ws1 as [vs2d w2d].
    destruct hh1 as [n2d q2d].

    unfold DenPrms_ext in X.
    simpl in X.

    revert X.
    generalize ((matchListsAux02_T (funEnv2funTC fenv) (valEnv2valTC env) 
                      (map snd tenv0) (map Val vvs2) vvs2 eq_refl uuB1)).
    intro kk1.
    intro X.
    unfold vlsTyping in kk1.

    inversion X; subst.

    unfold ExpSoundness_CallX0_aux1.

    unfold eq_rect_r.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.

    clear X.

    assert (forall RBE,
        SOS_Exp1 fenv env (Call x (PS ls)) t s0 0
    (ExpSoundness_CallX0_aux2 fenv D1 ftenv tenv tenv0 x v0 e t eq_refl k1 ls
       pt i1 p env s0 vvs2 uuB1 eq_refl w2d n2d uuC1 eq_refl m2 0 
       (le_n 0)
       RBE) =
  DenExp_ext t 0
    (ExpTrans_CallX_aux4_0 fenv D1 ftenv tenv tenv0 x v0 e t eq_refl k1 ls pt
       i1 p 0 (Eval_vls (map snd tenv0) vvs2 kk1) w2d 
       (Nat.le_0_l 0) eq_refl senv s0
       RBE)).
    
    intro RBE.
    simpl in RBE.
    subst pt.
    dependent destruction RBE.

    assert (le_n 0 = Nat.le_0_l 0) as E1.
    eapply proof_irrelevance.
    rewrite E1.
    
    assert (n2d = 0) as q2.
    omega.
    inversion q2; subst.
    clear H.
    
    unfold ExpSoundness_CallX0_aux2.
    
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    unfold f_equal.

    simpl.
    unfold ExpTrans_CallX_aux4_0.
    unfold eq_rect_r.
    unfold DenExp_ext.
    simpl.

    destruct v.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.

    simpl.
    reflexivity.

    eapply H.
Defined.    
    
Lemma ExpInterp_PrmsNil (fenv : funEnv)
  (D : FEnvWT fenv)
  (n : nat) :
  forall (ftenv : funTC) (tenv : valTC),
  PInterpPrms fenv D n ftenv tenv (PS []) (PT [])
    (PSNil_Typing ftenv tenv).
    unfold PInterpExp, PInterpPrms in *.
    intros.
    econstructor 1 with (x := ExpSoundness_PrmsNil fenv D n ftenv tenv).
    econstructor 1 with (x := ExpTrans_PrmsNil fenv D n ftenv tenv).
    intros.
    simpl.
    unfold ExpTrans_PrmsNil.
    unfold DenPrms_ext.
    simpl.
    reflexivity.
Defined.


Lemma ExpInterp_Prms (fenv : funEnv)
  (D : FEnvWT fenv)
  (n : nat) : 
  forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp) 
    (es : list Exp) (ts : list VTyp) (e0 : ExpTyping ftenv tenv e t),
  PInterpExp fenv D n ftenv tenv e t e0 ->
  forall p : PrmsTyping ftenv tenv (PS es) (PT ts),
  PInterpPrms fenv D n ftenv tenv (PS es) (PT ts) p ->
  PInterpPrms fenv D n ftenv tenv (PS (e :: es)) 
    (PT (t :: ts)) (PSCons_Typing ftenv tenv e t es ts e0 p).
    unfold PInterpExp, PInterpPrms.
    intros.
    specialize (X m1).
    specialize (X0 m1).
    destruct X as [k4 X].
    destruct X as [k5 X].

    destruct X0 as [k8 X0].
    destruct X0 as [k9 X0].
    
    econstructor 1 with (x:=ExpSoundness_PrmsCons fenv D n ftenv tenv  
                                        e t es ts e0 k4 p k8).
    
    econstructor 1 with (x:=ExpTrans_Prms fenv D n ftenv tenv 
                                        e t es ts e0 k5 p k9).

    intros.
    specialize (X s0 n0 q env m2 senv kk).
     
    unfold ExpSoundness_PrmsCons.
    destruct (k4 m1 env m2 n0 q s0) as [v1 mm1 C1].
    destruct C1 as [w1 C1].
    destruct w1 as [s1 n1].
    simpl in C1.
    simpl in X.
    simpl.
    
    assert (n1 <= n0) as q01.
    eapply ExpDecrease in C1.
    exact C1.
    assert (n1 <= n) as q1.
    omega.

    unfold VTyping in mm1.
    remember (v1) as v1a.
    destruct v1a as [t1' v1a].
    simpl in mm1.
    subst.
    destruct v1a as [sv1].

    specialize (X0 s1 n1 q1 env m2 senv kk).

    unfold FEnvTyping in m1.
    unfold EnvTyping in m2.
    unfold MatchEnvs in m1, m2.
    subst.
    
    assert ((Nat.le_trans n1 n0 n
            (ExpDecrease fenv env s0 s1 n0 n1 e
               (Val (existT ValueI t (Cst t sv1))) C1) q) = q1) as E1.
    eapply proof_irrelevance.

    rewrite E1.
    clear E1.

    destruct (k8 eq_refl env eq_refl n1 q1 s1) as [es2 C2]. 
    destruct C2 as [vs2 C2 p0].
    inversion C2; subst.
    
    simpl in X0.
    rewrite <- eq_rect_eq in X0.

    unfold ExpTrans_Prms.

    destruct (k5 eq_refl senv n0 q s0).

    unfold DenExp_ext in X.
    simpl in X.
    destruct p1 as [sv1d s1d].
    destruct s as [n1d q1d].
    simpl in X.
    unfold sValue in X.
    simpl in X.
    inversion X; subst.

    destruct p0 as [p2 ww].
    destruct ww as [n2 q2].
    
    simpl.

    assert ((Nat.le_trans n1d n0 n q1d q) = q1) as E1.
    eapply proof_irrelevance.

    rewrite E1.

    destruct (k9 eq_refl senv n1d q1 s1d).
    unfold DenPrms_ext in X0.
    destruct s.
    destruct p0.
    simpl in X0.

    dependent destruction X0.
    simpl.

    rewrite <- eq_rect_eq.
    reflexivity.
Defined.    

      
Lemma append_valTC_Trans_agree (env env0: valEnv) (tenv tenv0: valTC) :
       forall (k: EnvTyping env tenv)       
              (k0: EnvTyping env0 tenv0)    
              (senv: valTC_Trans tenv)
              (kk : ValEnv_agree tenv env k senv), 
         sigT (fun senv1 : valTC_Trans (tenv0 ++ tenv) =>
                 ValEnv_agree (tenv0 ++ tenv) (env0 ++ env)
                        (overrideEnvLemma valueVTyp env0 env tenv0 tenv k0 k)
                        senv1).
  unfold ValEnv_agree.
  intros.
  unfold EnvTyping in k, k0.
  unfold MatchEnvs in k, k0.
  inversion k; subst.
  clear H.

  induction env0.
  simpl.
  econstructor 1 with (x:= senv).
  exact kk.

  destruct IHenv0 as [senv1 IH].
  
  simpl.
  destruct a as [x v].
  destruct v as [t v].
  destruct v as [sv].
  

  set (tenv1 := (map (thicken StaticSemL.Id valueVTyp) env0 ++
                   map (thicken StaticSemL.Id valueVTyp) env)).
  

  econstructor 1 with (x:= ext_senv tenv1 senv1 x t sv).

  simpl.
(*  specialize (IH x t sv). *)

  intro x0.

  destruct (IdT.IdEqDec x0 x).

  inversion e; subst.
  intros.
  inversion k1; subst.
  inversion k2; subst.
  eapply inj_pair2 in H1.
  inversion H1; subst.
  dependent destruction k1.
  
  simpl.
  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  simpl.
  reflexivity.

  intros.
  specialize (IH x0 t0 v k1 k2).
  rewrite IH at 1.

  reflexivity.
Defined.  


Lemma append_valTC_Trans_agreeE (env env0: valEnv) (tenv tenv0: valTC) :
       forall (k: EnvTyping env tenv)       
              (k0: EnvTyping env0 tenv0)    
              (senv: valTC_Trans tenv)
              (kk : ValEnv_agree tenv env k senv), 
         sigT2 (fun senv1 : valTC_Trans (tenv0 ++ tenv) =>
                 ValEnv_agree (tenv0 ++ tenv) (env0 ++ env)
                        (overrideEnvLemma valueVTyp env0 env tenv0 tenv k0 k)
                        senv1)
               (fun senv1 : valTC_Trans (tenv0 ++ tenv) =>
                  senv1 = extend_valTC_Trans env0 tenv tenv0 k0 senv). 
  unfold ValEnv_agree.
  intros.
  unfold EnvTyping in k, k0.
  unfold MatchEnvs in k, k0.
  inversion k; subst.
  clear H.

  induction env0.
  simpl.
  econstructor 1 with (x:= senv).
  exact kk.

  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  reflexivity.

  destruct IHenv0 as [senv1 IH].
  
  simpl.
  destruct a as [x v].
  destruct v as [t v].
  destruct v as [sv].
  
  set (tenv1 := (map (thicken StaticSemL.Id valueVTyp) env0 ++
                   map (thicken StaticSemL.Id valueVTyp) env)).
  
  econstructor 1 with (x:= ext_senv tenv1 senv1 x t sv).

  simpl.
(*  specialize (IH x t sv). *)

  intro x0.

  destruct (IdT.IdEqDec x0 x).

  inversion e; subst.
  intros.
  inversion k1; subst.
  inversion k2; subst.
  eapply inj_pair2 in H1.
  inversion H1; subst.
  dependent destruction k1.
  
  simpl.
  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  simpl.
  reflexivity.

  intros.
  specialize (IH x0 t0 v k1 k2).
  rewrite IH at 1.

  reflexivity.

  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  unfold ext_senv.
  unfold sValue.
  simpl.

  f_equal.

  rewrite e.
  simpl.
  reflexivity.
Defined.  
  

Lemma ExpInterp_BindMS (fenv : funEnv)
  (D : FEnvWT fenv)
  (n : nat) : 
forall (ftenv : funTC) (tenv tenv0 tenv1 : valTC) 
    (env0 : valEnv) (e : Exp) (t : VTyp) (e0 : EnvTyping env0 tenv0)
    (e1 : tenv1 = tenv0 ++ tenv) (e2 : ExpTyping ftenv tenv1 e t),
  PInterpExp fenv D n ftenv tenv1 e t e2 ->
  PInterpExp fenv D n ftenv tenv (BindMS env0 e) t
    (BindMS_Typing ftenv tenv tenv0 tenv1 env0 e t e0 e1 e2).
    unfold PInterpExp, PInterpPrms.
    intros.
    specialize (X m1).
    destruct X as [k4 X].
    destruct X as [k5 X].

    econstructor 1 with (x:=ExpSoundness_BindMS fenv D n ftenv tenv
                               tenv0 tenv1 env0 e t e0 e1 e2 k4).
    
    econstructor 1 with (x:=ExpTrans_BindMS fenv D n ftenv tenv
                               tenv0 tenv1 env0 e t e0 e1 e2 k5).
    
    intros.

    set (X3 := overrideEnvLemma valueVTyp env0 env tenv0 tenv e0 m2).

    inversion e1; subst.
    set (env1:= env0 ++ env).
    set (tenv1:= tenv0 ++ tenv).

    set (seag1:= append_valTC_Trans_agreeE env env0 tenv tenv0
                                          m2 e0 senv kk).

    destruct seag1 as [senv1 kk1 kk2].

    specialize (X s0 n0 q env1 X3 senv1 kk1).
    
    unfold ExpSoundness_BindMS.
    
    unfold eq_rect_r.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    subst env1.
    subst X3.

    clear kk1.

    destruct (k4 m1 (env0 ++ env)
                 (overrideEnvLemma valueVTyp env0 env tenv0 tenv e0 m2) n0 q s0)
         as [v1 vt1 ss1]. 

    destruct ss1 as [ww1 ss1].
    unfold VTyping in vt1.
    inversion vt1; subst.
    destruct ww1 as [s1 n1].

    simpl in *.
    unfold eq_rect_r.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.

    exact X.
Defined.    
    
      
Lemma ExpInterp_IfThenElse (fenv : funEnv)
  (D : FEnvWT fenv)
  (n : nat) : 
  forall (ftenv : funTC) (tenv : valTC) (e1 e2 e3 : Exp) 
    (t : VTyp) (e : ExpTyping ftenv tenv e1 Bool),
  PInterpExp fenv D n ftenv tenv e1 Bool e ->
  forall e0 : ExpTyping ftenv tenv e2 t,
  PInterpExp fenv D n ftenv tenv e2 t e0 ->
  forall e4 : ExpTyping ftenv tenv e3 t,
  PInterpExp fenv D n ftenv tenv e3 t e4 ->
  PInterpExp fenv D n ftenv tenv (IfThenElse e1 e2 e3) t
    (IfThenElse_Typing ftenv tenv e1 e2 e3 t e e0 e4).
    unfold PInterpExp, PInterpPrms.
    intros.
    specialize (X m1).
    specialize (X0 m1).
    specialize (X1 m1).
    destruct X as [k4 X].
    destruct X as [k5 X].
    destruct X0 as [k8 X0].
    destruct X0 as [k9 X0].
    destruct X1 as [k12 X1].
    destruct X1 as [k13 X1].

    econstructor 1 with (x := ExpSoundness_IfThenElse fenv D n
                                  ftenv tenv e1 e2 e3 t e k4 e0 k8 e4 k12).
    econstructor 1 with (x := ExpTrans_IfThenElse fenv D n
                                  ftenv tenv e1 e2 e3 t e k5 e0 k9 e4 k13).

    intros.
    specialize (X s0 n0 q env m2 senv kk).

    unfold ExpSoundness_IfThenElse.
    destruct (k4 m1 env m2 n0 q s0) as [v1 vt1 ss1].

    destruct ss1 as [ww1 ss1].
    unfold VTyping in vt1.
    inversion vt1; subst.
    destruct ww1 as [s1 n1].

    destruct v1 as [t1 v1].
    simpl in vt1.
    inversion vt1; subst.

    destruct v1 as [v1].
    
    simpl. 
    unfold eq_rect_r.  
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    simpl.

    simpl in ss1.

    generalize ss1.
    intro ss1a.
    assert (n1 <= n0) as q1a.
    eapply ExpDecrease in ss1a.
    assumption.

    assert (n1 <= n) as q1.
    omega.

    unfold ExpTrans_IfThenElse.
    destruct (k5 m1 senv n0 q s0) as [ww1 jj2].
    destruct ww1 as [sv1d s1d].
    destruct jj2 as [n1d q1d].
    
    simpl in X.
    unfold DenExp_ext in X.
    simpl in X.
    inversion X; subst.
    simpl.
    
    destruct v1.
    simpl.

    specialize (X0 s1d n1d q1 env m2 senv kk).
    
    generalize (Nat.le_trans n1d n0 n
            (ExpDecrease fenv env s0 s1d n0 n1d e1
                         (Val (existT ValueI Bool (Cst Bool true))) ss1a) q).
    intro q1c.
    assert (q1 = q1c) as E1.
    eapply proof_irrelevance.

    inversion E1; subst.
    
    destruct (k8 m1 env m2 n1d q1c s1d) as [v2 vt2 ss2].
    
    destruct ss2 as [ww2 ss2].
    unfold VTyping in vt2.
    inversion vt2; subst.
    destruct ww2 as [s2 n2].

    generalize (Nat.le_trans n1d n0 n q1d q).
    intro q1e.
    assert (q1c = q1e) as E1.
    eapply proof_irrelevance.
    inversion E1; subst.

    destruct (k9 m1 senv n1d q1e s1d) as [ww2 jj2].
    destruct ww2 as [sv2d s2d].
    destruct jj2 as [n2d q2d].
    
    unfold DenExp_ext in *.
    simpl in X0.
    inversion X0; subst.

    simpl.
    reflexivity.

    specialize (X1 s1d n1d q1 env m2 senv kk).
    
    generalize (Nat.le_trans n1d n0 n
            (ExpDecrease fenv env s0 s1d n0 n1d e1
                         (Val (existT ValueI Bool (Cst Bool false))) ss1a) q).
    intro q1c.
    assert (q1 = q1c) as E1.
    eapply proof_irrelevance.

    inversion E1; subst.

    destruct (k12 m1 env m2 n1d q1c s1d) as [v2 vt2 ss2].
    
    destruct ss2 as [ww2 ss2].
    unfold VTyping in vt2.
    inversion vt2; subst.
    destruct ww2 as [s2 n2].

    generalize (Nat.le_trans n1d n0 n q1d q).
    intro q1e.
    assert (q1c = q1e) as E1.
    eapply proof_irrelevance.
    inversion E1; subst.

    simpl.

    destruct (k13 m1 senv n1d q1e s1d) as [ww2 jj2].
    destruct ww2 as [sv2d s2d].
    destruct jj2 as [n2d q2d].
    
    unfold DenExp_ext in *.
    simpl in X1.
    inversion X1; subst.

    simpl.
    reflexivity.
Defined. 


Lemma ExpInterp_Modify (fenv : funEnv)
  (D : FEnvWT fenv)
  (n : nat) :
  forall (ftenv : funTC) (tenv : valTC) (t1 t2 : VTyp) 
    (XF : XFun t1 t2) (e : Exp) (e0 : ExpTyping ftenv tenv e t1),
  PInterpExp fenv D n ftenv tenv e t1 e0 ->
  PInterpExp fenv D n ftenv tenv (Modify t1 t2 XF e) t2
    (Modify_Typing ftenv tenv t1 t2 XF e e0).
    unfold PInterpExp, PInterpPrms.
    intros.
    specialize (X m1).
    destruct X as [k4 X].
    destruct X as [k5 X].

    econstructor 1 with (x:=ExpSoundness_Modify fenv D n ftenv tenv
                              t1 t2 XF e e0 k4).
    
    econstructor 1 with (x:=ExpTrans_Modify fenv D n ftenv tenv
                              t1 t2 XF e e0 k5).
    
    intros.
    specialize (X s0 n0 q env m2 senv kk).
    
    unfold ExpSoundness_Modify.
    simpl.
    
    destruct (k4 m1 env m2 n0 q s0) as [v1 mm1 C1].
    destruct C1 as [w1 C1].
    destruct w1 as [s1 n1].
    simpl in C1.
    simpl in X.
    simpl.

    unfold VTyping in mm1.
    inversion mm1; subst.
    unfold ExpTrans_Modify.

    destruct (k5 m1 senv n0 q s0) as [ww1 p1].
    destruct ww1 as [sv1 s1d].
    destruct p1 as [n1p q1].

    unfold DenExp_ext in X.
    simpl in X.
    inversion X; subst.
 
    simpl.
    destruct XF.

    simpl.
    unfold SOS_Exp1.
    simpl.
    unfold DenExp_ext.
    simpl.
    destruct v1.
    destruct v.
    unfold EnvTyping in m2.
    unfold MatchEnvs in m2.
    inversion m2; subst.

    simpl in *.
    unfold sValue.
    unfold sValueI.
    simpl.
    reflexivity.
Defined.    
    
    
(*********************************************************************)


Lemma ExpInterp_ApplyS (fenv : funEnv) (D:  FEnvWT fenv) (n : nat) 
  (IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) 
          (t : VTyp) (k : ExpTyping ftenv tenv e t), 
        PInterpExp fenv D n ftenv tenv e t k) :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (e9 : Exp) (ls : list Exp) (pt : PTyp) (t : VTyp) (p9 : Pure e9)
    (i : IdFTyping ftenv x (FT pt t)) (p : PrmsTyping ftenv tenv (PS ls) pt),
  PInterpPrms fenv D (S n) ftenv tenv (PS ls) pt p ->
  forall m9 : ExpTyping ftenv tenv e9 Nat,
  PInterpExp fenv D (S n) ftenv tenv e9 Nat m9 ->
  PInterpExp fenv D (S n) ftenv tenv (Apply x (PS ls) e9) t
    (Apply_Typing ftenv tenv x e9 (PS ls) pt t p9 i p m9).
    unfold PInterpExp, PInterpPrms in *.
    intros.

    specialize (X m1).
    specialize (X0 m1).
    destruct X as [k4 X].
    destruct X as [k5 X].

    rename X0 into Y.
    destruct Y as [k8 Y].
    destruct Y as [k9 Y].
    
    unfold FEnvTyping in m1.
    unfold MatchEnvs in m1.
    subst.
    
    set (ftenv:= (map (thicken StaticSemL.Id funFTyp) fenv)).

    generalize i.
    intro i2.

    eapply (ExtRelVal2A funFTyp ftenv fenv x (FT pt t)) in i2.
    destruct i2 as [f k1 k2].
    
    Focus 2.
    subst.
    constructor.

    rename i into i1.

    generalize D.
    intro D1.
    
    unfold FEnvWT in D.
    specialize (D ftenv eq_refl x f k1).
    unfold FunWT in D.

    destruct f as [tenv0 v e].

    set (v0:= v).
    destruct v as [x0 v].
    simpl in k2.
    inversion k2; subst.
    clear k2.

    set (pt:= PT (map snd tenv0)).

    unfold SoundExp.

    specialize (IHn ftenv tenv0 e t D eq_refl).

    destruct IHn as [IH1 IH2].

    destruct IH2 as [IH2 IH3].

    econstructor 1 with (x :=
                           ExpSoundness_ApplyX fenv D1 n ftenv tenv tenv0
                                              x v0 e t eq_refl k1 IH1
                                              e9 ls pt p9 i1 p k4 m9 k8).
    
    econstructor 1 with (x :=
                           ExpTrans_ApplyX fenv D1 n ftenv tenv tenv0
                                              x v0 e t eq_refl k1 IH2
                                              e9 ls pt p9 i1 p k5 m9 k9).

    intros.

(* deal with Y - left *)
    
    specialize (Y s0 n0 q env m2 senv kk).
    
    unfold ExpSoundness_ApplyX.
    
    remember (k8 eq_refl env m2 n0 q s0) as JJ.

    set (LL1 := SOS_Exp1 fenv env (Apply x (PS ls) e9) t s0 n0
    (ExpSoundness_ApplyX_aux0 fenv n ftenv tenv tenv0 x v0 e t eq_refl k1 IH1
       e9 ls pt p9 i1 p k4 m9 env n0 s0 (k8 eq_refl env m2 n0 q s0) eq_refl m2
       q)).

    set (LL2 := SOS_Exp1 fenv env (Apply x (PS ls) e9) t s0 n0
    (ExpSoundness_ApplyX_aux0 fenv n ftenv tenv tenv0 x v0 e t eq_refl k1 IH1
       e9 ls pt p9 i1 p k4 m9 env n0 s0 JJ eq_refl m2
       q)).

    assert (LL1 = LL2) as E1.
    subst LL2.
    unfold ExpSoundness_ApplyX_aux0.
    rewrite HeqJJ at 1.
    subst LL1.
    reflexivity.

    set (RR := DenExp_ext t n0
    (ExpTrans_ApplyX fenv D1 n ftenv tenv tenv0 x v0 e t eq_refl k1 IH2 e9 ls
                     pt p9 i1 p k5 m9 k9 eq_refl senv n0 q s0)).

    assert ((LL1 = RR) = (LL2 = RR)) as E2.
    rewrite E1.
    reflexivity.

    assert (LL2 = RR) as NE.
    Focus 2.
    rewrite <- E2 in NE.
    exact NE.

    clear E2 E1 LL1.
    subst RR.

(* deal with Y - right *)
    
    unfold ExpTrans_ApplyX.

    remember (k9 eq_refl senv n0 q s0) as JJ2.

    set (RR1 := DenExp_ext t n0
    (ExpTrans_ApplyX_aux0 fenv D1 n ftenv tenv tenv0 x v0 e t eq_refl k1 IH2
          e9 ls pt i1 p k5 m9 n0 (k9 eq_refl senv n0 q s0) eq_refl senv q s0)).

    set (RR2 := DenExp_ext t n0
    (ExpTrans_ApplyX_aux0 fenv D1 n ftenv tenv tenv0 x v0 e t eq_refl k1 IH2
                          e9 ls pt i1 p k5 m9 n0 JJ2 eq_refl senv q s0)).

    assert (RR1 = RR2) as E1.
    subst RR2.
    unfold ExpTrans_ApplyX_aux0.
    rewrite HeqJJ2.
    reflexivity.

    assert ((LL2 = RR1) = (LL2 = RR2)) as E2.
    rewrite E1.
    reflexivity.

    assert (LL2 = RR2) as NE.
    Focus 2.
    rewrite <- E2 in NE.
    exact NE.
    
    subst LL2 RR2.
    clear E1 E2 RR1.

(* destruct in Y *)
    
    destruct (k8 eq_refl env m2 n0 q s0) as [v9 pp9 ss9].
    destruct (k9 eq_refl senv n0 q s0) as [ws9 hh9].

    inversion HeqJJ; subst.
    clear H.

    destruct ss9 as [ww9 uu9].
    destruct ww9 as [s9 n9].
    simpl in uu9.
    unfold VTyping in pp9.
    destruct v9 as [t9 v9].
    destruct v9 as [sv9].
    unfold Nat in pp9.
    unfold valueVTyp in pp9.
    simpl in pp9.
    inversion pp9; subst.
    clear H.

    destruct ws9 as [sv9a s9a].
    simpl in sv9a.
    destruct hh9 as [n9a q9a].
    
    unfold DenExp_ext in Y.
    simpl in Y.
    unfold sValue in Y.
    simpl in Y.
    inversion Y; subst.
    clear Y.

(* deal with Pure *)    
    
     unfold ExpSoundness_ApplyX_aux0.
     generalize (Pure_sideffect fenv env s0 s9a n0 n9a e9
        (Val
           (existT ValueI (VT nat (CInt nat eq_refl I32 Unsigned))
               (Cst (VT nat (CInt nat eq_refl I32 Unsigned)) sv9a))) p9 uu9).
     intro bb.
     destruct bb as [bb1 bb2]. 
     inversion bb1; subst.
     clear H.
     unfold eq_rect_r.
     rewrite <- eq_rect_eq.
     rewrite <- eq_rect_eq.
     rewrite <- eq_rect_eq.

(* deal with X - left *)
     
     specialize (X s9a n9a q env m2 senv kk).

     remember (k4 eq_refl env m2 n9a q s9a) as JJ1.
     
     set (LL1 := SOS_Exp1 fenv env (Apply x (PS ls) e9) t s9a n9a
    (ExpSoundness_ApplyX_aux1 fenv n ftenv tenv tenv0 x v0 e t eq_refl k1 IH1
       e9 ls pt p9 i1 p env s9a n9a (k4 eq_refl env m2 n9a q s9a) m9
       (existT ValueI (VT nat (CInt nat eq_refl I32 Unsigned))
               (Cst (VT nat (CInt nat eq_refl I32 Unsigned)) sv9a))
       eq_refl eq_refl m2 q uu9)).

     set (LL2 := SOS_Exp1 fenv env (Apply x (PS ls) e9) t s9a n9a
    (ExpSoundness_ApplyX_aux1 fenv n ftenv tenv tenv0 x v0 e t eq_refl k1 IH1
       e9 ls pt p9 i1 p env s9a n9a JJ1 m9
       (existT ValueI (VT nat (CInt nat eq_refl I32 Unsigned))
               (Cst (VT nat (CInt nat eq_refl I32 Unsigned)) sv9a))
       eq_refl eq_refl m2 q uu9)).

    assert (LL1 = LL2) as E1.
    subst LL2.
    rewrite HeqJJ1.
    subst LL1.
    reflexivity.
    
    set (RR := DenExp_ext t n9a
    (ExpTrans_ApplyX_aux0 fenv D1 n ftenv tenv tenv0 x v0 e t eq_refl k1 IH2
       e9 ls pt i1 p k5 m9 n9a
       (sv9a, s9a, existT (fun n1 : nat => n1 <= n9a) n9a q9a) eq_refl senv q
       s9a)).

    assert ((LL1 = RR) = (LL2 = RR)) as E2.
    rewrite E1.
    reflexivity.

    assert (LL2 = RR) as NE.
    Focus 2.
    rewrite <- E2 in NE.
    exact NE.

    clear E2 E1 LL1.
    subst RR.

(* deal with X - right *)
    
    unfold ExpTrans_ApplyX_aux0.

    remember (k5 eq_refl senv n9a q s9a) as JJ2.

    set (RR1 := DenExp_ext t n9a
    (ExpTrans_ApplyX_aux1 fenv D1 n ftenv tenv tenv0 x v0 e t eq_refl k1 IH2
       e9 ls pt i1 p n9a (k5 eq_refl senv n9a q s9a) m9 sv9a s9a n9a q9a
       eq_refl senv q s9a)).

    set (RR2 := DenExp_ext t n9a
    (ExpTrans_ApplyX_aux1 fenv D1 n ftenv tenv tenv0 x v0 e t eq_refl k1 IH2
       e9 ls pt i1 p n9a JJ2 m9 sv9a s9a n9a q9a
       eq_refl senv q s9a)).

    assert (RR1 = RR2) as E1.
    subst RR2.
    rewrite HeqJJ2.
    subst RR1.
    reflexivity.

    assert ((LL2 = RR1) = (LL2 = RR2)) as E2.
    rewrite E1.
    reflexivity.

    assert (LL2 = RR2) as NE.
    Focus 2.
    rewrite <- E2 in NE.
    exact NE.
    
    subst LL2 RR2.
    clear E1 E2 RR1.

(* destruct in X *)
    
    destruct (k4 eq_refl env m2 n9a q s9a) as [vs1 mm1].
    destruct (k5 eq_refl senv n9a q s9a) as [ws1 hh1].

    inversion HeqJJ1; subst.
    clear H.

    destruct mm1 as [vvs2 uuA1 uuB1].
    destruct uuB1 as [uuB1 uuC1].
    destruct uuC1 as [ww2 uuC1].
    destruct ww2 as [s2 n2].
    simpl in uuC1.
    inversion uuA1; subst.

    unfold isValueList2T in uuA1.
    dependent destruction uuA1.

    destruct ws1 as [vs2d w2d].
    destruct hh1 as [n2d q2d].

    simpl in X.
    unfold DenPrms_ext in X.
    simpl in X.

    revert X.
    generalize ((matchListsAux02_T (funEnv2funTC fenv) (valEnv2valTC env) 
                      (map snd tenv0) (map Val vvs2) vvs2 eq_refl uuB1)).
    intro kk1.
    intro X.
    unfold vlsTyping in kk1.

    inversion X; subst.
    clear X.

(* prepare IH3 *)

    set (env0 := mkVEnv tenv0 vvs2).

    set (ts0 := map snd tenv0).
        
    set (senv0 := Eval_vls ts0 vvs2 kk1).

    assert (EnvTyping env0 tenv0) as m4.
    subst env0.
    eapply (mkVEnv_typing_lemma2  (funEnv2funTC fenv) 
             (valEnv2valTC env)).
    eapply uuB1.

    assert (ValEnv_agree tenv0 env0 m4 senv0) as VA2.
    subst senv0.
    subst ts0.
    unfold ValEnv_agree.
    intros.
    eapply Eval_vls_ok.
    exact k2.
    
    unfold ExpSoundness_ApplyX_aux1.
    unfold ExpSoundness_ApplyX_aux2.

    unfold eq_rect_r.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.

    unfold ExpTrans_ApplyX_aux1. 
    unfold ExpTrans_ApplyX_aux2. 
    
    assert (forall RBE, SOS_Exp1 fenv env (Apply x (PS ls) e9) t s9a n9a
    (ExpSoundness_ApplyX_aux3 fenv n ftenv tenv tenv0 x v0 e t eq_refl k1 IH1
       e9 ls pt p env s9a n9a vvs2 uuB1 eq_refl w2d n2d uuC1 m9
       (existT ValueI (VT nat (CInt nat eq_refl I32 Unsigned))
               (Cst (VT nat (CInt nat eq_refl I32 Unsigned)) sv9a))
       eq_refl eq_refl m2 q uu9
       RBE) =
  DenExp_ext t n9a
    (ExpTrans_ApplyX_aux3 fenv D1 n ftenv tenv tenv0 x v0 e t eq_refl k1 IH2
       e9 ls pt i1 p n9a (Eval_vls (map snd tenv0) vvs2 kk1) w2d n2d q2d m9
       sv9a s9a n9a q9a eq_refl senv q s9a
       RBE)).

    intro RBE.
    simpl in RBE.
    subst pt.
    dependent destruction RBE.

    remember (Init.Nat.min n2d sv9a) as n11.
    
    destruct n2d.

(* 1st case of n11 = 0 *)

    simpl in Heqn11.
    
    unfold SOS_Exp1.
    unfold ExpSoundness_ApplyX_aux3.
        
    unfold eq_rect_r.
    simpl.

    unfold ExpTrans_ApplyX_aux3.
    simpl.
    unfold ExpTrans_ApplyX_aux4_0.
    simpl.
    unfold DenExp_ext.
    simpl.
    destruct v.
    simpl.
    reflexivity.
    
    destruct sv9a.

(* 2nd case of n11 = 0 *)

    assert (Init.Nat.min (S n2d) 0 = 0) as E1.
    auto.
    rewrite E1 in Heqn11.

    unfold SOS_Exp1.
    unfold ExpSoundness_ApplyX_aux3.

    unfold eq_rect_r.
    simpl.

    unfold ExpTrans_ApplyX_aux3.
    simpl.
    unfold ExpTrans_ApplyX_aux4_0.
    simpl.
    unfold DenExp_ext.
    simpl.
    destruct v.
    simpl.
    reflexivity.
    
    destruct n11.

(* 3rd case of n11 = 0 *)

    assert (Init.Nat.min (S n2d) (S sv9a) = S (Init.Nat.min n2d sv9a)).
    simpl.
    reflexivity.
    rewrite H in Heqn11.
    inversion Heqn11.

(* case of n11 = S _ *)

    simpl in Heqn11.
   
(* prepare IH3 *)

    assert (S n11 <= S n2d) as q2c.
    rewrite Heqn11.
    assert (Init.Nat.min n2d sv9a <= n2d) as q2ca.
    intuition.
    intuition.
       
    assert (S n11 <= n9a) as q2cb.
    eapply le_trans.
    exact q2c.
    exact q2d.
    
    assert (S n11 <= S n) as q2e.
    intuition.

    assert (n11 <= n) as q2.
    intuition.
  
    specialize (IH3 w2d n11 q2 env0 m4 senv0 VA2).

    clear q2c q2cb q2e.
    
(* simplify the goal *)

    unfold ExpSoundness_ApplyX_aux3.
    unfold eq_rect_r.
    simpl.
    unfold ExpSoundness_ApplyX_aux4.

    inversion Heqn11; subst.
    dependent destruction Heqn11.

    
    assert (mkVEnv_typing_lemma1 (funEnv2funTC fenv) 
             (valEnv2valTC env) (FC tenv0 v0 e) (PT (map snd tenv0))
             (projT1 v0) vvs2 eq_refl uuB1 = m4) as EA1.
    eapply proof_irrelevance.
            
    assert ( (le_inject (Init.Nat.min n2d sv9a) n
             (Nat.le_trans (S (Init.Nat.min n2d sv9a)) 
                (S n2d) (S n)
                (eq_ind_r (fun n0 : nat => n0 <= S n2d)
                   (Nat.le_min_l (S n2d) (S sv9a)) eq_refl)
                (Nat.le_trans (S n2d) n9a (S n)
                   (PrmsDecrease fenv env s9a w2d n9a 
                (S n2d) (PS ls) (PS (map Val vvs2)) uuC1) q))) = q2) as EA2.
    eapply proof_irrelevance.

(* left side *)

    remember (IH1 eq_refl (mkVEnv tenv0 vvs2)
          (mkVEnv_typing_lemma1 (funEnv2funTC fenv) 
             (valEnv2valTC env) (FC tenv0 v0 e) (PT (map snd tenv0))
             (projT1 v0) vvs2 eq_refl uuB1) (Init.Nat.min n2d sv9a)
          (le_inject (Init.Nat.min n2d sv9a) n
             (Nat.le_trans (S (Init.Nat.min n2d sv9a)) 
                (S n2d) (S n)
                (eq_ind_r (fun n0 : nat => n0 <= S n2d)
                   (Nat.le_min_l (S n2d) (S sv9a)) eq_refl)
                (Nat.le_trans (S n2d) n9a (S n)
                   (PrmsDecrease fenv env s9a w2d n9a 
                  (S n2d) (PS ls) (PS (map Val vvs2)) uuC1) q))) w2d) as JJ1.
    
    remember (IH1 eq_refl env0 m4 (Init.Nat.min n2d sv9a) q2 w2d) as JJ2.
    
    assert (JJ2 = JJ1) as E4.
    subst JJ2.
    rewrite <- EA1.
    rewrite <- EA2.
    subst JJ1.
    reflexivity.

    set (RR := DenExp_ext t n9a
    (ExpTrans_ApplyX_aux3 fenv D1 n ftenv tenv tenv0 x v0 e t eq_refl k1 IH2
       e9 ls (PT (map snd tenv0)) i1 p n9a (Eval_vls (map snd tenv0) vvs2 kk1)
       w2d (S n2d) q2d m9 (S sv9a) s9a n9a q9a eq_refl senv q s9a eq_refl)).

    set (LL1 := SOS_Exp1 fenv env (Apply x (PS ls) e9) t s9a n9a
    (ExpSoundness_ApplyX_aux4_1 fenv n ftenv tenv tenv0 x v0 e eq_refl k1 vvs2
       (Init.Nat.min n2d sv9a) w2d
       (IH1 eq_refl (mkVEnv tenv0 vvs2)
          (mkVEnv_typing_lemma1 (funEnv2funTC fenv) 
             (valEnv2valTC env) (FC tenv0 v0 e) (PT (map snd tenv0))
             (projT1 v0) vvs2 eq_refl uuB1) (Init.Nat.min n2d sv9a)
          (le_inject (Init.Nat.min n2d sv9a) n
             (Nat.le_trans (S (Init.Nat.min n2d sv9a)) 
                (S n2d) (S n)
                (eq_ind_r (fun n0 : nat => n0 <= S n2d)
                   (Nat.le_min_l (S n2d) (S sv9a)) eq_refl)
                (Nat.le_trans (S n2d) n9a (S n)
                   (PrmsDecrease fenv env s9a w2d n9a 
                      (S n2d) (PS ls) (PS (map Val vvs2)) uuC1) q))) w2d) e9
       ls p env s9a n9a uuB1 eq_refl (S n2d) uuC1 m9 
       (S sv9a) eq_refl eq_refl m2 q uu9
       (eq_sym
          (eq_ind (length (map snd tenv0)) (fun n0 : nat => length vvs2 = n0)
             (eq_ind (length (map Val vvs2))
                (fun n0 : nat => n0 = length (map snd tenv0))
                (PrmsArity_lemma (funEnv2funTC fenv) 
                   (valEnv2valTC env) (map Val vvs2) 
                   (map snd tenv0) uuB1) (length vvs2) 
                (map_length Val vvs2)) (length tenv0) 
             (map_length snd tenv0))) eq_refl
       (mkVEnv_typing_lemma1 (funEnv2funTC fenv) (valEnv2valTC env)
          (FC tenv0 v0 e) (PT (map snd tenv0)) (projT1 v0) vvs2 eq_refl uuB1)
       (Nat.le_trans (S n2d) n9a (S n)
          (PrmsDecrease fenv env s9a w2d n9a (S n2d) 
             (PS ls) (PS (map Val vvs2)) uuC1) q)
       (eq_ind_r (fun n0 : nat => n0 <= S n2d) (Nat.le_min_l (S n2d) (S sv9a))
          eq_refl)
       (Nat.le_trans (S (Init.Nat.min n2d sv9a)) (S n2d) 
          (S n)
          (eq_ind_r (fun n0 : nat => n0 <= S n2d)
             (Nat.le_min_l (S n2d) (S sv9a)) eq_refl)
          (Nat.le_trans (S n2d) n9a (S n)
             (PrmsDecrease fenv env s9a w2d n9a (S n2d) 
                (PS ls) (PS (map Val vvs2)) uuC1) q))
       (le_inject (Init.Nat.min n2d sv9a) n
          (Nat.le_trans (S (Init.Nat.min n2d sv9a)) 
             (S n2d) (S n)
             (eq_ind_r (fun n0 : nat => n0 <= S n2d)
                (Nat.le_min_l (S n2d) (S sv9a)) eq_refl)
             (Nat.le_trans (S n2d) n9a (S n)
                (PrmsDecrease fenv env s9a w2d n9a 
                   (S n2d) (PS ls) (PS (map Val vvs2)) uuC1) q))))).
    
    set (LL2 := SOS_Exp1 fenv env (Apply x (PS ls) e9) t s9a n9a
    (ExpSoundness_ApplyX_aux4_1 fenv n ftenv tenv tenv0 x v0 e eq_refl k1 vvs2
                                (Init.Nat.min n2d sv9a) w2d
                                JJ2 e9
       ls p env s9a n9a uuB1 eq_refl (S n2d) uuC1 m9 
       (S sv9a) eq_refl eq_refl m2 q uu9
       (eq_sym
          (eq_ind (length (map snd tenv0)) (fun n0 : nat => length vvs2 = n0)
             (eq_ind (length (map Val vvs2))
                (fun n0 : nat => n0 = length (map snd tenv0))
                (PrmsArity_lemma (funEnv2funTC fenv) 
                   (valEnv2valTC env) (map Val vvs2) 
                   (map snd tenv0) uuB1) (length vvs2) 
                (map_length Val vvs2)) (length tenv0) 
             (map_length snd tenv0))) eq_refl
       (mkVEnv_typing_lemma1 (funEnv2funTC fenv) (valEnv2valTC env)
          (FC tenv0 v0 e) (PT (map snd tenv0)) (projT1 v0) vvs2 eq_refl uuB1)
       (Nat.le_trans (S n2d) n9a (S n)
          (PrmsDecrease fenv env s9a w2d n9a (S n2d) 
             (PS ls) (PS (map Val vvs2)) uuC1) q)
       (eq_ind_r (fun n0 : nat => n0 <= S n2d) (Nat.le_min_l (S n2d) (S sv9a))
          eq_refl)
       (Nat.le_trans (S (Init.Nat.min n2d sv9a)) (S n2d) 
          (S n)
          (eq_ind_r (fun n0 : nat => n0 <= S n2d)
             (Nat.le_min_l (S n2d) (S sv9a)) eq_refl)
          (Nat.le_trans (S n2d) n9a (S n)
             (PrmsDecrease fenv env s9a w2d n9a (S n2d) 
                (PS ls) (PS (map Val vvs2)) uuC1) q))
       (le_inject (Init.Nat.min n2d sv9a) n
          (Nat.le_trans (S (Init.Nat.min n2d sv9a)) 
             (S n2d) (S n)
             (eq_ind_r (fun n0 : nat => n0 <= S n2d)
                (Nat.le_min_l (S n2d) (S sv9a)) eq_refl)
             (Nat.le_trans (S n2d) n9a (S n)
                (PrmsDecrease fenv env s9a w2d n9a 
                   (S n2d) (PS ls) (PS (map Val vvs2)) uuC1) q))))).
    
    assert (LL1 = LL2) as E5.
    subst LL2.
    rewrite E4.
    subst JJ1.
    subst LL1.
    reflexivity.

    assert ((LL1 = RR) = (LL2 = RR)) as E6.
    rewrite E5.
    reflexivity.

    assert (LL2 = RR) as E7.

    Focus 2.
    rewrite <- E6 in E7.

    unfold LL1 in E7.
    unfold RR in E7.
    assumption.

    unfold RR.

    clear E6 E5 E4.
    subst LL1.
    clear HeqJJ1.
    clear JJ1.

(* right side *)    
    
    unfold ExpTrans_ApplyX_aux3.
    simpl.

    assert ((le_inject (Init.Nat.min n2d sv9a) n
             (Nat.le_trans (S (Init.Nat.min n2d sv9a)) 
                (S n2d) (S n)
                (eq_ind_r (fun n0 : nat => n0 <= S n2d)
                   (Nat.le_min_l (S n2d) (S sv9a)) eq_refl)
                (Nat.le_trans (S n2d) n9a (S n) q2d q))) = q2) as EA3.
    eapply proof_irrelevance.

    remember (IH2 eq_refl (Eval_vls (map snd tenv0) vvs2 kk1)
          (Init.Nat.min n2d sv9a)
          (le_inject (Init.Nat.min n2d sv9a) n
             (Nat.le_trans (S (Init.Nat.min n2d sv9a)) 
                (S n2d) (S n)
                (eq_ind_r (fun n0 : nat => n0 <= S n2d)
                   (Nat.le_min_l (S n2d) (S sv9a)) eq_refl)
                (Nat.le_trans (S n2d) n9a (S n) q2d q))) w2d) as JJ3.

    remember (IH2 eq_refl senv0 (Init.Nat.min n2d sv9a) q2 w2d) as JJ4.

    assert (JJ4 = JJ3) as E8.
    subst JJ4.
    rewrite <- EA3.
    subst JJ3.
    reflexivity.

    set (RR1 := DenExp_ext t n9a
    (ExpTrans_ApplyX_aux4 fenv D1 n ftenv tenv tenv0 x v0 e k1
       (Init.Nat.min n2d sv9a)
       (IH2 eq_refl (Eval_vls (map snd tenv0) vvs2 kk1)
          (Init.Nat.min n2d sv9a)
          (le_inject (Init.Nat.min n2d sv9a) n
             (Nat.le_trans (S (Init.Nat.min n2d sv9a)) 
                (S n2d) (S n)
                (eq_ind_r (fun n0 : nat => n0 <= S n2d)
                   (Nat.le_min_l (S n2d) (S sv9a)) eq_refl)
                (Nat.le_trans (S n2d) n9a (S n) q2d q))) w2d) e9 ls p i1 n9a
       (Eval_vls (map snd tenv0) vvs2 kk1) w2d (S n2d) q2d m9 
       (S sv9a) s9a n9a q9a eq_refl senv q s9a eq_refl eq_refl
       (eq_ind_r (fun n0 : nat => n0 <= S n2d) (Nat.le_min_l (S n2d) (S sv9a))
                 eq_refl) eq_refl)).

    set (RR2 := DenExp_ext t n9a
    (ExpTrans_ApplyX_aux4 fenv D1 n ftenv tenv tenv0 x v0 e k1
       (Init.Nat.min n2d sv9a)
       JJ4 e9 ls p i1 n9a
       (Eval_vls (map snd tenv0) vvs2 kk1) w2d (S n2d) q2d m9 
       (S sv9a) s9a n9a q9a eq_refl senv q s9a eq_refl eq_refl
       (eq_ind_r (fun n0 : nat => n0 <= S n2d) (Nat.le_min_l (S n2d) (S sv9a))
          eq_refl) eq_refl)).

    assert (RR1 = RR2) as E5.
    subst RR2.
    rewrite E8.
    subst JJ3.
    subst RR1.
    reflexivity.

    assert ((LL2 = RR1) = (LL2 = RR2)) as E6.
    rewrite E5.
    reflexivity.

    assert (LL2 = RR2) as E7.

    Focus 2.
    rewrite <- E6 in E7.

    unfold RR1 in E7.
    assumption.

    clear E5 E6 E8.
    clear EA1 EA2 EA3 RR1 RR HeqJJ3.
    clear JJ3.
    subst LL2.
    subst RR2.
    
(* destruct in IH3 *)

    destruct (IH1 eq_refl env0 m4 (Init.Nat.min n2d sv9a) q2 w2d)
      as [v5 m5 ww5]. 
    destruct (IH2 eq_refl senv0 (Init.Nat.min n2d sv9a) q2 w2d) as [pp5 qq5].

(* on the right *)
    
    unfold VTyping in m5.
    destruct ww5 as [w5 ww5].
    destruct w5 as [s5 n5].
    simpl in ww5.

    simpl in HeqJJ2.
    destruct v5 as [t5 v5].
    simpl in m5.
    inversion m5; subst.

    simpl.
    unfold sValue.
    unfold sValueI.
    simpl.
    destruct v5 as [sv5].

(* on the left *)

    destruct pp5 as [sv5d w5d].
    destruct qq5 as [n5d q5d].

    simpl in IH3.
    unfold sValue in IH3.
    unfold sValueI in IH3.
    simpl in IH3.

    unfold DenExp_ext in IH3.
    simpl in IH3.

    inversion IH3; subst.
    unfold DenExp_ext.
    simpl.
    reflexivity.

    eapply H.
Defined.    
    
    
(****************************************************)


Lemma ExpSoundness_ApplyX0_aux3
  (fenv : funEnv)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (t : VTyp)
  (m : VTyping v t)
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (e9 : Exp)
  (ls : list Exp)
  (pt : PTyp)
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (env : valEnv)
  (m9 : ExpTyping ftenv tenv e9 Nat)
  (s9: W)
  (vs : list Value)
  (k3 : PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) (PS (map Val vs)) pt)
  (k2 : isValueList2T (map Val vs) vs)
  (s2 : W)
  (n2 : nat)
  (n10 : nat)
  (H40 : PClosure fenv env (Conf Prms s9 0 (PS ls))
          (Conf Prms s2 n2 (PS (map Val vs))))
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (X3 : EClosure fenv env (Conf Exp s9 0 e9) (Conf Exp s9 0
             (Val
               (existT ValueI (VT nat (CInt nat eq_refl I32 Unsigned))
                  (Cst (VT nat (CInt nat eq_refl I32 Unsigned)) n10)))))
                                                 (*  (Val v9))) *)
  (i3 : funFTyp (FC tenv0 v e) = FT pt t)
  (n : nat)
  (H1 : n <= 0)
  :
  {v0 : Value & VTyping v0 t &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s9 n (Apply x (PS ls) e9))
    (Conf Exp (fst x0) (snd x0) (Val v0))}}.

    set (v9 := Val
               (existT ValueI (VT nat (CInt nat eq_refl I32 Unsigned))
                  (Cst (VT nat (CInt nat eq_refl I32 Unsigned)) n10))).
    set (f:=FC tenv0 v e). 
    set (ft:=FT pt t). 
  
    simpl in i3.
    inversion i3; subst.
    clear i3.

    set (t:= projT1 v).
    set (pt:=PT (map snd tenv0)).
        
    assert (funArity f = length vs) as H50.
    {+ eapply PrmsArity_lemma in k3.
       rewrite map_length in k3.
       rewrite map_length in k3.
       symmetry.
       exact k3.
    }

    assert (n2 <= 0) as qq1.
    eapply PrmsDecrease in H40.
    exact H40.

    assert (n2 = 0) as qq2.
    eapply (min_zero n2).
    exact qq1.

    inversion qq2; subst.
    subst t.

    assert (n = 0) as qq3.
    eapply (min_zero n).
    exact H1.

    inversion qq3; subst.

    assert (0 = min 0 n10) as h11.
    intuition.
    
    eapply (ExpSoundness_ApplyX_aux4_0 fenv ftenv tenv tenv0 x v e eq_refl
               i2 e9 ls p env s9 0 vs k3 k2 s2 0 H40 m9 n10 H H0 X3 H50
                h11).
Defined.
    

Lemma ExpSoundness_ApplyX0_aux1 
  (fenv : funEnv)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (t : VTyp)
  (m : VTyping v t)
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (e9 : Exp)
  (ls : list Exp)
  (pt : PTyp)
  (p9: Pure e9)
  (i1 : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (m9 : ExpTyping ftenv tenv e9 Nat)
  (env : valEnv)
  (s9: W)
  (X : {es : list Exp &
      {x : list Value & isValueList2T es x &
      PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) (PS es) pt *
      {x0 : W * nat &
      PClosure fenv env (Conf Prms s9 0 (PS ls))
               (Conf Prms (fst x0) (snd x0) (PS es))}}})
  (v9 : Value)
  (k9 : VTyping v9 Nat)
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (X3 : EClosure fenv env (Conf Exp s9 0 e9) (Conf Exp s9 0 (Val v9)))
  (n : nat)
  (H1 : n <= 0)
  :
  {v0 : Value & VTyping v0 t &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s9 n (Apply x (PS ls) e9))
    (Conf Exp (fst x0) (snd x0) (Val v0))}}.
    destruct X as [es X].
    destruct X as [vs k2 X].
    destruct X as [k3 X].
    destruct X as [w2 H40].
    destruct w2 as [s2 n2].

    simpl in *.  

    set (f := FC tenv0 v e).
    set (ft := FT pt t).
    inversion k2; subst.
    
    unfold VTyping in k9.
    unfold valueVTyp in k9.
    unfold Nat in k9.
    destruct v9 as [t9 v9].
    simpl in k9.
    inversion k9; subst.
    destruct v9 as [n10].
    clear H2.
    
    generalize i1.
    intro i3.

    eapply (RelatedByEnv funFTyp fenv ftenv x f ft H i2) in i3.

    eapply (ExpSoundness_ApplyX0_aux3 fenv ftenv tenv tenv0 x v e t m
                     i2 e9 ls pt p env m9 s9 vs k3 k2 s2 n2 n10 H40
                               H H0 X3 i3 n H1).
Defined.


Lemma ExpSoundness_ApplyX0_aux0 
  (fenv : funEnv)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (t : VTyp)
  (m : VTyping v t)
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (e9: Exp) (**)
  (ls : list Exp)
  (pt : PTyp)
  (p9: Pure e9) (**)
  (i1 : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (X : FEnvTyping fenv ftenv ->
      forall env : valEnv,
      EnvTyping env tenv ->
      forall n0 : nat,
      n0 <= 0 ->
      forall s : W,
      {es : list Exp &
      {x : list Value & isValueList2T es x &
      PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) (PS es) pt *
      {x : W * nat &
      PClosure fenv env (Conf Prms s n0 (PS ls))
        (Conf Prms (fst x) (snd x) (PS es))}}}) (**)
  (m9 : ExpTyping ftenv tenv e9 Nat) (**)
  (env : valEnv)
  (s : W)
  (X0 : {v : Value & VTyping v Nat &
        {x : W * nat &
            EClosure fenv env (Conf Exp s 0 e9)
                     (Conf Exp (fst x) (snd x) (Val v))}}) (**)
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (n : nat)
  (H1 : n <= 0)
  :
  {v0 : Value & VTyping v0 t &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s n (Apply x (PS ls) e9))
           (Conf Exp (fst x0) (snd x0) (Val v0))}}.  
    destruct X0 as [v9 k9 X0].
    destruct X0 as [w X0].
    destruct w as [s9 n9].
    
    simpl in *.
    generalize X0.
    intro X3.
    eapply (Pure_sideffect _ _ _ _ _ _ _ _ p9) in X0.
    destruct X0 as [H2 H3].
    inversion H2; subst.

    assert (0 <= 0) as q0.
    auto.
    specialize (X H env H0 0 q0 s9).

    eapply (ExpSoundness_ApplyX0_aux1 fenv ftenv tenv tenv0 x v e t m
                   i2 e9 ls pt p9 i1 p m9 env s9 X v9 k9 H H0 X3 n H1).
Defined.

    
Lemma ExpSoundness_ApplyX0 : forall (fenv: funEnv) (D:  FEnvWT fenv)
    (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
    (v: Value) (e: Exp)
    (t : VTyp) (m: VTyping v t)
    (i2 : findE fenv x = Some (FC tenv0 v e))     
    (e9 : Exp) (ls : list Exp) (pt : PTyp) (p9 : Pure e9)
    (i1 : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),  
  PrmsSoundness_def fenv D 0 ftenv tenv (PS ls) pt p ->
  forall m9 : ExpTyping ftenv tenv e9 Nat,
  ExpSoundness_def fenv D 0 ftenv tenv e9 Nat m9 ->
  ExpSoundness_def fenv D 0 ftenv tenv (Apply x (PS ls) e9) t
                   (Apply_Typing ftenv tenv x e9 (PS ls) pt t p9 i1 p m9).
    unfold ExpSoundness_def, SoundExp, PrmsSoundness_def, SoundPrms.
    intros.

    assert (0 <= 0) as q0.
    auto.

    specialize (X0 H env H0 0 q0 s).

    eapply (ExpSoundness_ApplyX0_aux0 fenv ftenv tenv tenv0 x v e t m
                   i2 e9 ls pt p9 i1 p X m9 env s X0 H H0 n H1).
Defined.


(********************************************************************)

Lemma ExpTrans_ApplyX0_aux3
    (v: Value) 
    (t : VTyp) (m: valueVTyp v = t)
    (s3 : W) : 
  sVTyp t * W * {n2 : nat & n2 <= 0}.
    
    split.
    destruct v.
    destruct v.
    simpl in m.
    inversion m; subst.
    exact (v, s3).
    econstructor 1 with (x:=0).
    intuition.
Defined.


Lemma ExpTrans_ApplyX0_aux1 (fenv: funEnv) (D: FEnvWT fenv) 
    (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
    (v: Value) (e: Exp)
    (t : VTyp) (m: VTyping v t)
    (i2 : findE fenv x = Some (FC tenv0 v e))     
  (e9: Exp) 
  (ls : list Exp)
  (pt : PTyp)
  (i1 : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (n1 : nat)
  (X : PTyp_TRN pt * W * {n2 : nat & n2 <= n1})
  (m9 : ExpTyping ftenv tenv e9 Nat)
  (n10 : nat)
  (H : FEnvTyping fenv ftenv)
  (X0 : valTC_Trans tenv)
  (H1 : n1 <= 0)
  (X1 : W) :
  sVTyp t * W * {n2 : nat & n2 <= n1}.

   destruct X as [p3 X].
    destruct p3 as [svs2 s3].
    destruct X as [n3 q4].
    simpl in *.

    set (f:=FC tenv0 v e).
    set (ft:=FT pt t).
    unfold VTyping in m.
     
    generalize i1.
    intro i3.

    assert (n3 <= n1) as q6.
    intuition.
    
    eapply (RelatedByEnv funFTyp fenv ftenv x f ft H i2) in i3.

    assert (0 = min n3 n10) as h11.
    assert (n3 = 0).
    intuition.
    rewrite H0.
    intuition.
    
    eapply (ExpTrans_ApplyX_aux4_0 fenv D ftenv tenv tenv0
                                x v e t m i2 e9 ls pt i1 p n1
                                svs2 s3 n3 q6 m9 n10 
                                H X0 X1 i3 h11).
Defined.
    

Lemma ExpTrans_ApplyX0_aux0 (fenv : funEnv)
    (D: FEnvWT fenv) 
    (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
    (v: Value) (e: Exp)
    (t : VTyp) (m: VTyping v t)
    (i2 : findE fenv x = Some (FC tenv0 v e))     
    (e9 : Exp)
    (ls : list Exp)
    (pt : PTyp)
    (i1 : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt)
  (X : FEnvTyping fenv ftenv ->
      valTC_Trans tenv ->
      forall n1 : nat,
      n1 <= 0 ->
      W -> PTyp_TRN pt * W * {n2 : nat & n2 <= n1})
  (m9 : ExpTyping ftenv tenv e9 Nat)
  (n1 : nat)
  (Y : sVTyp Nat * W * {n2 : nat & n2 <= n1})  
  (H : FEnvTyping fenv ftenv)
  (X0 : valTC_Trans tenv)
  (H1 : n1 <= 0)
  (X1 : W) :
  sVTyp t * W * {n2 : nat & n2 <= n1}.
    destruct Y as [pp9 Y].
    destruct pp9 as [n10 s9].
    destruct Y as [n9 q9].
    simpl in *.

    specialize (X H X0 n1 H1 X1).

    eapply (ExpTrans_ApplyX0_aux1 fenv D ftenv tenv tenv0 x v e t m
                    i2 e9 ls pt i1 p n1 X m9 n10 H X0 H1 X1).
Defined.


Lemma ExpTrans_ApplyX0 (fenv: funEnv) (D: FEnvWT fenv) 
     (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
     (v: Value) (e: Exp)
     (t : VTyp) (m: VTyping v t)
     (i2 : findE fenv x = Some (FC tenv0 v e)) :
    forall (e9 : Exp) (ls : list Exp) (pt : PTyp) (p9 : Pure e9)
           (i1 : IdFTyping ftenv x (FT pt t))
           (p : PrmsTyping ftenv tenv (PS ls) pt),
      PrmsTrans3_def fenv D 0 ftenv tenv (PS ls) pt p ->
   forall m9 : ExpTyping ftenv tenv e9 Nat,
   ExpTrans3_def fenv D 0 ftenv tenv e9 Nat m9 ->
   ExpTrans3_def fenv D 0 ftenv tenv (Apply x (PS ls) e9) t
                 (Apply_Typing ftenv tenv x e9 (PS ls) pt t p9 i1 p m9).
    unfold ExpTrans3_def, PrmsTrans3_def.
    intros e9 ls pt p9 i1 p.
    intros X m9 Y H X0 n1 H0 X1.
    specialize (Y H X0 n1 H0 X1).
    eapply (ExpTrans_ApplyX0_aux0 fenv D ftenv tenv tenv0
           x v e t m i2 e9 ls pt i1 p X m9 n1 Y H X0 H0 X1).
Defined.


(*******************************************************************)

Lemma ExpInterp_Apply0 (fenv : funEnv) (D:  FEnvWT fenv) :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (e9 : Exp) (ls : list Exp) (pt : PTyp) (t : VTyp) (p9 : Pure e9)
    (i1 : IdFTyping ftenv x (FT pt t)) (p0 : PrmsTyping ftenv tenv (PS ls) pt),
  PInterpPrms fenv D 0 ftenv tenv (PS ls) pt p0 ->
  forall e0 : ExpTyping ftenv tenv e9 Nat,
  PInterpExp fenv D 0 ftenv tenv e9 Nat e0 ->
  PInterpExp fenv D 0 ftenv tenv (Apply x (PS ls) e9) t
    (Apply_Typing ftenv tenv x e9 (PS ls) pt t p9 i1 p0 e0).
    unfold PInterpExp, PInterpPrms in *.
    intros.

    specialize (X m1).
    specialize (X0 m1).
    destruct X as [k4 X].
    destruct X as [k5 X].

    rename X0 into Y.
    destruct Y as [k8 Y].
    destruct Y as [k9 Y].
    
    unfold FEnvTyping in m1.
    unfold MatchEnvs in m1.
    subst.
    
    set (ftenv:= (map (thicken StaticSemL.Id funFTyp) fenv)).

    generalize i1.
    intro i2.

    eapply (ExtRelVal2A funFTyp ftenv fenv x (FT pt t)) in i2.
    destruct i2 as [f k1 k2].
    
    Focus 2.
    subst.
    constructor.

    generalize D.
    intro D1.
    
    unfold FEnvWT in D.
    specialize (D ftenv eq_refl x f k1).
    unfold FunWT in D.

    destruct f as [tenv0 v e].

    set (v0:= v).
    destruct v as [x0 v].
    simpl in k2.
    inversion k2; subst.
    clear k2.

    set (pt:= PT (map snd tenv0)).

    unfold SoundExp.

    econstructor 1 with (x :=
                           ExpSoundness_ApplyX0 fenv D1 ftenv tenv tenv0
                                              x v0 e t eq_refl k1 
                                              e9 ls pt p9 i1 p0 k4 e0 k8).

    econstructor 1 with (x :=
                           ExpTrans_ApplyX0 fenv D1 ftenv tenv tenv0
                                              x v0 e t eq_refl k1 
                                              e9 ls pt p9 i1 p0 k5 e0 k9).

    intros.

    specialize (Y s0 n0 q env m2 senv kk).
    specialize (X s0 n0 q env m2 senv kk).
    
    unfold ExpSoundness_ApplyX0.

    assert (n0 = 0) as q1.
    intuition.
    inversion q1; subst.
    clear H.

    assert (q = le_n 0) as gg.
    eapply proof_irrelevance.

    inversion gg; subst.
    clear H.

    remember (k8 eq_refl env m2 0 (le_n 0) s0) as JJ1.

    set (LL1 := SOS_Exp1 fenv env (Apply x (PS ls) e9) t s0 0
    (ExpSoundness_ApplyX0_aux0 fenv ftenv tenv tenv0 x v0 e t eq_refl k1 e9 ls
       pt p9 i1 p0 k4 e0 env s0 (k8 eq_refl env m2 0 (le_n 0) s0) eq_refl m2 0
       (le_n 0))).

    set (LL2 := SOS_Exp1 fenv env (Apply x (PS ls) e9) t s0 0
    (ExpSoundness_ApplyX0_aux0 fenv ftenv tenv tenv0 x v0 e t eq_refl k1 e9 ls
       pt p9 i1 p0 k4 e0 env s0 JJ1 eq_refl m2 0
       (le_n 0))).

    set (RR := DenExp_ext t 0
    (ExpTrans_ApplyX0 fenv D1 ftenv tenv tenv0 x v0 e t eq_refl k1 e9 ls pt p9
       i1 p0 k5 e0 k9 eq_refl senv 0 (le_n 0) s0)).

    assert (LL1 = LL2) as E1.
    subst LL2.
    unfold ExpSoundness_ApplyX0_aux0.
    rewrite HeqJJ1 at 1.
    subst LL1.
    reflexivity.
    
    assert ((LL1 = RR) = (LL2 = RR)) as E2.
    rewrite E1.
    reflexivity.

    assert (LL2 = RR) as NE.
    Focus 2.
    rewrite <- E2 in NE.
    exact NE.

    clear E2 E1 LL1.    
    subst RR.

    unfold ExpTrans_ApplyX0.
    
    remember (k9 eq_refl senv 0 (le_n 0) s0) as JJ2.

    set (RR1 := DenExp_ext t 0
    (ExpTrans_ApplyX0_aux0 fenv D1 ftenv tenv tenv0 x v0 e t eq_refl k1 e9 ls
       pt i1 p0 k5 e0 0 (k9 eq_refl senv 0 (le_n 0) s0) eq_refl senv 
       (le_n 0) s0)).

    set (RR2 := DenExp_ext t 0
    (ExpTrans_ApplyX0_aux0 fenv D1 ftenv tenv tenv0 x v0 e t eq_refl k1 e9 ls
       pt i1 p0 k5 e0 0 JJ2 eq_refl senv 
       (le_n 0) s0)).

    assert (RR1 = RR2) as E1.
    subst RR2.
    rewrite HeqJJ2.
    reflexivity.

    assert ((LL2 = RR1) = (LL2 = RR2)) as E2.
    rewrite E1.
    reflexivity.

    assert (LL2 = RR2) as NE.
    Focus 2.
    rewrite <- E2 in NE.
    exact NE.
    
    subst LL2 RR2.
    clear E1 E2 RR1.
    
    destruct (k8 eq_refl env m2 0 (le_n 0) s0) as [v9 pp9 ss9].
    destruct (k9 eq_refl senv 0 (le_n 0) s0) as [ws9 hh9].

    inversion HeqJJ1; subst.
    clear H.

    destruct ss9 as [ww9 uu9].
    destruct ww9 as [s9 n9].
    simpl in uu9.
    unfold VTyping in pp9.
    destruct v9 as [t9 v9].
    destruct v9 as [sv9].
    unfold Nat in pp9.
    unfold valueVTyp in pp9.
    simpl in pp9.
    inversion pp9; subst.
    clear H.

    destruct ws9 as [sv9a s9a].
    simpl in sv9a.
    destruct hh9 as [n9a q9a].
    
    unfold DenExp_ext in Y.
    simpl in Y.
    unfold sValue in Y.
    simpl in Y.
    inversion Y; subst.
    clear Y.
    
    simpl.
    
    destruct (Pure_sideffect fenv env s0 s9a 0 n9a e9
        (Val
           (existT ValueI (VT nat (CInt nat eq_refl I32 Unsigned))
                   (Cst (VT nat (CInt nat eq_refl I32 Unsigned)) sv9a)))
        p9 uu9).

    inversion e1; subst.
    unfold eq_rect_r.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    
    remember (k4 eq_refl env m2 0 (le_n 0) s9a) as JJ1.

    set (LL1 := SOS_Exp1 fenv env (Apply x (PS ls) e9) t s9a 0
    (ExpSoundness_ApplyX0_aux1 fenv ftenv tenv tenv0 x v0 e t eq_refl k1 e9 ls
       pt p9 i1 p0 e0 env s9a (k4 eq_refl env m2 0 (le_n 0) s9a)
       (existT ValueI (VT nat (CInt nat eq_refl I32 Unsigned))
               (Cst (VT nat (CInt nat eq_refl I32 Unsigned)) sv9a))
       eq_refl eq_refl m2 uu9 0
       (le_n 0))).

    set (LL2 := SOS_Exp1 fenv env (Apply x (PS ls) e9) t s9a 0
    (ExpSoundness_ApplyX0_aux1 fenv ftenv tenv tenv0 x v0 e t eq_refl k1 e9 ls
       pt p9 i1 p0 e0 env s9a JJ1
       (existT ValueI (VT nat (CInt nat eq_refl I32 Unsigned))
               (Cst (VT nat (CInt nat eq_refl I32 Unsigned)) sv9a))
       eq_refl eq_refl m2 uu9 0
       (le_n 0))).

    set (RR := DenExp_ext t 0
    (ExpTrans_ApplyX0_aux1 fenv D1 ftenv tenv tenv0 x v0 e t eq_refl k1 e9 ls
       pt i1 p0 0 (k5 eq_refl senv 0 (le_n 0) s9a) e0 sv9a eq_refl senv
       (le_n 0) s9a)).

    assert (LL1 = LL2) as E1.
    subst LL2.
    unfold ExpSoundness_ApplyX0_aux1.
    rewrite HeqJJ1 at 1.
    subst LL1.
    reflexivity.
    
    assert ((LL1 = RR) = (LL2 = RR)) as E2.
    rewrite E1.
    reflexivity.

    assert (LL2 = RR) as NE.
    Focus 2.
    rewrite <- E2 in NE.
    exact NE.

    clear E2 E1 LL1.
    subst RR.
    subst LL2.

    remember (k5 eq_refl senv 0 (le_n 0) s9a) as JJ2.
    
    destruct (k4 eq_refl env m2 0 (le_n 0) s9a) as [vs1 mm1].
    destruct (k5 eq_refl senv 0 (le_n 0) s9a) as [ws1 hh1].
    
    inversion HeqJJ1; subst.
    clear H0.

    destruct mm1 as [vvs2 uuA1 uuB1].
    destruct uuB1 as [uuB1 uuC1].
    destruct uuC1 as [ww2 uuC1].
    destruct ww2 as [s2 n2].
    simpl in uuC1.
    inversion uuA1; subst.

    unfold isValueList2T in uuA1.
    dependent destruction uuA1.
    
    destruct ws1 as [vs2d w2d].
    destruct hh1 as [n2d q2d].

    simpl.

    unfold eq_rect_r.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    
    simpl in X.
    revert X.

    generalize (matchListsAux02_T (funEnv2funTC fenv) (valEnv2valTC env)                          (map snd tenv0) (map Val vvs2) vvs2 eq_refl uuB1).
    
    intro kk1.
    intro X.
    unfold DenPrms_ext in X.
    simpl in X.
    inversion X; subst.
    clear X.
    clear H.

    remember (RelatedByEnv funFTyp fenv ftenv x (FC tenv0 v0 e) 
                           (FT pt t) eq_refl k1 i1) as JJ.

    unfold ExpTrans_ApplyX_aux4_0.
    destruct v.
    simpl.
    unfold eq_rect_r.
    rewrite <- eq_rect_eq.
     
    set (PP1 := SOS_Exp1 fenv env (Apply x (PS ls) e9) t s9a 0
    (ExpSoundness_ApplyX0_aux3 fenv ftenv tenv tenv0 x v0 e t eq_refl k1 e9 ls
       pt p0 env e0 s9a vvs2 uuB1 eq_refl w2d n2d sv9a uuC1 eq_refl m2 uu9
       (RelatedByEnv funFTyp fenv ftenv x (FC tenv0 v0 e) 
          (FT pt t) eq_refl k1 i1) 0 (le_n 0)) =
  DenExp_ext t 0
    (eq_rect t
       (fun y : VTyp =>
        forall v1 : sVTyp y,
        findE fenv x = Some (FC tenv0 (existT ValueI y (Cst y v1)) e) ->
        FT (PT (map snd tenv0)) y = FT pt t -> y = t -> sVTyp t * ReflectL.W)
       (fun (v1 : sVTyp t)
          (_ : findE fenv x = Some (FC tenv0 (existT ValueI t (Cst t v1)) e))
          (_ : FT (PT (map snd tenv0)) t = FT pt t) 
          (_ : t = t) => (v1, w2d)) t (eq_sym eq_refl) v k1
       (RelatedByEnv funFTyp fenv ftenv x (FC tenv0 v0 e) 
          (FT pt t) eq_refl k1 i1) eq_refl,
    existT (fun n2 : nat => n2 <= 0) 0 (Nat.le_0_l 0))).

    set (PP2 := SOS_Exp1 fenv env (Apply x (PS ls) e9) t s9a 0
    (ExpSoundness_ApplyX0_aux3 fenv ftenv tenv tenv0 x v0 e t eq_refl k1 e9 ls
       pt p0 env e0 s9a vvs2 uuB1 eq_refl w2d n2d sv9a uuC1 eq_refl m2 uu9
       JJ 0 (le_n 0)) =
  DenExp_ext t 0
    (eq_rect t
       (fun y : VTyp =>
        forall v1 : sVTyp y,
        findE fenv x = Some (FC tenv0 (existT ValueI y (Cst y v1)) e) ->
        FT (PT (map snd tenv0)) y = FT pt t -> y = t -> sVTyp t * ReflectL.W)
       (fun (v1 : sVTyp t)
          (_ : findE fenv x = Some (FC tenv0 (existT ValueI t (Cst t v1)) e))
          (_ : FT (PT (map snd tenv0)) t = FT pt t) 
          (_ : t = t) => (v1, w2d)) t (eq_sym eq_refl) v k1
       JJ eq_refl,
    existT (fun n2 : nat => n2 <= 0) 0 (Nat.le_0_l 0))).

    assert (PP1 = PP2) as E1.
    unfold PP2.
    rewrite HeqJJ.
    reflexivity.

    assert PP2.
    Focus 2.
    rewrite <- E1 in H.
    subst PP1.
    assumption.
    
    subst PP2.
    clear E1.
    clear PP1.

    simpl in JJ.
    subst pt.

    dependent destruction JJ.

    dependent destruction HeqJJ.

    simpl.

    assert (n2d = 0) as qq.
    intuition.

    assert (qq = min_zero n2d
                          (PrmsDecrease fenv env s9a w2d 0 n2d
                                        (PS ls) (PS (map Val vvs2)) uuC1))
           as E1.
    eapply proof_irrelevance.

    inversion E1; subst.
    dependent destruction E1.

    simpl.
    reflexivity.
Defined.    

Lemma ExpInterp_ApplyT0 (fenv : funEnv)
  (D : FEnvWT fenv) :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (e : Exp) (ps : Prms) (pt : PTyp) (t : VTyp) (p : Pure e)
    (i : IdFTyping ftenv x (FT pt t)) (p0 : PrmsTyping ftenv tenv ps pt),
  PInterpPrms fenv D 0 ftenv tenv ps pt p0 ->
  forall e0 : ExpTyping ftenv tenv e Nat,
  PInterpExp fenv D 0 ftenv tenv e Nat e0 ->
  PInterpExp fenv D 0 ftenv tenv (Apply x ps e) t
             (Apply_Typing ftenv tenv x e ps pt t p i p0 e0).
  destruct ps.
  eapply ExpInterp_Apply0.
Defined.

Lemma ExpInterp_ApplyTS (fenv : funEnv)
  (D : FEnvWT fenv) 
  (n : nat)
  (IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) 
          (t : VTyp) (k : ExpTyping ftenv tenv e t),
        PInterpExp fenv D n ftenv tenv e t k) :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (e : Exp) (ps : Prms) (pt : PTyp) (t : VTyp) (p : Pure e)
    (i : IdFTyping ftenv x (FT pt t)) (p0 : PrmsTyping ftenv tenv ps pt),
  PInterpPrms fenv D (S n) ftenv tenv ps pt p0 ->
  forall e0 : ExpTyping ftenv tenv e Nat,
  PInterpExp fenv D (S n) ftenv tenv e Nat e0 ->
  PInterpExp fenv D (S n) ftenv tenv (Apply x ps e) t
             (Apply_Typing ftenv tenv x e ps pt t p i p0 e0).
  destruct ps.
  eapply ExpInterp_ApplyS.
  assumption.
Defined.


(*****************************************************************)

(** MAIN *)
Lemma ExpInterpA (fenv: funEnv) (D: FEnvWT fenv) :
   forall (n: nat) (ftenv: funTC) (tenv: valTC)
          (e: Exp) (t: VTyp) 
          (k: ExpTyping ftenv tenv e t),
     PInterpExp fenv D n ftenv tenv e t k.
Proof.
  intro n.
  induction n.
  eapply (PInterp_ExpTyping_mut fenv D 0).
  - eapply (ExpInterp_Val fenv D 0).
  - eapply (ExpInterp_Var fenv D 0).
  - eapply (ExpInterp_BindN fenv D 0).
  - eapply (ExpInterp_BindS fenv D 0).  
  - eapply (ExpInterp_BindMS fenv D 0).
  - eapply (ExpInterp_IfThenElse fenv D 0).
  - eapply (ExpInterp_ApplyT0 fenv D).
  - eapply (ExpInterp_Call0 fenv D).
  - eapply (ExpInterp_Modify fenv D).
  - eapply (ExpInterp_PrmsNil fenv D 0).
  - eapply (ExpInterp_Prms fenv D 0).
  - eapply (PInterp_ExpTyping_mut fenv D (S n)).
    + eapply (ExpInterp_Val fenv D (S n)).
    + eapply (ExpInterp_Var fenv D (S n)).
    + eapply (ExpInterp_BindN fenv D (S n)).
    + eapply (ExpInterp_BindS fenv D (S n)).
    + eapply (ExpInterp_BindMS fenv D (S n)).
    + eapply (ExpInterp_IfThenElse fenv D (S n)).
    + eapply (ExpInterp_ApplyTS fenv D n).
      exact IHn.
    + eapply (ExpInterp_CallS fenv D n).
      exact IHn.
    + eapply (ExpInterp_Modify fenv D (S n)).
    + eapply (ExpInterp_PrmsNil fenv D (S n)).
    + eapply (ExpInterp_Prms fenv D (S n)).
Defined.
    
 

Lemma Prms2ExpClos (fenv: funEnv) (env: valEnv)
         (s s': W) (n n': nat) (e: Exp) (v: Value) :
      (PClosure fenv env (Conf Prms s n (PS [e]))
                (Conf Prms s' n' (PS [Val v]))) ->
       EClosure fenv env (Conf Exp s n e)
                (Conf Exp s' n' (Val v)).
  intros.
  dependent induction X.
  constructor.
  destruct p2.
  inversion p; subst.
  inversion X0.
  econstructor.
  exact X0.
  eapply IHX.
  reflexivity.
  reflexivity.
Defined.

  
Lemma PInterpPrms_aux1_lemma
  (fenv : funEnv)
  (n : nat)
  (ftenv : funTC)
  (tenv : valTC) (t: VTyp) (e: Exp) :
    (FEnvTyping fenv ftenv ->
       forall env : valEnv,
       EnvTyping env tenv ->
       forall n' : nat,
         n' <= n -> forall s : InterprBaseL.W,
           SoundPrms fenv env (PS [e]) (PT [t]) s n') ->
  (FEnvTyping fenv ftenv ->
    forall env : valEnv,
    EnvTyping env tenv ->
    forall n' : nat,
      n' <= n -> forall s : InterprBaseL.W, SoundExp fenv env e t s n').
   intros.
   specialize (X H env H0 n' H1 s).
   unfold SoundPrms in X.
   unfold SoundExp.
   destruct X as [es X].
   destruct X as [vs m X].
   destruct X as [k X].
   destruct X as [ww X].
   inversion k; subst.
   inversion X1; subst.
   unfold isValueList2T in m.
   destruct vs.
   simpl in m.
   inversion m.
   inversion m; subst.
   simpl in m.
   rewrite <- H4 in *.
   econstructor 1 with (x := v).
   inversion k; subst.
   inversion X2; subst.
   exact H6.
   econstructor 1 with (x := ww).

   eapply Prms2ExpClos.
   assumption.
Defined.   


Lemma PInterpPrms_aux2_lemma
  (fenv : funEnv)
  (n : nat)
  (ftenv : funTC)
  (tenv : valTC) (t: VTyp) (e: Exp) :
    (FEnvTyping fenv ftenv ->
       valTC_Trans tenv ->
       forall n' : nat,
       n' <= n ->
       InterprBaseL.W -> PTyp_TRN (PT [t]) *
                         InterprBaseL.W * {n1 : nat & n1 <= n'})
    ->
    (FEnvTyping fenv ftenv ->
    valTC_Trans tenv ->
    forall n' : nat,
    n' <= n ->
    InterprBaseL.W -> sVTyp t * InterprBaseL.W * {n1 : nat & n1 <= n'}).
   intros.
   specialize (X H X0 n' H0 X1).
   destruct X as [spt ww].
   destruct spt as [spt1 s1].
   split.
   split.
   unfold PTyp_TRN in spt1.
   unfold PTyp_ListTrans in spt1.
   simpl in spt1.
   exact (fst spt1).
   exact s1.
   exact ww.
Defined.   


Lemma eval_vls_aux3 (v: Value) :
  forall (kp2: vlsTyping [v] [valueVTyp v]),    
     Eval_vls [valueVTyp v] [v] kp2 
     = (Value_Trans v, tt).
  simpl in *.

  unfold valueVTyp in *.
  intro.

  dependent destruction kp2.
  simpl in *.
  dependent destruction v0.
  dependent destruction kp2.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  destruct v.
  destruct v.
  simpl.
  reflexivity.
Defined.


Lemma PInterpPrms_IH_lemma (fenv : funEnv)
  (D : FEnvWT fenv)
  (n : nat)
  (IHn : forall (ftenv : funTC) (tenv : valTC) (ps : Prms) 
          (pt : PTyp) (k : PrmsTyping ftenv tenv ps pt),
        PInterpPrms fenv D n ftenv tenv ps pt k) :
  forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp)
         (k : ExpTyping ftenv tenv e t), PInterpExp fenv D n ftenv tenv e t k.
  unfold PInterpExp, PInterpPrms in *.
  intros.
  set (ps := PS [e]).
  set (pt := PT [t]).
  assert (PrmsTyping ftenv tenv ps pt) as X.
  econstructor.
  assumption.
  constructor.
  specialize (IHn ftenv tenv ps pt X m1).
  destruct IHn as [I1 IH].
  destruct IH as [I2 IH].
   
  econstructor 1 with (x := PInterpPrms_aux1_lemma fenv n ftenv tenv t e I1).
  econstructor 1 with (x := PInterpPrms_aux2_lemma fenv n ftenv tenv t e I2).

  intros.
  specialize (IH s0 n0 q env m2 senv kk).

  unfold PInterpPrms_aux1_lemma.
  destruct (I1 m1 env m2 n0 q s0).
  simpl.
  destruct s.
  destruct p.
  destruct s.
  inversion i; subst.
  destruct x1.
  unfold EnvTyping in m1, m2.
  unfold MatchEnvs in m1, m2.
  inversion m1; subst.

  simpl in IH.

  rewrite <- eq_rect_eq in IH.
  
  unfold PInterpPrms_aux2_lemma.

  destruct (I2 m1 senv n0 q s0).
  simpl in IH.
  unfold DenPrms_ext in IH.
  destruct p1.
  destruct s.
  simpl in IH.
  inversion IH; subst.

  simpl.

  unfold f_equal.
  simpl.
  unfold SOS_Exp1.
  simpl.

  clear IH.

  generalize (matchListsAux02_T (funEnv2funTC fenv) (valEnv2valTC env) 
                                [t] (map Val x0) x0 eq_refl p).

  assert ([t] = (map snd [(x0,t)])) as E2.
  simpl.
  reflexivity.

  intros.
  subst ps.
  subst pt.
  simpl.

  inversion p; subst.
  destruct x0.
  simpl in H2.
  inversion H2.
  simpl in H2.
  inversion H2; subst.
  inversion X1; subst.

  symmetry in H3.
  eapply map_eq_nil with (f:=Val) in H3.
  inversion H3; subst.
  simpl.
  
  dependent destruction p.
  
  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.

  dependent destruction p.

  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.

  unfold isValueList2T in i.
  dependent destruction i.

  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.

  simpl.
  unfold FEnvTyping in m1.
  unfold MatchEnvs in m1.
  inversion m1; subst.
  simpl.
  
  unfold eq_ind_r.
  unfold eq_ind.
  unfold eq_rect.
  simpl.
  dependent destruction e1.

  simpl.
  unfold vlsTyping in v.
  
  unfold VTyping in v1.
  inversion v1; subst.
  unfold DenExp_ext.
  simpl.

  rewrite eval_vls_aux3.
  simpl.
  reflexivity.
Defined.  


(** MAIN *)
Lemma PrmsInterpA (fenv: funEnv) (D: FEnvWT fenv) :
   forall (n: nat) (ftenv: funTC) (tenv: valTC)
          (ps: Prms) (pt: PTyp) 
          (k: PrmsTyping ftenv tenv ps pt),
     PInterpPrms fenv D n ftenv tenv ps pt k.
Proof.
  intro n.
  induction n.
  eapply (PInterp_PrmsTyping_mut fenv D 0).
  - eapply (ExpInterp_Val fenv D 0).
  - eapply (ExpInterp_Var fenv D 0).
  - eapply (ExpInterp_BindN fenv D 0).
  - eapply (ExpInterp_BindS fenv D 0).  
  - eapply (ExpInterp_BindMS fenv D 0).
  - eapply (ExpInterp_IfThenElse fenv D 0).
  - eapply (ExpInterp_ApplyT0 fenv D).
  - eapply (ExpInterp_Call0 fenv D).
  - eapply (ExpInterp_Modify fenv D).
  - eapply (ExpInterp_PrmsNil fenv D 0).
  - eapply (ExpInterp_Prms fenv D 0).
  - eapply (PInterp_PrmsTyping_mut fenv D (S n)).
    + eapply (ExpInterp_Val fenv D (S n)).
    + eapply (ExpInterp_Var fenv D (S n)).
    + eapply (ExpInterp_BindN fenv D (S n)).
    + eapply (ExpInterp_BindS fenv D (S n)).
    + eapply (ExpInterp_BindMS fenv D (S n)).
    + eapply (ExpInterp_IfThenElse fenv D (S n)).
    + eapply (ExpInterp_ApplyTS fenv D n).
      eapply (PInterpPrms_IH_lemma fenv D n).
      auto.      
    + eapply (ExpInterp_CallS fenv D n).
      eapply (PInterpPrms_IH_lemma fenv D n).
      auto.
    + eapply (ExpInterp_Modify fenv D (S n)).
    + eapply (ExpInterp_PrmsNil fenv D (S n)).
    + eapply (ExpInterp_Prms fenv D (S n)).
Defined.  

(* SOS interpreter for Exp *)
Lemma SOS_ExpInterpA (fenv: funEnv) (D: FEnvWT fenv) :
   forall (n: nat) (ftenv: funTC) (tenv: valTC)
          (e: Exp) (t: VTyp) 
          (k: ExpTyping ftenv tenv e t),
   forall (m1: FEnvTyping fenv ftenv)
            (env: valEnv) (m2: EnvTyping env tenv)
                       (n': nat) (q1: n' <= n) (s: W),
                SoundExp fenv env e t s n'.
Proof.
 intros. 
 eapply (projT1 (ExpInterpA fenv D n ftenv tenv e t k m1)).
 assumption.
 assumption.
 assumption.
Defined. 

(* SOS interpreter for Prms *)
Lemma SOS_PrmsInterpA (fenv: funEnv) (D: FEnvWT fenv) :
   forall (n: nat) (ftenv: funTC) (tenv: valTC)
          (ps: Prms) (pt: PTyp) 
          (k: PrmsTyping ftenv tenv ps pt),
   forall (m1: FEnvTyping fenv ftenv)
                       (env: valEnv) (m2: EnvTyping env tenv)
                       (n': nat) (q1: n' <= n) (s: W),
                SoundPrms fenv env ps pt s n'.
Proof.
 intros. 
 eapply (projT1 (PrmsInterpA fenv D n ftenv tenv ps pt k m1)).
 assumption.
 assumption.
 assumption.
Defined. 


(* Reflective interpreter for Exp *)
Lemma Refl_ExpInterpA (fenv: funEnv) (D: FEnvWT fenv) :
   forall (n: nat) (ftenv: funTC) (tenv: valTC)
          (e: Exp) (t: VTyp) 
          (k: ExpTyping ftenv tenv e t),
    forall (m1: FEnvTyping fenv ftenv)
                    (senv: valTC_Trans tenv)
                       (n': nat) (q2: n' <= n), W -> 
                        (sVTyp t * W) * sigT (fun n1 => n1 <= n').
Proof.
  intros.
  eapply (projT1 (projT2 (ExpInterpA fenv D n ftenv tenv e t k m1))).
  assumption.
  assumption.
  assumption.
  assumption.
Defined. 

(* Reflective interpreter for Prms *)
Lemma Refl_PrmsInterpA (fenv: funEnv) (D: FEnvWT fenv) :
   forall (n: nat) (ftenv: funTC) (tenv: valTC)
          (ps: Prms) (pt: PTyp) 
          (k: PrmsTyping ftenv tenv ps pt),
   forall (m1: FEnvTyping fenv ftenv)
          (senv: valTC_Trans tenv) 
          (n': nat) (q2: n' <= n), W -> 
                (PTyp_TRN pt * W) * sigT (fun n1 => n1 <= n').
Proof.
 intros. 
 eapply (projT1 (projT2 (PrmsInterpA fenv D n ftenv tenv ps pt k m1))).
 assumption.
 assumption.
 assumption.
 assumption.
Defined. 


(* Interpreter equality for Exp *)
Lemma ExpSOSRefl_Eq (fenv: funEnv) (D: FEnvWT fenv) :
   forall (n: nat) (ftenv: funTC) (tenv: valTC)
          (e: Exp) (t: VTyp) 
          (k: ExpTyping ftenv tenv e t),
   forall  (m1: FEnvTyping fenv ftenv),  
   forall (s0: W) (n0: nat) (q: n0 <= n)               
         (env: valEnv) (m2: EnvTyping env tenv)
         (senv: valTC_Trans tenv)                  
         (kk: ValEnv_agree tenv env m2 senv),
     
     SOS_Exp1 fenv env e t s0 n0 (SOS_ExpInterpA fenv D n ftenv tenv e t k
                                 m1 env m2 n0 q s0) =
     DenExp_ext t n0 (Refl_ExpInterpA fenv D n ftenv tenv e t k
                                      m1 senv n0 q s0).
Proof.
  intros.
  eapply (projT2 (projT2 (ExpInterpA fenv D n ftenv tenv e t k m1))).
  assumption.
Defined.

(* Interpreter equality for Prms *)
Lemma PrmsSOSRefl_Eq (fenv: funEnv) (D: FEnvWT fenv) :
   forall (n: nat) (ftenv: funTC) (tenv: valTC)
          (ps: Prms) (pt: PTyp) 
          (k: PrmsTyping ftenv tenv ps pt),
   forall  (m1: FEnvTyping fenv ftenv),  
   forall (s0: W) (n0: nat) (q: n0 <= n)               
         (env: valEnv) (m2: EnvTyping env tenv)
         (senv: valTC_Trans tenv)                  
         (kk: ValEnv_agree tenv env m2 senv),
     
     SOS_Prms fenv env ps pt s0 n0
              (SOS_PrmsInterpA fenv D n ftenv tenv ps pt k
                                 m1 env m2 n0 q s0) =
     DenPrms_ext pt n0
              (Refl_PrmsInterpA fenv D n ftenv tenv ps pt k
                                      m1 senv n0 q s0).
Proof.
  intros.
  eapply (projT2 (projT2 (PrmsInterpA fenv D n ftenv tenv ps pt k m1))).
  assumption.
Defined.


End Interpret.

  
