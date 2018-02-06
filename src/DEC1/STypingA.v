(* DEC1 language development.
   Paolo Torrini, 
   Universite' Lille-1 - CRIStAL-CNRS
*)
(* type uniqueness *)

Require Export Basics.

Require Export EnvLibA.
Require Export RelLibA.

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
Require Import SReducA.
Require Import DetermA.

Require Import Coq.Logic.EqdepFacts.

Module STyping (IdT: IdModType) <: IdModType.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module DetermI := Determ IdT.
Export DetermI.

  
(******* strong typing properties **************************)

Lemma prmsTyping_aux4 (ftenv: funTC) (tenv: valTC)
        (fenv: funEnv) (env: valEnv) (es: list Exp) (vs: list Value)
        (ts: list VTyp) (s0 s1: W) :
    MatchEnvsT FunTyping fenv ftenv ->
    MatchEnvsT ValueTyping env tenv ->
    PrmsTyping ftenv tenv fenv (PS es) (PT ts) -> 
    PrmsClosure fenv env (Conf Prms s0 (PS es))
        (Conf Prms s1 (PS (map Val vs))) -> 
    vlsTyping vs ts.
  intros.
  assert (vs = extractPRunValue ftenv tenv fenv (PS es) (PT ts)
                                X1 X env X0 s0).
  eapply (proj2 (PEvalElim ftenv tenv fenv (PS es) (PT ts)
                                X1 X env X0 s0 s1 vs _)).
  rewrite H.
  assert (PrmsTyping emptyE emptyE emptyE
    (PS
       (projT1
          (PrmsEval ftenv tenv fenv (PS es) (PT ts) X1 X env X0 s0)))
    (PT ts)).
  exact (extractPRunTyping ftenv tenv fenv (PS es) (PT ts)
                                X1 X env X0 s0).
  assert (PrmsTyping ftenv tenv fenv
    (PS
       (projT1
          (PrmsEval ftenv tenv fenv (PS es) (PT ts) X1 X env X0 s0)))
    (PT ts)).
  eapply weakenPrmsTyping in X3. 
  exact X3.
  constructor.
  auto.
  clear X3.
  simpl in *.
  generalize (extractPRunCons ftenv tenv fenv (PS es)
                              (PT ts) X1 X env X0 s0).
  intros.
  unfold extractPRunEValue in H0.
  rewrite H0 in X4.
  eapply matchListsAux02_T.
  instantiate (1:= map Val vs).
  rewrite <- H.
  constructor.
  auto.
  rewrite <- H in X4.
  exact X4.
  Unshelve.
  auto.
Defined.  


(************************************************************************)


Lemma ValueStrongTyping :
  forall (v: Value) (t1: VTyp),   
     ValueTyping v t1 -> 
  forall t2: VTyp,  
    ValueTyping v t2 -> 
        t1 = t2.
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  subst T T0.
  rewrite H1 in H3.
  assert (H2 = H4).
  eapply loc_pi.
  subst.
  destruct t1.
  destruct t2.
  simpl in *.
  revert H1.
  revert H0.
  revert v1.
  rewrite <- H3.
  intros.
  assert (v0 = v1).
  eapply loc_pi.
  subst.
  auto.
Defined.  
  
Lemma IdStrongTyping :
  forall (tenv: valTC) (x: Id) (t1: VTyp),   
     IdTyping tenv x t1 -> 
  forall t2: VTyp,  
    IdTyping tenv x t2 -> 
        t1 = t2.
Proof.
  intros.
  inversion X; subst.
  inversion X0; subst.
  inversion X1; subst.
  inversion X2; subst.
  rewrite H in H0.
  injection H0.
  auto.
Defined.  


Lemma EnvStrongTyping :
  forall (env: valEnv) (tenv1: valTC),   
     EnvTyping env tenv1 -> 
  forall tenv2: valTC,  
    EnvTyping env tenv2 -> 
        tenv1 = tenv2.
Proof.
  intros.
  dependent induction env.
  inversion X; subst.
  inversion X0; subst.
  auto.
  inversion X; subst.
  inversion X0; subst.
  assert (ls2 = ls0).
  eapply IHenv.
  auto.
  auto.
  assert (v2 = v3).
  eapply ValueStrongTyping.
  eauto.
  auto.
  rewrite H.
  rewrite H0.
  auto.
Defined.  
  

Definition UniEType :=
  fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
      (e: Exp) (t1: VTyp) (k: ExpTyping ftenv tenv fenv e t1) => 
  FEnvTyping fenv ftenv ->     
  forall (t2: VTyp) (ftenv0: funTC),
    FEnvTyping fenv ftenv0 ->       
    ExpTyping ftenv0 tenv fenv e t2 -> 
        t1 = t2.


Definition UniPType :=
  fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
      (ps: Prms) (pt1: PTyp) (k: PrmsTyping ftenv tenv fenv ps pt1) => 
    FEnvTyping fenv ftenv ->
    forall (pt2: PTyp) (ftenv0: funTC),
      FEnvTyping fenv ftenv0 ->  
      PrmsTyping ftenv0 tenv fenv ps pt2 -> 
        pt1 = pt2.


Definition UniQFType :=
  fun (ftenv: funTC) (fenv: funEnv) 
      (qf: QFun) (ft1: FTyp) (k: QFunTyping ftenv fenv qf ft1) => 
    FEnvTyping fenv ftenv ->     
    forall (ft2: FTyp) (ftenv0: funTC),
    FEnvTyping fenv ftenv0 ->  
      QFunTyping ftenv0 fenv qf ft2 -> 
        ft1 = ft2.


Definition UniETypeW (ftenv: funTC)
                      (tenv: valTC) (fenv: funEnv)
                      (e: Exp) (t1: VTyp) := 
  ExpTyping ftenv tenv fenv e t1 ->  
  FEnvTyping fenv ftenv ->     
  forall (t2: VTyp) (ftenv0: funTC),
    FEnvTyping fenv ftenv0 ->       
    ExpTyping ftenv0 tenv fenv e t2 -> 
        t1 = t2.


Definition UniFTypeS :=
  fun (f: Fun) (ft1: FTyp) (k: FunTyping f ft1) => 
    forall (ft2: FTyp),  
      FunTyping f ft2 -> 
        ft1 = ft2.


Definition UniFType :=
  fun (f: Fun) (ft: FTyp) (k: FunTyping f ft) => 
   (forall (fps: valTC) (t: VTyp),
    ft = FT fps t ->      
    forall (ftenv: funTC) (i: nat) (fenv: funEnv) 
           (x: Id) (e0 e1: Exp),
       FEnvTyping fenv ftenv ->      
       f = FC fenv fps e0 e1 x i -> 
       match i with 
       | 0 => UniETypeW ftenv fps fenv e0 t
       | S j => UniETypeW (updateE ftenv x ft) fps
                (updateE fenv x (FC fenv fps e0 e1 x j)) e1 t 
       end).



Definition ExpTypingUni_rect :=
  ExpTyping_str_rect UniFType UniQFType UniEType UniPType.


Lemma ExpStrongTyping :
  forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (e: Exp) (t1: VTyp),   
      ExpTyping ftenv tenv fenv e t1 -> 
      FEnvTyping fenv ftenv ->
  forall (t2: VTyp) (ftenv0: funTC),
    FEnvTyping fenv ftenv0 ->  
    ExpTyping ftenv0 tenv fenv e t2 -> 
        t1 = t2.
Proof.
eapply ExpTypingUni_rect.
- (* SLL *)
  unfold Par_SSL, UniEType.
  intros.
  constructor.
- (* SLL *)
  unfold Par_SSL, UniEType.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSA *)  
  unfold Par_SSA, UniFType.
  constructor.
- unfold Par_SSA, UniFType.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSB *)
  unfold Par_SSB, Par_SSA, UniFType.
  intros.
  econstructor.
  exact m0.
  exact m1.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
- (* Par_F *)
  unfold UniFType, UniETypeW, UniEType.
  intros.
  inversion H0; subst.
  inversion H1; subst. 
  intros.
  eapply H.
  auto.
  Focus 2.
  eauto.
  auto.
- (* Par_F *)
  unfold UniFType, UniETypeW, UniEType.
  intros ftenv tenv fenv.
  intros e0 e1 x n t.
  intros K1 K2 K3 HP1 HP2.
  intros fps t0 E3.
  intros ftenv1 i fenv1 x0 e2 e3 K4 E4.
  inversion E3; subst.
  inversion E4; subst.
  intros.
  eapply HP1.
  eapply updateFEnvLemma.
  assumption.
  assumption.
  eassumption.
  assumption.
- (* Par_Q - QF *)
  unfold UniQFType, UniFType, UniEType, UniETypeW.
  intros.
  inversion X1; subst.
  destruct ft as [fps t].
  specialize (H fps t eq_refl).
  inversion k; subst.
  + inversion X2; subst.
    specialize (H ftenv1 0 fenv0 x e0 e1 X3 eq_refl).  
    simpl in *.
    assert (t = t0).
    eapply H.
    auto.
    auto.
    Focus 2.
    eassumption.
    auto.
    rewrite H0.
    auto.
  + inversion X2; subst.
    subst ftenv' fenv'.
    subst ftenv'0 fenv'0. (* to compare X5 and X8 *)
    specialize (H ftenv1
                  (S n) fenv0 x e0 e1 X3 eq_refl).  
    simpl in *.
    assert (t = t0).
    eapply H.
    auto.
    eapply updateFEnvLemma.
    auto.
    auto.
    Focus 2.
    eauto.
    eapply updateFEnvLemma.
    auto.
    auto.
    rewrite H0.
    auto.

- (* Par_Q - FVar *)  
  unfold  UniQFType, UniFType, UniEType, UniETypeW, Par_SSB, Par_SSA.
  intros.  
  inversion X; subst.
  clear X.
  clear X3 X4.
  destruct ft as [fps t].
  specialize (H1 fps t eq_refl).  
  inversion X2; subst.
  destruct ft2.
  destruct f.

  inversion m; subst.
  inversion X3; subst.
  
  +
    inversion X; subst.
    rewrite H0 in H4.
   
(***)    
    assert (f0 = FC fenv fps e0 e1 x0 0).
    eapply (envAppendCompare FunTyping ls0 ls8 ls1 ls3). 
    eauto.
    eauto.
    eauto.
    auto.
    auto.
        
    rewrite H5 in *.
  
    specialize (H1 ftenv).  
    specialize (H1 0 fenv x0 e0 e1). 
    specialize (H1 X6 eq_refl).
    simpl in *.
    inversion X8; subst.

    assert (t = ret_type).
    eapply H1. 
    auto.
    auto.
    Focus 2.
    eauto.
    auto.
    rewrite H5.
    auto.
    
  + inversion X; subst.
    rewrite H0 in H4.

    assert (f0 = FC fenv fps e0 e1 x0 (S n0)).
    eapply (envAppendCompare FunTyping ls0 ls8 ls1 ls3). 
    eauto.
    eauto.
    eauto.
    auto.
    auto.

    rewrite H5 in *.

    specialize (H1 ftenv).  
    specialize (H1 (S n0) fenv x0 e0 e1). 
    specialize (H1 X6 eq_refl).
    simpl in *.
    inversion X9; subst.

    assert (t = ret_type).
    eapply H1. 
    auto.
    eapply updateFEnvLemma.
    auto.
    auto.
    Focus 2.
    eauto.
    subst ftenv'0.
    eapply updateFEnvLemma.
    auto.
    auto.
    rewrite H5.
    auto.
    
- (* modify *)
  unfold UniEType.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q K H0 t ftenv0 H0' X.
  inversion X; subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.  
  assert (VT4 = VT1).
  eapply loc_pi.
  subst.
  assert (VT5 = VT2).
  eapply loc_pi.
  subst.
  clear XF2.
  reflexivity.
  (* return *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  inversion X2; subst.
  inversion k; subst.
  eapply ValueStrongTyping.
  eauto.
  eauto.
  inversion k; subst.
  eapply IdStrongTyping.
  eauto.
  auto.
(* bindN *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  eauto.
  auto.
(* bindS *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  subst tenv'.
  assert (t1 = t3).
  eapply H.
  auto.
  Focus 2.
  eauto.
  auto.
  rewrite H1.
  eauto.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H.
  eapply overrideEnvLemmaT.
  assumption.
  assumption.
  Focus 2.
  assert (tenvP = tenvP0).
  eapply EnvStrongTyping.
  eauto.
  auto.
  rewrite H0.
  eauto.
  eapply overrideEnvLemmaT.
  auto.
  auto.
- unfold UniEType, UniQFType, UniPType.
  intros.  
  inversion X1; subst.
  assert (FT fps t = FT fps0 t2).
  eapply H.
  auto.
  eauto.
  auto.
  injection H1.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply ValueStrongTyping.
  eauto.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  eauto.
  auto.
- unfold UniEType, Par_SSL, UniPType.
  intros.
  dependent induction X; subst.
  inversion X2; subst.
  inversion X; subst.
  auto.
  destruct pt2.
  destruct ts.
  + inversion X2; subst.
    inversion X3.
  + inversion m; subst.
    inversion X2; subst.
    inversion X5; subst.
    assert (PT bbs = PT ts).
    {*  eapply IHX.
      auto.
      auto.
      Focus 2.
      econstructor.
      eauto.
      auto.
   }   
   injection H.
   intro.
   assert (b = v).
   {* eapply p0.
      auto.
      Focus 2.
      eauto.
      auto.
   }
   rewrite H0.
   rewrite H1.
   auto.
Defined.   



Definition PrmsTypingUni_rect :=
  PrmsTyping_str_rect UniFType UniQFType UniEType UniPType.


Lemma PrmsStrongTyping :
  forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (ps: Prms) (pt: PTyp)   
         (k: PrmsTyping ftenv tenv fenv ps pt),  
         UniPType ftenv tenv fenv ps pt k.
Proof.
eapply PrmsTypingUni_rect.
- (* SLL *)
  unfold Par_SSL, UniEType.
  intros.
  constructor.
- (* SLL *)
  unfold Par_SSL, UniEType.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSA *)  
  unfold Par_SSA, UniFType.
  constructor.
- unfold Par_SSA, UniFType.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSB *)
  unfold Par_SSB, Par_SSA, UniFType.
  intros.
  econstructor.
  exact m0.
  exact m1.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
- (* Par_F *)
  unfold UniFType, UniETypeW, UniEType.
  intros.
  inversion H0; subst.
  inversion H1; subst. 
  intros.
  eapply H.
  auto.
  Focus 2.
  eauto.
  auto.
- (* Par_F *)
  unfold UniFType, UniETypeW, UniEType.
  intros ftenv tenv fenv.
  intros e0 e1 x n t.
  intros K1 K2 K3 HP1 HP2.
  intros fps t0 E3.
  intros ftenv1 i fenv1 x0 e2 e3 K4 E4.
  inversion E3; subst.
  inversion E4; subst.
  intros.
  eapply HP1.
  eapply updateFEnvLemma.
  assumption.
  assumption.
  eassumption.
  assumption.
- (* Par_Q - QF *)
  unfold UniQFType, UniFType, UniEType, UniETypeW.
  intros.
  inversion X1; subst.
  destruct ft as [fps t].
  specialize (H fps t eq_refl).
  inversion k; subst.
  + inversion X2; subst.
    specialize (H ftenv1 0 fenv0 x e0 e1 X3 eq_refl).  
    simpl in *.
    assert (t = t0).
    eapply H.
    auto.
    auto.
    Focus 2.
    eassumption.
    auto.
    rewrite H0.
    auto.
  + inversion X2; subst.
    subst ftenv' fenv'.
    subst ftenv'0 fenv'0. (* to compare X5 and X8 *)
    specialize (H ftenv1
                  (S n) fenv0 x e0 e1 X3 eq_refl).  
    simpl in *.
    assert (t = t0).
    eapply H.
    auto.
    eapply updateFEnvLemma.
    auto.
    auto.
    Focus 2.
    eauto.
    eapply updateFEnvLemma.
    auto.
    auto.
    rewrite H0.
    auto.

- (* Par_Q - FVar *)  
  unfold  UniQFType, UniFType, UniEType, UniETypeW, Par_SSB, Par_SSA.
  intros.  
  inversion X; subst.
  clear X.
  clear X3 X4.
  destruct ft as [fps t].
  specialize (H1 fps t eq_refl).  
  inversion X2; subst.
  destruct ft2.
  destruct f.

  inversion m; subst.
  inversion X3; subst.
  
  +
    inversion X; subst.
    rewrite H0 in H4.
    
(***)    
    assert (f0 = FC fenv fps e0 e1 x0 0).
    eapply (envAppendCompare FunTyping ls0 ls8 ls1 ls3). 
    eauto.
    eauto.
    eauto.
    auto.
    auto.
    
    rewrite H5 in *.
  
    specialize (H1 ftenv).  
    specialize (H1 0 fenv x0 e0 e1). 
    specialize (H1 X6 eq_refl).
    simpl in *.
    inversion X8; subst.

    assert (t = ret_type).
    eapply H1. 
    auto.
    auto.
    Focus 2.
    eauto.
    auto.
    rewrite H5.
    auto.
    
  + inversion X; subst.
    rewrite H0 in H4.

    assert (f0 = FC fenv fps e0 e1 x0 (S n0)).
    eapply (envAppendCompare FunTyping ls0 ls8 ls1 ls3). 
    eauto.
    eauto.
    eauto.
    auto.
    auto.

    rewrite H5 in *.

    specialize (H1 ftenv).  
    specialize (H1 (S n0) fenv x0 e0 e1). 
    specialize (H1 X6 eq_refl).
    simpl in *.
    inversion X9; subst.

    assert (t = ret_type).
    eapply H1. 
    auto.
    eapply updateFEnvLemma.
    auto.
    auto.
    Focus 2.
    eauto.
    subst ftenv'0.
    eapply updateFEnvLemma.
    auto.
    auto.
    rewrite H5.
    auto.
    
- (* modify *)
  unfold UniEType.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q K H0 t ftenv0 H0' X.
  inversion X; subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.  
  assert (VT4 = VT1).
  eapply loc_pi.
  subst.
  assert (VT5 = VT2).
  eapply loc_pi.
  subst.
  clear XF2.
  reflexivity.
  (* return *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  inversion X2; subst.
  inversion k; subst.
  eapply ValueStrongTyping.
  eauto.
  eauto.
  inversion k; subst.
  eapply IdStrongTyping.
  eauto.
  auto.
(* bindN *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  eauto.
  auto.
(* bindS *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  subst tenv'.
  assert (t1 = t3).
  eapply H.
  auto.
  Focus 2.
  eauto.
  auto.
  rewrite H1.
  eauto.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H.
  eapply overrideEnvLemmaT.
  assumption.
  assumption.
  Focus 2.
  assert (tenvP = tenvP0).
  eapply EnvStrongTyping.
  eauto.
  auto.
  rewrite H0.
  eauto.
  eapply overrideEnvLemmaT.
  auto.
  auto.
- unfold UniEType, UniQFType, UniPType.
  intros.  
  inversion X1; subst.
  assert (FT fps t = FT fps0 t2).
  eapply H.
  auto.
  eauto.
  auto.
  injection H1.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply ValueStrongTyping.
  eauto.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  eauto.
  auto.
- unfold UniEType, Par_SSL, UniPType.
  intros.
  dependent induction X; subst.
  inversion X2; subst.
  inversion X; subst.
  auto.
  destruct pt2.
  destruct ts.
  + inversion X2; subst.
    inversion X3.
  + inversion m; subst.
    inversion X2; subst.
    inversion X5; subst.
    assert (PT bbs = PT ts).
    {*  eapply IHX.
      auto.
      auto.
      Focus 2.
      econstructor.
      eauto.
      auto.
   }   
   injection H.
   intro.
   assert (b = v).
   {* eapply p0.
      auto.
      Focus 2.
      eauto.
      auto.
   }
   rewrite H0.
   rewrite H1.
   auto.
Defined.   


Definition QFunTypingUni_rect :=
  QFunTyping_str_rect UniFType UniQFType UniEType UniPType.


Lemma QFunStrongTyping :
  forall (ftenv: funTC) (fenv: funEnv)
         (qf: QFun) (ft: FTyp)  
         (k: QFunTyping ftenv fenv qf ft), 
     UniQFType ftenv fenv qf ft k.    
Proof.
eapply QFunTypingUni_rect.
- (* SLL *)
  unfold Par_SSL, UniEType.
  intros.
  constructor.
- (* SLL *)
  unfold Par_SSL, UniEType.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSA *)  
  unfold Par_SSA, UniFType.
  constructor.
- unfold Par_SSA, UniFType.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSB *)
  unfold Par_SSB, Par_SSA, UniFType.
  intros.
  econstructor.
  exact m0.
  exact m1.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
- (* Par_F *)
  unfold UniFType, UniETypeW, UniEType.
  intros.
  inversion H0; subst.
  inversion H1; subst. 
  intros.
  eapply H.
  auto.
  Focus 2.
  eauto.
  auto.
- (* Par_F *)
  unfold UniFType, UniETypeW, UniEType.
  intros ftenv tenv fenv.
  intros e0 e1 x n t.
  intros K1 K2 K3 HP1 HP2.
  intros fps t0 E3.
  intros ftenv1 i fenv1 x0 e2 e3 K4 E4.
  inversion E3; subst.
  inversion E4; subst.
  intros.
  eapply HP1.
  eapply updateFEnvLemma.
  assumption.
  assumption.
  eassumption.
  assumption.
- (* Par_Q - QF *)
  unfold UniQFType, UniFType, UniEType, UniETypeW.
  intros.
  inversion X1; subst.
  destruct ft as [fps t].
  specialize (H fps t eq_refl).
  inversion k; subst.
  + inversion X2; subst.
    specialize (H ftenv1 0 fenv0 x e0 e1 X3 eq_refl).  
    simpl in *.
    assert (t = t0).
    eapply H.
    auto.
    auto.
    Focus 2.
    eassumption.
    auto.
    rewrite H0.
    auto.
  + inversion X2; subst.
    subst ftenv' fenv'.
    subst ftenv'0 fenv'0. (* to compare X5 and X8 *)
    specialize (H ftenv1
                  (S n) fenv0 x e0 e1 X3 eq_refl).  
    simpl in *.
    assert (t = t0).
    eapply H.
    auto.
    eapply updateFEnvLemma.
    auto.
    auto.
    Focus 2.
    eauto.
    eapply updateFEnvLemma.
    auto.
    auto.
    rewrite H0.
    auto.

- (* Par_Q - FVar *)  
  unfold  UniQFType, UniFType, UniEType, UniETypeW, Par_SSB, Par_SSA.
  intros.  
  inversion X; subst.
  clear X.
  clear X3 X4.
  destruct ft as [fps t].
  specialize (H1 fps t eq_refl).  
  inversion X2; subst.
  destruct ft2.
  destruct f.

  inversion m; subst.
  inversion X3; subst.
  
  +
    inversion X; subst.
    rewrite H0 in H4.
    
(***)    
    assert (f0 = FC fenv fps e0 e1 x0 0).
    eapply (envAppendCompare FunTyping ls0 ls8 ls1 ls3). 
    eauto.
    eauto.
    eauto.
    auto.
    auto.
    
    rewrite H5 in *.
  
    specialize (H1 ftenv).  
    specialize (H1 0 fenv x0 e0 e1). 
    specialize (H1 X6 eq_refl).
    simpl in *.
    inversion X8; subst.

    assert (t = ret_type).
    eapply H1. 
    auto.
    auto.
    Focus 2.
    eauto.
    auto.
    rewrite H5.
    auto.
    
  + inversion X; subst.
    rewrite H0 in H4.

    assert (f0 = FC fenv fps e0 e1 x0 (S n0)).
    eapply (envAppendCompare FunTyping ls0 ls8 ls1 ls3). 
    eauto.
    eauto.
    eauto.
    auto.
    auto.
    
    rewrite H5 in *.

    specialize (H1 ftenv).  
    specialize (H1 (S n0) fenv x0 e0 e1). 
    specialize (H1 X6 eq_refl).
    simpl in *.
    inversion X9; subst.

    assert (t = ret_type).
    eapply H1. 
    auto.
    eapply updateFEnvLemma.
    auto.
    auto.
    Focus 2.
    eauto.
    subst ftenv'0.
    eapply updateFEnvLemma.
    auto.
    auto.
    rewrite H5.
    auto.
    
- (* modify *)
  unfold UniEType.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q K H0 t ftenv0 H0' X.
  inversion X; subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.  
  assert (VT4 = VT1).
  eapply loc_pi.
  subst.
  assert (VT5 = VT2).
  eapply loc_pi.
  subst.
  clear XF2.
  reflexivity.
  (* return *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  inversion X2; subst.
  inversion k; subst.
  eapply ValueStrongTyping.
  eauto.
  eauto.
  inversion k; subst.
  eapply IdStrongTyping.
  eauto.
  auto.
(* bindN *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  eauto.
  auto.
(* bindS *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  subst tenv'.
  assert (t1 = t3).
  eapply H.
  auto.
  Focus 2.
  eauto.
  auto.
  rewrite H1.
  eauto.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H.
  eapply overrideEnvLemmaT.
  assumption.
  assumption.
  Focus 2.
  assert (tenvP = tenvP0).
  eapply EnvStrongTyping.
  eauto.
  auto.
  rewrite H0.
  eauto.
  eapply overrideEnvLemmaT.
  auto.
  auto.
- unfold UniEType, UniQFType, UniPType.
  intros.  
  inversion X1; subst.
  assert (FT fps t = FT fps0 t2).
  eapply H.
  auto.
  eauto.
  auto.
  injection H1.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply ValueStrongTyping.
  eauto.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  eauto.
  auto.
- unfold UniEType, Par_SSL, UniPType.
  intros.
  dependent induction X; subst.
  inversion X2; subst.
  inversion X; subst.
  auto.
  destruct pt2.
  destruct ts.
  + inversion X2; subst.
    inversion X3.
  + inversion m; subst.
    inversion X2; subst.
    inversion X5; subst.
    assert (PT bbs = PT ts).
    {*  eapply IHX.
      auto.
      auto.
      Focus 2.
      econstructor.
      eauto.
      auto.
   }   
   injection H.
   intro.
   assert (b = v).
   {* eapply p0.
      auto.
      Focus 2.
      eauto.
      auto.
   }
   rewrite H0.
   rewrite H1.
   auto.
Defined.   

 
Definition FunTypingUni_rect :=
  FunTyping_str_rect UniFType UniQFType UniEType UniPType.


Lemma FunStrongTyping :
  forall (f: Fun) (ft: FTyp) (k: FunTyping f ft),
    UniFType f ft k.
Proof.
eapply FunTypingUni_rect.
- (* SLL *)
  unfold Par_SSL, UniEType.
  intros.
  constructor.
- (* SLL *)
  unfold Par_SSL, UniEType.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSA *)  
  unfold Par_SSA, UniFType.
  constructor.
- unfold Par_SSA, UniFType.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSB *)
  unfold Par_SSB, Par_SSA, UniFType.
  intros.
  econstructor.
  exact m0.
  exact m1.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
- (* Par_F *)
  unfold UniFType, UniETypeW, UniEType.
  intros.
  inversion H0; subst.
  inversion H1; subst. 
  intros.
  eapply H.
  auto.
  Focus 2.
  eauto.
  auto.
- (* Par_F *)
  unfold UniFType, UniETypeW, UniEType.
  intros ftenv tenv fenv.
  intros e0 e1 x n t.
  intros K1 K2 K3 HP1 HP2.
  intros fps t0 E3.
  intros ftenv1 i fenv1 x0 e2 e3 K4 E4.
  inversion E3; subst.
  inversion E4; subst.
  intros.
  eapply HP1.
  eapply updateFEnvLemma.
  assumption.
  assumption.
  eassumption.
  assumption.
- (* Par_Q - QF *)
  unfold UniQFType, UniFType, UniEType, UniETypeW.
  intros.
  inversion X1; subst.
  destruct ft as [fps t].
  specialize (H fps t eq_refl).
  inversion k; subst.
  + inversion X2; subst.
    specialize (H ftenv1 0 fenv0 x e0 e1 X3 eq_refl).  
    simpl in *.
    assert (t = t0).
    eapply H.
    auto.
    auto.
    Focus 2.
    eassumption.
    auto.
    rewrite H0.
    auto.
  + inversion X2; subst.
    subst ftenv' fenv'.
    subst ftenv'0 fenv'0. 
    specialize (H ftenv1
                  (S n) fenv0 x e0 e1 X3 eq_refl).  
    simpl in *.
    assert (t = t0).
    eapply H.
    auto.
    eapply updateFEnvLemma.
    auto.
    auto.
    Focus 2.
    eauto.
    eapply updateFEnvLemma.
    auto.
    auto.
    rewrite H0.
    auto.

- (* Par_Q - FVar *)  
  unfold  UniQFType, UniFType, UniEType, UniETypeW, Par_SSB, Par_SSA.
  intros.  
  inversion X; subst.
  clear X.
  clear X3 X4.
  destruct ft as [fps t].
  specialize (H1 fps t eq_refl).  
  inversion X2; subst.
  destruct ft2.
  destruct f.

  inversion m; subst.
  inversion X3; subst.
  
  +
    inversion X; subst.
    rewrite H0 in H4.
    
(***)    
    assert (f0 = FC fenv fps e0 e1 x0 0).
    eapply (envAppendCompare FunTyping ls0 ls8 ls1 ls3). 
    eauto.
    eauto.
    eauto.
    auto.
    auto.
       
    rewrite H5 in *.
  
    specialize (H1 ftenv).  
    specialize (H1 0 fenv x0 e0 e1). 
    specialize (H1 X6 eq_refl).
    simpl in *.
    inversion X8; subst.

    assert (t = ret_type).
    eapply H1. 
    auto.
    auto.
    Focus 2.
    eauto.
    auto.
    rewrite H5.
    auto.
    
  + inversion X; subst.
    rewrite H0 in H4.

    assert (f0 = FC fenv fps e0 e1 x0 (S n0)).
    eapply (envAppendCompare FunTyping ls0 ls8 ls1 ls3). 
    eauto.
    eauto.
    eauto.
    auto.
    auto.
    
    rewrite H5 in *.

    specialize (H1 ftenv).  
    specialize (H1 (S n0) fenv x0 e0 e1). 
    specialize (H1 X6 eq_refl).
    simpl in *.
    inversion X9; subst.

    assert (t = ret_type).
    eapply H1. 
    auto.
    eapply updateFEnvLemma.
    auto.
    auto.
    Focus 2.
    eauto.
    subst ftenv'0.
    eapply updateFEnvLemma.
    auto.
    auto.
    rewrite H5.
    auto.
    
- (* modify *)
  unfold UniEType.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q K H0 t ftenv0 H0' X.
  inversion X; subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.  
  assert (VT4 = VT1).
  eapply loc_pi.
  subst.
  assert (VT5 = VT2).
  eapply loc_pi.
  subst.
  clear XF2.
  reflexivity.
  (* return *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  inversion X2; subst.
  inversion k; subst.
  eapply ValueStrongTyping.
  eauto.
  eauto.
  inversion k; subst.
  eapply IdStrongTyping.
  eauto.
  auto.
(* bindN *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  eauto.
  auto.
(* bindS *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  subst tenv'.
  assert (t1 = t3).
  eapply H.
  auto.
  Focus 2.
  eauto.
  auto.
  rewrite H1.
  eauto.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H.
  eapply overrideEnvLemmaT.
  assumption.
  assumption.
  Focus 2.
  assert (tenvP = tenvP0).
  eapply EnvStrongTyping.
  eauto.
  auto.
  rewrite H0.
  eauto.
  eapply overrideEnvLemmaT.
  auto.
  auto.
- unfold UniEType, UniQFType, UniPType.
  intros.  
  inversion X1; subst.
  assert (FT fps t = FT fps0 t2).
  eapply H.
  auto.
  eauto.
  auto.
  injection H1.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply ValueStrongTyping.
  eauto.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  eauto.
  auto.
- unfold UniEType, Par_SSL, UniPType.
  intros.
  dependent induction X; subst.
  inversion X2; subst.
  inversion X; subst.
  auto.
  destruct pt2.
  destruct ts.
  + inversion X2; subst.
    inversion X3.
  + inversion m; subst.
    inversion X2; subst.
    inversion X5; subst.
    assert (PT bbs = PT ts).
    {*  eapply IHX.
      auto.
      auto.
      Focus 2.
      econstructor.
      eauto.
      auto.
   }   
   injection H.
   intro.
   assert (b = v).
   {* eapply p0.
      auto.
      Focus 2.
      eauto.
      auto.
   }
   rewrite H0.
   rewrite H1.
   auto.
Defined.   
   


Lemma UniFTypeLm0 (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft1: FTyp)
      (k: FunTyping (FC fenv tenv0 e0 e1 x 0) ft1) :
  UniFType (FC fenv tenv0 e0 e1 x 0) ft1 k ->
  UniFTypeS (FC fenv tenv0 e0 e1 x 0) ft1 k.
Proof.
  unfold UniFTypeS.
  unfold UniFType, UniFTypeS, UniETypeW.
  intros.
  destruct ft1 as [tenv t].
  destruct ft2.
  specialize (H tenv t eq_refl).
  inversion k; subst.
  inversion X; subst.
  rename prs_type into tenv.
  rename ret_type into t0.
  specialize (H ftenv 0 fenv x e0 e1 X0 eq_refl).
  simpl in *.
  specialize (H X1 X0).
  specialize (H t0 ftenv0 X2 X3).
  assert (t = t0).
  eapply ExpStrongTyping.
  exact X1.
  auto.
  exact X2.
  auto.
  rewrite H0.
  auto.
Defined.


Lemma UniFTypeLm0a (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft1 ft2: FTyp)
      (k: FunTyping (FC fenv tenv0 e0 e1 x 0) ft1) :
  UniFType (FC fenv tenv0 e0 e1 x 0) ft1 k ->
  FunTyping (FC fenv tenv0 e0 e1 x 0) ft2 -> ft1 = ft2.
  intros.
  eapply UniFTypeLm0.
  eauto.
  auto.
Defined.


Lemma UniFTypeLm0b (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft1 ft2: FTyp)
      (k1: FunTyping (FC fenv tenv0 e0 e1 x 0) ft1) 
      (k2: FunTyping (FC fenv tenv0 e0 e1 x 0) ft2) : ft1 = ft2.
  intros.
  inversion k1; subst.
  inversion k2; subst.
  assert (t = t0).
  eapply ExpStrongTyping.
  exact X0.
  auto.
  exact X1.
  auto.
  rewrite H.
  auto.
Defined.


Lemma UniFTypeLm1 (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft1: FTyp)
      (k1: FunTyping (FC fenv tenv0 e0 e1 x 1) ft1)
      (k0: FunTyping (FC fenv tenv0 e0 e1 x 0) ft1):
  UniFType (FC fenv tenv0 e0 e1 x 1) ft1 k1 ->
  UniFType (FC fenv tenv0 e0 e1 x 0) ft1 k0.
Proof.
  unfold UniFType.
  intros.
  destruct ft1 as [tenv1 t1].

  inversion H1; subst.
  inversion H0; subst.
  clear H1.
  clear H0.
  unfold UniETypeW in *.

  intros.
  eapply ExpStrongTyping.
  exact X0.
  auto.
  exact X2.
  auto.
Defined.


Lemma UniFTypeLmN (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (n: nat) (ft1: FTyp)
      (k1: FunTyping (FC fenv tenv0 e0 e1 x (S n)) ft1)
      (k0: FunTyping (FC fenv tenv0 e0 e1 x n) ft1):
  UniFType (FC fenv tenv0 e0 e1 x (S n)) ft1 k1 ->
  UniFType (FC fenv tenv0 e0 e1 x n) ft1 k0.
Proof.
  unfold UniFType.
  intros.
  destruct ft1 as [tenv1 t1].

  inversion H1; subst.
  inversion H0; subst.
  clear H1.
  clear H0.
  unfold UniETypeW in *.

  destruct i. 
  intros.
  eapply ExpStrongTyping.
  exact X0.
  auto.
  exact X2.
  auto.

  intros.
  inversion k0; subst.
  subst ftenv' fenv'.
  eapply ExpStrongTyping.
  exact X5.
  eapply updateFEnvLemma.
  auto.
  auto.
  eapply X2.
  auto.
Defined.

 

Lemma UniFTypeLm1b (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft1 ft2: FTyp)
      (k1: FunTyping (FC fenv tenv0 e0 e1 x 1) ft1) 
      (k2: FunTyping (FC fenv tenv0 e0 e1 x 0) ft2) : ft1 = ft2.
  intros.
  inversion k1; subst.
  inversion X1; subst.
  inversion k2; subst.
  subst ftenv' fenv'. 
  assert (t = t0).
  eapply ExpStrongTyping.
  exact X3.
  auto.
  exact X4.
  auto.
  rewrite H.
  auto.
Defined.



Lemma UniFTypeLmPb (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (n: nat) (ft1 ft2: FTyp)
      (k1: FunTyping (FC fenv tenv0 e0 e1 x n) ft1) 
      (k2: FunTyping (FC fenv tenv0 e0 e1 x (S n)) ft2) : ft1 = ft2.
Proof.
  intros.
  inversion k1; subst.
  
  - inversion k2; subst.
    inversion X3; subst.
    assert (t = t0).
    {+ eapply ExpStrongTyping.
       exact X0.
       auto.
       exact X4. 
       auto.
    }   
    rewrite H.
    auto.

  - inversion k2; subst.
    subst ftenv' fenv' ftenv'0 fenv'0.
    inversion X4; subst.
    subst ftenv' fenv'. 
    assert (t = t0).
    {+ eapply ExpStrongTyping.
       exact X0.
       eapply updateFEnvLemma.
       auto.
       auto.
       eapply updateFEnvLemma.
       eauto.
       eauto.
       auto.
    }
    rewrite H.
    auto.
Defined.    

Lemma UniFTypeLmNZE1 (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft: FTyp) :
  forall n: nat,
    FunTyping (FC fenv tenv0 e0 e1 x (S n)) ft ->
    sigT (fun ft0 => FunTyping (FC fenv tenv0 e0 e1 x n) ft0).
Proof.
  intros.
  inversion X; subst.  
  econstructor.
  eassumption.
Defined.



Lemma UniFTypeLmNZ1 (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft: FTyp) :
  forall n: nat,
    FunTyping (FC fenv tenv0 e0 e1 x (S n)) ft ->
    FunTyping (FC fenv tenv0 e0 e1 x n) ft.
Proof.
  intros.
  generalize X.
  eapply UniFTypeLmNZE1 in X.
  intro.
  destruct X as [ft0 X].
  eapply UniFTypeLmPb with (ft1:=ft0) (ft2:=ft) in X0.
  rewrite <- X0.
  auto.
  auto.
Defined.  


Lemma UniFTypeLmNZ (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft: FTyp) :
  forall n: nat,
    FunTyping (FC fenv tenv0 e0 e1 x n) ft ->
    FunTyping (FC fenv tenv0 e0 e1 x 0) ft.
Proof.
  intros.
  induction n.
  auto.
  eapply UniFTypeLmNZ1 in X.
  eapply IHn.
  auto.
Defined.



Lemma UniFTypeLm (f: Fun) (ft1 ft2: FTyp) (k: FunTyping f ft1) :
  UniFType f ft1 k ->
  FunTyping f ft2 -> ft1 = ft2.
Proof.
  destruct f.
  induction n.
  eapply UniFTypeLm0a.
  intros.
  inversion k; subst.
  eapply (IHn X2).
  eapply UniFTypeLmN.
  exact H.
  inversion X; subst.
  auto. 
Defined.  


Lemma UniqueFunType (f: Fun) (ft1 ft2: FTyp)
      (k1: FunTyping f ft1) 
      (k2: FunTyping f ft2) :  ft1 = ft2.
Proof.
  eapply UniFTypeLm with (k:=k1).
  eapply FunStrongTyping.
  eauto.
Defined.

Lemma UniFTypeLmNZ2 (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft: FTyp) :
  forall n: nat,
    sigT (fun ft0 => FunTyping (FC fenv tenv0 e0 e1 x (S n)) ft0) ->
    FunTyping (FC fenv tenv0 e0 e1 x n) ft ->
    FunTyping (FC fenv tenv0 e0 e1 x (S n)) ft.            
Proof.
  intros.
  destruct X as [ft0 X].
  generalize X as X1.
  intro.
  eapply UniFTypeLmNZ1 in X.
  eapply UniqueFunType with (ft2 := ft) in X.
  rewrite X in *.
  assumption.
  assumption. 
Defined.


Lemma UniqueFEnvType (fenv: funEnv) (ftenv1 ftenv2: funTC)
      (k1: FEnvTyping fenv ftenv1) 
      (k2: FEnvTyping fenv ftenv2) :  ftenv1 = ftenv2.
Proof.
  revert k1 k2.
  revert ftenv1 ftenv2.
  induction fenv.
  intros.
  inversion k1; subst.
  inversion k2; subst.
  auto.
  intros.
  inversion k1; subst.
  inversion k2; subst.
  assert (v2 = v3).
  eapply UniqueFunType.
  eauto.
  auto.
  rewrite H.
  assert (ls2 = ls0).
  eapply IHfenv.
  auto.
  auto.
  rewrite H0.
  auto.
Defined.


Lemma UniqueExpType (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
      (e: Exp) (t1 t2: VTyp)
      (k0: FEnvTyping fenv ftenv)
      (k1: ExpTyping ftenv tenv fenv e t1)
      (k2: ExpTyping ftenv tenv fenv e t2) : t1 = t2.
  eapply ExpStrongTyping.
  eauto.
  auto.
  eauto.
  auto.
Defined.

Lemma UniquePrmsType (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
      (ps: Prms) (pt1 pt2: PTyp)
      (k0: FEnvTyping fenv ftenv)
      (k1: PrmsTyping ftenv tenv fenv ps pt1)
      (k2: PrmsTyping ftenv tenv fenv ps pt2) : pt1 = pt2.
  eapply PrmsStrongTyping.
  eauto.
  auto.
  eauto.
  auto.
Defined.

Lemma UniqueQFunType (ftenv: funTC) (fenv: funEnv)
      (qf: QFun) (ft1 ft2: FTyp)
      (k0: FEnvTyping fenv ftenv)
      (k1: QFunTyping ftenv fenv qf ft1)
      (k2: QFunTyping ftenv fenv qf ft2) : ft1 = ft2.
  eapply QFunStrongTyping.
  eauto.
  auto.
  eauto.
  auto.
Defined.

  
End STyping.
