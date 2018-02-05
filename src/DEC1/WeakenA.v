Require Export Basics.

Require Export EnvLibA.
Require Export RelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Import StaticSemA.
Require Import DynamicSemA.

Import ListNotations.

Module Weaken (IdT: IdModType) <: IdModType.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module DynamicI := Dynamic IdT.
Export DynamicI.


Lemma QValWeakening (env env': valEnv)
      (n1 n2: W)
      (q1 q2: QValue):
  QVStep env (Conf QValue n1 q1) (Conf QValue n2 q2) ->
  QVStep (env ++ env') (Conf QValue n1 q1) (Conf QValue n2 q2).
Proof.
  intros. 
  inversion X; subst.
  constructor.
  inversion X0; subst.
  eapply override_simpl1 with (env2:=env') in H.
  constructor.
  rewrite H.
  inversion X0; subst.
  assumption.
Defined.


Lemma QFunWeakening (env env': funEnv)
      (n1 n2: W)
      (q1 q2: QFun):
  QFStep env (Conf QFun n1 q1) (Conf QFun n2 q2) ->
  QFStep (env ++ env') (Conf QFun n1 q1) (Conf QFun n2 q2).
Proof.
  intros. 
  inversion X; subst.
  constructor.
  inversion X0; subst.
  eapply override_simpl1 with (env2:=env') in H.
  constructor.
  rewrite H.
  inversion X0; subst.
  assumption.
Defined.
  

Lemma weaken 
           (fenv fenv': funEnv) (env env': valEnv)
           (n1 n2: W) (e1 e2: Exp):
      EClosure fenv env (Conf Exp n1 e1) (Conf Exp n2 e2) ->
      EClosure (fenv ++ fenv') (env ++ env')
               (Conf Exp n1 e1) (Conf Exp n2 e2).
Proof.
  intros.  
  dependent induction X.
  constructor.
  destruct p2 as [n0 e0].
  specialize (IHX n0 n2 e0 e2 eq_refl eq_refl).
  econstructor.
  Focus 2.
  eassumption.

  (***)

  clear IHX.
  clear X.
  rename e into H.
  clear n2 e2.
  revert fenv' env'.
  
  (***)

    eapply (EStep_mut (fun fenv env c1 c2
 (ExIH: EStep fenv env c1 c2) => forall fenv' env',    
  EStep (fenv ++ fenv') (env ++ env') 
        c1 c2)
  (fun fenv env c1 c2
  (PsIH: PrmsStep fenv env c1 c2) => forall fenv' env', 
  PrmsStep (fenv ++ fenv') (env ++ env') 
           c1 c2)).

  - intros.
    constructor.
  - intros.                     
    constructor.
    eapply QValWeakening.
    assumption.
  - intros.
    constructor.
  - intros.
    constructor.
    eapply QValWeakening.
    assumption.
  - intros.
    constructor.
  - intros.
    constructor.
    eapply X.
  - intros.    
    constructor.    
  - intros.  
    constructor.    
    eapply X.
  - intros.        
    constructor. 
  - intros. 
    econstructor.
    + reflexivity.
    + reflexivity.
    + rewrite app_assoc.
      rewrite app_assoc.
      specialize (X fenv'0 env'0).
      rewrite e2 in X.
      rewrite e3 in X.
      eapply X. 
  - intros.
    econstructor.
    auto.
    eassumption.
    assumption.
    assumption.
  - intros.
    econstructor.
    eassumption.
    assumption.
    assumption.
  - intros.  
    econstructor.
    eapply X.    
  - intros.
    econstructor.
    eapply QFunWeakening.       
    assumption.    
  - intros.
    constructor.
  - intros.
    constructor.
  - intros.
    constructor.
    eapply X.
  - intros.
    constructor.
    eapply X.                 
  - intros.
    constructor.      
    eapply X.     
  - assumption.
Defined.    



Definition FunWeaken :=
     fun (f: Fun) (ft: FTyp) 
         (k: FunTyping f ft) => True.    
      
Definition QFunWeaken :=
     fun (ftenv: funTC) (fenv: funEnv)
         (q: QFun) (ft: FTyp) 
         (k: QFunTyping ftenv fenv q ft) =>
       MatchEnvsT FunTyping fenv ftenv ->
       forall (ftenv': funTC) (fenv': funEnv),
          MatchEnvsT FunTyping fenv' ftenv' ->
          QFunTyping (ftenv ++ ftenv') (fenv ++ fenv') q ft.
          
Definition ExpWeaken :=
     fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (e: Exp) (t: VTyp) 
         (k: ExpTyping ftenv tenv fenv e t) =>
   MatchEnvsT FunTyping fenv ftenv ->
   forall (ftenv': funTC) (tenv': valTC) (fenv': funEnv),
       MatchEnvsT FunTyping fenv' ftenv' -> 
       ExpTyping (ftenv ++ ftenv') (tenv ++ tenv') (fenv ++ fenv') e t.


Definition PrmsWeaken :=
     fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (ps: Prms) (pt: PTyp) 
         (k: PrmsTyping ftenv tenv fenv ps pt) => 
   MatchEnvsT FunTyping fenv ftenv ->
   forall (ftenv': funTC) (tenv': valTC) (fenv': funEnv),
       MatchEnvsT FunTyping fenv' ftenv' -> 
       PrmsTyping (ftenv ++ ftenv') (tenv ++ tenv') (fenv ++ fenv') ps pt.



Definition ExpWeaken_rect :=
  ExpTyping_str_rect 
                     FunWeaken QFunWeaken 
                     ExpWeaken PrmsWeaken. 

Lemma weakenTyping 
           (ftenv: funTC) (tenv: valTC) (fenv: funEnv) 
           (e: Exp) (t: VTyp):
   ExpTyping ftenv tenv fenv e t ->
   MatchEnvsT FunTyping fenv ftenv ->
   forall (ftenv': funTC) (tenv': valTC) (fenv': funEnv),
       MatchEnvsT FunTyping fenv' ftenv' -> 
       ExpTyping (ftenv ++ ftenv') (tenv ++ tenv') (fenv ++ fenv') e t.
Proof.
  eapply ExpWeaken_rect.
  - unfold Par_SSL, ExpWeaken.
    intros.
    constructor.
  - unfold Par_SSL, ExpWeaken.
    intros.
    constructor.
    auto.
    auto.
    auto.
  - unfold Par_SSA.
    constructor.
  - unfold Par_SSA.
    econstructor.
    eauto.
    auto.
  - unfold Par_SSB, Par_SSA.
    intros.    
    econstructor.
    exact m0.
    exact m1. 
    auto.
    auto.
    auto.
    auto.
    eauto.
  - unfold ExpWeaken, FunWeaken.
    intros.
    constructor.    
  - unfold ExpWeaken, FunWeaken.
    intros.
    constructor.
  - unfold QFunWeaken, FunWeaken.
    intros.
    constructor.
    auto.
  - unfold QFunWeaken, FunWeaken, Par_SSB, Par_SSA.
    intros.
    econstructor.
    instantiate (1:=f).
    inversion m; subst.
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite <- app_comm_cons.
    rewrite <- app_comm_cons.
    econstructor.
    assumption.    
    exact X3.
    eapply appEnvLemmaT.
    exact X4.
    exact X1.
    assumption.
    reflexivity.
    reflexivity.
  - unfold ExpWeaken.
    intros.
    constructor.
    inversion k; subst.
    constructor.
    auto.
    constructor.
    inversion X1; subst.
    constructor.
    constructor.
    inversion X2; subst.
    rewrite (override_simpl1 tenv0 tenv' x (vtyp T1)).
    exact H.
    exact H.
  - unfold ExpWeaken.
    intros.
    constructor.
    inversion k; subst.
    constructor.
    auto.    
    constructor.
    inversion X1; subst.
    constructor.
    constructor.
    inversion X2; subst.
    rewrite (override_simpl1 tenv0 tenv' x t0).
    exact H.
    exact H.

  - unfold ExpWeaken.
    intros.
    specialize (X X1 ftenv' tenv' fenv' X2). 
    specialize (X0 X1 ftenv' tenv' fenv' X2). 
    econstructor.
    exact X.
    exact X0.
  - unfold ExpWeaken.
    intros.
    specialize (X X1 ftenv' tenv' fenv' X2). 
    econstructor.     
    exact X.
    eapply X0.
    exact X1.
    exact X2.    
  - unfold ExpWeaken.
    intros.
    econstructor.
    exact k1.
    eapply overrideEnvLemmaT.
    exact X0.
    exact X1.
    exact m2.
    reflexivity.
    reflexivity.
    reflexivity.    
    assert (MatchEnvsT FunTyping (fenvP ++ fenv0) (ftenvP ++ ftenv0)).
    eapply overrideEnvLemmaT.
    exact m2.    
    exact m1.
    rewrite h1 in X.
    rewrite h2 in X.
    rewrite h3 in X.
    
    specialize (X X2 ftenv'0 tenv'0 fenv'0 X1).
    repeat rewrite app_assoc. 
    auto.
  - unfold ExpWeaken, QFunWeaken, PrmsWeaken.
    intros.
    econstructor.
    reflexivity.
    
    eapply overrideEnvLemmaT.
    assumption.    
    assumption.
    eapply X.    
    assumption.
    assumption.
    rewrite h in X0.
    eapply X0.
    assumption.
    assumption.
  - unfold ExpWeaken.
    intros.
    constructor.  
    assumption.
  - unfold ExpWeaken.
    intros.
    constructor.
    eapply X.
    assumption.
    assumption.
    eapply X0.
    assumption.    
    assumption.
    eapply X1.
    assumption.    
    assumption.
  - unfold Par_SSL, PrmsWeaken, ExpWeaken.
    intros.
    constructor.
    induction X.
    constructor.
    constructor. 
    eapply p0.    
    assumption.
    assumption.
    eapply IHX.
    inversion m; subst.
    exact X3.
Defined.


Definition PrmsWeaken_rect :=
  PrmsTyping_str_rect 
                     FunWeaken QFunWeaken 
                     ExpWeaken PrmsWeaken. 


Lemma weakenPrmsTyping 
           (ftenv: funTC) (tenv: valTC) (fenv: funEnv) 
           (ps: Prms) (pt: PTyp):
   PrmsTyping ftenv tenv fenv ps pt ->
   MatchEnvsT FunTyping fenv ftenv ->
   forall (ftenv': funTC) (tenv': valTC) (fenv': funEnv),
       MatchEnvsT FunTyping fenv' ftenv' -> 
       PrmsTyping (ftenv ++ ftenv') (tenv ++ tenv') (fenv ++ fenv') ps pt.
Proof.
  eapply PrmsWeaken_rect.
  - unfold Par_SSL, ExpWeaken.
    intros.
    constructor.
  - unfold Par_SSL, ExpWeaken.
    intros.
    constructor.
    auto.
    auto.
    auto.
  - unfold Par_SSA.
    constructor.
  - unfold Par_SSA.
    econstructor.
    eauto.
    auto.
  - unfold Par_SSB, Par_SSA.
    intros.    
    econstructor.
    exact m0.
    exact m1. 
    auto.
    auto.
    auto.
    auto.
    eauto.
  - unfold ExpWeaken, FunWeaken.
    intros.
    constructor.    
  - unfold ExpWeaken, FunWeaken.
    intros.
    constructor.
  - unfold QFunWeaken, FunWeaken.
    intros.
    constructor.
    auto.
  - unfold QFunWeaken, FunWeaken, Par_SSB, Par_SSA.
    intros.
    econstructor.
    instantiate (1:=f).
    inversion m; subst.
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite <- app_comm_cons.
    rewrite <- app_comm_cons.
    econstructor.
    assumption.    
    exact X3.
    eapply appEnvLemmaT.
    exact X4.
    exact X1.
    assumption.
    reflexivity.
    reflexivity.
  - unfold ExpWeaken.
    intros.
    constructor.
    inversion k; subst.
    constructor.
    auto.
    constructor.
    inversion X1; subst.
    constructor.
    constructor.
    inversion X2; subst.
    rewrite (override_simpl1 tenv0 tenv' x (vtyp T1)).
    exact H.
    exact H.
  - unfold ExpWeaken.
    intros.
    constructor.
    inversion k; subst.
    constructor.
    auto.    
    constructor.
    inversion X1; subst.
    constructor.
    constructor.
    inversion X2; subst.
    rewrite (override_simpl1 tenv0 tenv' x t).
    exact H.
    exact H.

  - unfold ExpWeaken.
    intros.
    specialize (X X1 ftenv' tenv' fenv' X2). 
    specialize (X0 X1 ftenv' tenv' fenv' X2). 
    econstructor.
    exact X.
    exact X0.
  - unfold ExpWeaken.
    intros.
    specialize (X X1 ftenv' tenv' fenv' X2). 
    econstructor.     
    exact X.
    eapply X0.
    exact X1.
    exact X2.    
  - unfold ExpWeaken.
    intros.
    econstructor.
    exact k1.
    eapply overrideEnvLemmaT.
    exact X0.
    exact X1.
    exact m2.
    reflexivity.
    reflexivity.
    reflexivity.    
    assert (MatchEnvsT FunTyping (fenvP ++ fenv0) (ftenvP ++ ftenv0)).
    eapply overrideEnvLemmaT.
    exact m2.    
    exact m1.
    rewrite h1 in X.
    rewrite h2 in X.
    rewrite h3 in X.
    
    specialize (X X2 ftenv'0 tenv'0 fenv'0 X1).
    repeat rewrite app_assoc. 
    auto.
  - unfold ExpWeaken, QFunWeaken, PrmsWeaken.
    intros.
    econstructor.
    reflexivity.
    
    eapply overrideEnvLemmaT.
    assumption.    
    assumption.
    eapply X.    
    assumption.
    assumption.
    rewrite h in X0.
    eapply X0.
    assumption.
    assumption.
  - unfold ExpWeaken.
    intros.
    constructor.  
    assumption.
  - unfold ExpWeaken.
    intros.
    constructor.
    eapply X.
    assumption.
    assumption.
    eapply X0.
    assumption.    
    assumption.
    eapply X1.
    assumption.    
    assumption.
  - unfold Par_SSL, PrmsWeaken, ExpWeaken.
    intros.
    constructor.
    induction X.
    constructor.
    constructor. 
    eapply p0.    
    assumption.
    assumption.
    eapply IHX.
    inversion m; subst.
    exact X3.
Defined.


End Weaken.

