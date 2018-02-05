
Require Export Basics.

Require Export EnvLibA.
Require Export RelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Import ProofIrrelevance. 

Require Import IdModTypeA.
Require Import StaticSemA.
Require Import DynamicSemA.
Require Import TRInductA.
Require Import WeakenA.
Require Import TSoundnessA.

Import ListNotations.

Module SReduc (IdT: IdModType) <: IdModType.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module TSoundnessI := TSoundness IdT.
Export TSoundnessI.


(** subject reduction *)


Definition FunSRed :=
     fun (f: Fun) (ft: FTyp) 
         (k: FunTyping f ft) => True.    
      
Definition QFunSRed :=
     fun (ftenv: funTC) (fenv: funEnv)
         (q: QFun) (ft: FTyp) 
         (k: QFunTyping ftenv fenv q ft) =>
       MatchEnvsT FunTyping fenv ftenv ->
       forall (q': QFun) (n n': W),
         QFStep fenv (Conf QFun n q) (Conf QFun n' q') ->
         QFunTyping ftenv fenv q' ft.
         
Definition ExpSRed :=
     fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (e: Exp) (t: VTyp) 
         (k: ExpTyping ftenv tenv fenv e t) =>
   MatchEnvsT FunTyping fenv ftenv ->
   forall (env: valEnv),   
   MatchEnvsT ValueTyping env tenv ->
   forall (e': Exp) (n n': W),
     EStep fenv env (Conf Exp n e) (Conf Exp n' e') ->
     ExpTyping ftenv tenv fenv e' t.


Definition PrmsSRed :=
     fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (ps: Prms) (pt: PTyp) 
         (k: PrmsTyping ftenv tenv fenv ps pt) => 
   MatchEnvsT FunTyping fenv ftenv ->
   forall (env: valEnv),   
   MatchEnvsT ValueTyping env tenv ->
   forall (ps': Prms) (n n': W),
     PrmsStep fenv env (Conf Prms n ps) (Conf Prms n' ps') ->
     PrmsTyping ftenv tenv fenv ps' pt.


Definition ExpSRed_rect :=
  ExpTyping_str_rect FunSRed QFunSRed 
                     ExpSRed PrmsSRed. 


Lemma ExpSubjectRed :
  forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (e: Exp) (t: VTyp)
   (k: ExpTyping ftenv tenv fenv e t),
   ExpSRed ftenv tenv fenv e t k.
    
Proof.
eapply ExpSRed_rect.

- (** base Par_SSL *)
  unfold Par_SSL, ExpSRed.
  constructor.
  
- (** step Par_SSL *)
  unfold Par_SSL, ExpSRed.
  intros.  
  constructor.
  + assumption.
  + assumption.    
  + assumption.

- (** base Par_SSA *)
  unfold Par_SSA, FunSRed.
  constructor.

- (** step Par_SSA *)
  unfold Par_SSA, FunSRed.
  intros.
  constructor.
  + assumption.
  + assumption.
  + assumption.

- (** Par_SSB *)
  unfold Par_SSB, Par_SSA, FunSRed.
  intros.
  econstructor.
  exact m0.
  exact m1.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  auto.
  
- (** base Par_F *)
  unfold FunSRed, ExpSRed.
  intros.
  auto.

- (** step Par_F *)
  unfold FunSRed, ExpSRed.
  intros.
  auto.

- (** Par_Q - QF *)    
  unfold QFunSRed, FunSRed. 
  intros.
  destruct ft. 
  intros.  
  inversion X0; subst.

- (** Par_Q - FId *)
  unfold QFunSRed, Par_SSB, FunSRed, Par_SSA.
  intros.
  destruct q'.
  destruct ft.
  econstructor 2 with (f:=f).
  inversion X1.
  inversion X1; subst.

  inversion X; subst.
  clear X.
  constructor.
  inversion m; subst.
   
  eapply ExRelValTNone with (venv:=ls1) in H.
  eapply override_simpl3 with (env:= (x, f)::ls3) in H.
  simpl in H.
  destruct (IdT.IdEqDec x x) in H.
  inversion X1; subst.
  inversion X7; subst.
  rewrite H0 in H3.
  rewrite <- H in H3 at 1.
  inversion H3; subst.
  exact p0.
  intuition n.
  (* exact ft. *)
  eassumption.

 (** Par_E *)
-  (* modify *)
  unfold ExpSRed.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q H H0 env H0' e' n n' H1.
  inversion H; subst; clear H. 
  destruct v as [T' v].
  destruct v.
  inversion H2; subst; clear H2.
  subst T.
  simpl in *.
  subst.
  inversion H1; subst.
  
  clear H9.
  eapply inj_pair2 in H8.
  eapply inj_pair2 in H8.
  subst.
  eapply inj_pair2 in H10.
  subst.
  clear VT5 VT4.
  clear XF2.
  clear H3.
  
  constructor.
  constructor.
  simpl.
  auto.
  simpl.
  auto.

  inversion X. 
  inversion H1; subst.
  clear XF2.
  eapply inj_pair2 in H7.
  eapply inj_pair2 in H7.
  subst.
  assert (VT1 = VT4).
  eapply loc_pi.
  subst.
  assert (VT2 = VT5).
  eapply loc_pi.
  subst.
  inversion X0; subst.
  destruct v as [T v]. 
  destruct v.
  inversion X; subst.
  
  constructor.  
  constructor.

  simpl in *.
  eapply (ValTypedByEnvA env tenv x _ _ H0' X1) in X2.
  inversion X2; subst.
  subst T0.   
  simpl in *.
  subst.
  auto.
  
- (* return *)
  unfold ExpSRed.
  intros G ftenv tenv fenv q t H H0 env H0' e' n n' H1.
  inversion H; subst.
  + inversion H1; subst.
    constructor.
    exact H2.
    inversion X.
  + inversion H1; subst.
    constructor.
    inversion X0; subst.
    inversion X; subst.
    constructor.
    eapply ValTypedByEnvA.
    exact H0'.
    exact X1.
    exact X2.    
- (* bindN *)
  unfold ExpSRed.
  intros ftenv tenv fenv e1 e2 t1 t2.
  intros k1 k2 IH1 IH2.
  intros H0 env H0' e n n' H.  
  specialize (IH1 H0 env H0').
  specialize (IH2 H0 env H0').
  inversion H; subst.
  exact k2.  
  specialize (IH1 e1' n n' X).
  econstructor.
  exact IH1.
  exact k2.
- (* BindS *)
  unfold ExpSRed.
  intros ftenv tenv fenv x e1 e2 t1 t2.
  intros k1 k2 IH1 IH2.
  intros H0 env H0' e n n' H.  
  specialize (IH1 H0 env H0').  
  specialize (IH2 H0).
  inversion H; subst.
  inversion k1; subst.
  econstructor.
  instantiate (1:=(singleE x t1)).
  constructor.
  exact H5.
  constructor.
  exact H0.
  econstructor.
  reflexivity.
  reflexivity.
  reflexivity.
  simpl in *.
  exact k2.
  econstructor.
  eapply IH1.
  exact X.
  exact k2.
- (* BindMS *)
  unfold ExpSRed.  
  intros ftenv ftenvP ftenv' tenv tenvP tenv' fenv fenvP fenv' envP e t.
  intros k1 k2 k3 k4 k5 k6 k7 IH.  
  intros H0 env H0' e' n n' H.
  generalize H0'.
  intro H0''. 
  eapply (overrideVEnvLemma envP env tenvP tenv k1) in H0'.
  eapply (overrideFEnvLemma fenvP fenv ftenvP ftenv k3) in H0.
  cut (MatchEnvsT FunTyping (fenvP ++ fenv) (ftenvP ++ ftenv)).
  + cut (MatchEnvsT ValueTyping (envP ++ env) (tenvP ++ tenv)).
    * intros H1' H1.
      inversion H; subst.
      inversion k7; subst.
      constructor.      
      exact H6.
      econstructor.
      exact k1.
      exact k2.
      exact k3.
      reflexivity.
      reflexivity.
      reflexivity.
      specialize (IH H1 (envP ++ env) H1' e'0 n n' X).
      exact IH.
    * eapply appEnvLemmaT.   
      assumption.
      assumption.   
  + eapply appEnvLemmaT.
    assumption.
    assumption.
- (* Apply *)
  unfold QFunSRed, PrmsSRed, ExpSRed.  
  intros ftenv tenv fps fenv q ps pt t.  
  intros k0 k1 k2 k3 IH1 IH2.
  intros H0 env H0' e n n' H.

  specialize (IH1 k1).
  inversion H; subst.

  (* 1 *) 
  inversion H7; subst.
  inversion k2; subst.
  inversion X; subst.
  econstructor.
  eapply prmsTypingAux_T.
  exact H9.
  eapply matchListsAux02_T.
  exact H7.
  exact k3.
  exact k1.
  exact X0.
  reflexivity.
  reflexivity.
  reflexivity.
  
  (* weakening on typing needed *)
  eapply weakenTyping.
  assumption.
  assumption.
  assumption.

  (* 2 *)
  inversion k2; subst.
  inversion X; subst.
  subst ftenv'.
  subst fenv'0.
  econstructor.
  eapply prmsTypingAux_T.
  exact H9.
  eapply matchListsAux02_T.
  exact H7.
  exact k3.
  exact k1.
  eapply updateEnvLemmaT.
  exact X0.
  exact X2.
  reflexivity.
  reflexivity.
  reflexivity.
  eapply weakenTyping.
  exact X1.
  eapply updateEnvLemmaT.
  exact X0.
  exact X2.
  exact H0.
  
  (* 3 *)
  
  econstructor.
  reflexivity.
  exact H0.
  eapply k2.
  eapply IH2.
  exact H0.
  exact H0'.
  exact X.

  (* 4 *)
  econstructor.
  reflexivity.
  exact H0.
  eapply IH1.
  exact X.
  exact k3.

- (* Val *)
  unfold ExpSRed. 
  intros.
  inversion X1; subst.
 - (* IFThenElse *)
  unfold ExpSRed.    
  intros.
  inversion X4; subst.
  exact k2.
  exact k3.
  econstructor.
  eapply X.
  exact X2.
  exact X3.
  exact X5.
  exact k2.
  exact k3.
 - unfold PrmsSRed, Par_SSL, ExpSRed.    
   intros.
   revert X2.
   revert ps'.
   induction X.
   intros.
   inversion X2.
   intros.
   inversion m; subst.
   specialize (IHX X4).
   destruct ps'.
   destruct es.
   inversion X2.
   specialize (IHX (PS es)).
   inversion X2; subst.
   specialize (IHX X5).
   inversion IHX; subst.
   constructor.
   constructor.
   exact p.
   exact X6.
   constructor.
   constructor.
   eapply p0.
   auto.
   eauto.
   eauto.
   auto.
Defined.
   

Definition PrmsSRed_rect :=
  PrmsTyping_str_rect FunSRed QFunSRed 
                     ExpSRed PrmsSRed. 


Lemma PrmsSubjectRed :
  forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (ps: Prms) (pt: PTyp)
   (k: PrmsTyping ftenv tenv fenv ps pt),
   PrmsSRed ftenv tenv fenv ps pt k.
    
Proof.
eapply PrmsSRed_rect.

- (** base Par_SSL *)
  unfold Par_SSL, ExpSRed.
  constructor.
  
- (** step Par_SSL *)
  unfold Par_SSL, ExpSRed.
  intros.  
  constructor.
  + assumption.
  + assumption.    
  + assumption.

- (** base Par_SSA *)
  unfold Par_SSA, FunSRed.
  constructor.

- (** step Par_SSA *)
  unfold Par_SSA, FunSRed.
  intros.
  constructor.
  + assumption.
  + assumption.
  + assumption.

- (** Par_SSB *)
  unfold Par_SSB, Par_SSA, FunSRed.
  intros.
  econstructor.
  exact m0.
  exact m1.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  auto.
  
- (** base Par_F *)
  unfold FunSRed, ExpSRed.
  intros.
  auto.

- (** step Par_F *)
  unfold FunSRed, ExpSRed.
  intros.
  auto.

- (** Par_Q - QF *)    
  unfold QFunSRed, FunSRed. 
  intros.
  destruct ft. 
  intros.  
  inversion X0; subst.

- (** Par_Q - FId *)
  unfold QFunSRed, Par_SSB, FunSRed, Par_SSA.
  intros.
  destruct q'.
  destruct ft.
  econstructor 2 with (f:=f).
  inversion X1.
  inversion X1; subst.

  inversion X; subst.
  clear X.
  constructor.
  inversion m; subst.
   
  eapply ExRelValTNone with (venv:=ls1) in H.
  eapply override_simpl3 with (env:= (x, f)::ls3) in H.
  simpl in H.
  destruct (IdT.IdEqDec x x) in H.
  inversion X1; subst.
  inversion X7; subst.
  rewrite H0 in H3.
  rewrite <- H in H3 at 1.
  inversion H3; subst.
  exact p0.
  intuition n.
  (* exact ft. *)
  eassumption.

 (** Par_E *)
-  (* modify *)
  unfold ExpSRed.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q H H0 env H0' e' n n' H1.
  inversion H; subst; clear H. 
  destruct v as [T' v].
  destruct v.
  inversion H2; subst; clear H2.
  subst T.
  simpl in *.
  subst.
  inversion H1; subst.
  
  clear H9.
  eapply inj_pair2 in H8.
  eapply inj_pair2 in H8.
  subst.
  eapply inj_pair2 in H10.
  subst.
  clear VT5 VT4.
  clear XF2.
  clear H3.
  
  constructor.
  constructor.
  simpl.
  auto.
  simpl.
  auto.

  inversion X. 
  inversion H1; subst.
  clear XF2.
  eapply inj_pair2 in H7.
  eapply inj_pair2 in H7.
  subst.
  assert (VT1 = VT4).
  eapply loc_pi.
  subst.
  assert (VT2 = VT5).
  eapply loc_pi.
  subst.
  inversion X0; subst.
  destruct v as [T v]. 
  destruct v.
  inversion X; subst.
  
  constructor.  
  constructor.

  simpl in *.
  eapply (ValTypedByEnvA env tenv x _ _ H0' X1) in X2.
  inversion X2; subst.
  subst T0.   
  simpl in *.
  subst.
  auto.
  
- (* return *)
  unfold ExpSRed.
  intros G ftenv tenv fenv q t H H0 env H0' e' n n' H1.
  inversion H; subst.
  + inversion H1; subst.
    constructor.
    exact H2.
    inversion X.
  + inversion H1; subst.
    constructor.
    inversion X0; subst.
    inversion X; subst.
    constructor.
    eapply ValTypedByEnvA.
    exact H0'.
    exact X1.
    exact X2.    
- (* bindN *)
  unfold ExpSRed.
  intros ftenv tenv fenv e1 e2 t1 t2.
  intros k1 k2 IH1 IH2.
  intros H0 env H0' e n n' H.  
  specialize (IH1 H0 env H0').
  specialize (IH2 H0 env H0').
  inversion H; subst.
  exact k2.  
  specialize (IH1 e1' n n' X).
  econstructor.
  exact IH1.
  exact k2.
- (* BindS *)
  unfold ExpSRed.
  intros ftenv tenv fenv x e1 e2 t1 t2.
  intros k1 k2 IH1 IH2.
  intros H0 env H0' e n n' H.  
  specialize (IH1 H0 env H0').  
  specialize (IH2 H0).
  inversion H; subst.
  inversion k1; subst.
  econstructor.
  instantiate (1:=(singleE x t1)).
  constructor.
  exact H5.
  constructor.
  exact H0.
  econstructor.
  reflexivity.
  reflexivity.
  reflexivity.
  simpl in *.
  exact k2.
  econstructor.
  eapply IH1.
  exact X.
  exact k2.
- (* BindMS *)
  unfold ExpSRed.  
  intros ftenv ftenvP ftenv' tenv tenvP tenv' fenv fenvP fenv' envP e t.
  intros k1 k2 k3 k4 k5 k6 k7 IH.  
  intros H0 env H0' e' n n' H.
  generalize H0'.
  intro H0''. 
  eapply (overrideVEnvLemma envP env tenvP tenv k1) in H0'.
  eapply (overrideFEnvLemma fenvP fenv ftenvP ftenv k3) in H0.
  cut (MatchEnvsT FunTyping (fenvP ++ fenv) (ftenvP ++ ftenv)).
  + cut (MatchEnvsT ValueTyping (envP ++ env) (tenvP ++ tenv)).
    * intros H1' H1.
      inversion H; subst.
      inversion k7; subst.
      constructor.      
      exact H6.
      econstructor.
      exact k1.
      exact k2.
      exact k3.
      reflexivity.
      reflexivity.
      reflexivity.
      specialize (IH H1 (envP ++ env) H1' e'0 n n' X).
      exact IH.
    * eapply appEnvLemmaT.   
      assumption.
      assumption.   
  + eapply appEnvLemmaT.
    assumption.
    assumption.
- (* Apply *)
  unfold QFunSRed, PrmsSRed, ExpSRed.  
  intros ftenv tenv fps fenv q ps pt t.  
  intros k0 k1 k2 k3 IH1 IH2.
  intros H0 env H0' e n n' H.

  specialize (IH1 k1).
  inversion H; subst.

  (* 1 *) 
  inversion H7; subst.
  inversion k2; subst.
  inversion X; subst.
  econstructor.
  eapply prmsTypingAux_T.
  exact H9.
  eapply matchListsAux02_T.
  exact H7.
  exact k3.
  exact k1.
  exact X0.
  reflexivity.
  reflexivity.
  reflexivity.
  
  (* weakening on typing needed *)
  eapply weakenTyping.
  assumption.
  assumption.
  assumption.

  (* 2 *)
  inversion k2; subst.
  inversion X; subst.
  subst ftenv'.
  subst fenv'0.
  econstructor.
  eapply prmsTypingAux_T.
  exact H9.
  eapply matchListsAux02_T.
  exact H7.
  exact k3.
  exact k1.
  eapply updateEnvLemmaT.
  exact X0.
  exact X2.
  reflexivity.
  reflexivity.
  reflexivity.
  eapply weakenTyping.
  exact X1.
  eapply updateEnvLemmaT.
  exact X0.
  exact X2.
  exact H0.
  
  (* 3 *)
  
  econstructor.
  reflexivity.
  exact H0.
  eapply k2.
  eapply IH2.
  exact H0.
  exact H0'.
  exact X.

  (* 4 *)
  econstructor.
  reflexivity.
  exact H0.
  eapply IH1.
  exact X.
  exact k3.

- (* Val *)
  unfold ExpSRed. 
  intros.
  inversion X1; subst.
 - (* IFThenElse *)
  unfold ExpSRed.    
  intros.
  inversion X4; subst.
  exact k2.
  exact k3.
  econstructor.
  eapply X.
  exact X2.
  exact X3.
  exact X5.
  exact k2.
  exact k3.
 - unfold PrmsSRed, Par_SSL, ExpSRed.    
   intros.
   revert X2.
   revert ps'.
   induction X.
   intros.
   inversion X2.
   intros.
   inversion m; subst.
   specialize (IHX X4).
   destruct ps'.
   destruct es.
   inversion X2.
   specialize (IHX (PS es)).
   inversion X2; subst.
   specialize (IHX X5).
   inversion IHX; subst.
   constructor.
   constructor.
   exact p.
   exact X6.
   constructor.
   constructor.
   eapply p0.
   auto.
   eauto.
   eauto.
   auto.
Defined.



End SReduc.
