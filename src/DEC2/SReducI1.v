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


Import ListNotations.


Module SReduc (IdT: ModTyp) <: ModTyp.

Module TSoundnessL := TSoundness IdT.
Export TSoundnessL.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Open Scope type_scope.


(** subject reduction *)
         
Definition ExpSRed (fenv: funEnv) (D: FEnvWT fenv) :=
     fun (ftenv: funTC) (tenv: valTC) 
         (e: Exp) (t: VTyp) 
         (k: ExpTyping ftenv tenv e t) =>
   FEnvTyping fenv ftenv -> 
   forall (env: valEnv),                      
   EnvTyping env tenv ->
   forall (e': Exp) (s s': W) (n n': nat),
     EStep fenv env (Conf Exp s n e) (Conf Exp s' n' e') ->
     ExpTyping ftenv tenv e' t.


Definition PrmsSRed (fenv: funEnv) (D: FEnvWT fenv) :=
     fun (ftenv: funTC) (tenv: valTC) 
         (ps: Prms) (pt: PTyp) 
         (k: PrmsTyping ftenv tenv ps pt) => 
   FEnvTyping fenv ftenv -> 
   forall (env: valEnv),                      
   EnvTyping env tenv ->
   forall (ps': Prms) (s s': W) (n n': nat),
     PStep fenv env (Conf Prms s n ps) (Conf Prms s' n' ps') ->
     PrmsTyping ftenv tenv ps' pt.


Definition ExpSRed_mut (fenv: funEnv) (D: FEnvWT fenv) :=
  ExpTyping_mut (ExpSRed fenv D) (PrmsSRed fenv D). 

Definition PrmsSRed_mut (fenv: funEnv) (D: FEnvWT fenv) :=
  PrmsTyping_mut (ExpSRed fenv D) (PrmsSRed fenv D).

Lemma ExpSubjectRed (fenv: funEnv) (D: FEnvWT fenv) :
  forall (ftenv: funTC) (tenv: valTC) 
   (e: Exp) (t: VTyp)
   (k: ExpTyping ftenv tenv e t),
   ExpSRed fenv D ftenv tenv e t k.
    
Proof.
eapply (ExpSRed_mut fenv D).
- unfold ExpSRed.
  intros.
  inversion X.
- unfold ExpSRed.
  intros.
  inversion X; subst.
  inversion i; subst.
  constructor.
  unfold VTyping.
  eapply (RelatedByEnv valueVTyp).
  exact H0.
  exact H4.
  assumption.
- unfold ExpSRed.
  intros.
  inversion X1; subst.
  exact e0.
  econstructor.
  specialize (X H env H0 e1' s s' n n' X2).
  exact X.
  exact e0.
- unfold ExpSRed.
  intros.
  inversion X1; subst.
  assert (EnvTyping (singleE x v) (singleE x t1)) as K.
  {- unfold EnvTyping.
     unfold MatchEnvs.
     unfold singleE.
     unfold emptyE.
     unfold thicken.
     simpl.
     inversion e0; subst.
     inversion H4; subst.
     reflexivity.
  }
  econstructor.
  {- exact K. }
  {- reflexivity. }
  {- eapply e3. }
  econstructor.
  exact m0.
  reflexivity.
  eapply (X H env H0).
  exact X2.
  eapply e3.
- unfold ExpSRed.
  intros.
  inversion X0; subst.
  inversion e2; subst.
  econstructor.
  assumption.

  econstructor.
  exact e0.
  reflexivity.
  eapply X.
  exact H.
  eapply overrideEnvLemma.
  exact e0.
  exact H0.
  exact X1.
- unfold ExpSRed.
  intros.
  inversion X2; subst.
  exact e0.
  exact e4.
  econstructor.
  eapply (X H env H0).
  exact X3.
  exact e0.
  exact e4.
- unfold ExpSRed, PrmsSRed.
  intros.

  inversion X1; subst.
  econstructor.
  eapply Pure_step_inv1.
  exact p.
  exact X2.
  exact i.
  exact p0.

  eapply X0.
  exact H.
  exact H0.
  exact X2.

  econstructor.
  constructor.
  exact i.
  eapply X.
  exact H.
  exact H0.
  exact X2.
  exact e0.
  
  inversion X1; subst.

  econstructor.
  exact i.
  exact p0.
    
- unfold ExpSRed, PrmsSRed.
  intros.
  inversion X0; subst.
  destruct ps' as [ls'].
  econstructor.
  exact i.
  eapply (X H env H0).
  exact X1.

  assert (FTyping f (FT pt t)).
  eapply RelatedByEnv.
  exact H.
  exact H8.
  exact i.

  destruct f.
  simpl in *.
  inversion H1; subst.
  constructor.
  constructor.

  assert (FTyping f (FT pt t)) as K1.
  eapply RelatedByEnv.
  exact H.
  exact H8.
  exact i.

  inversion X0; subst.
  rewrite H8 in H9.
  inversion H9; subst.
  econstructor.
  instantiate (1:=funValTC f0).
  eapply mkVEnv_typing_lemma1.
  exact K1.
  instantiate (1:=tenv).
  instantiate (1:=ftenv).
  inversion X1; subst.
  inversion X2; subst.
  eapply mapEq in H2.
  inversion H2; subst.
  exact p.
  reflexivity.

  unfold FEnvWT in D.
  specialize (D ftenv H x).
  specialize (D f0 H8).
  unfold FunWT in D.
  
  destruct f0.
  inversion K1; subst.
  simpl in *.

  eapply ExpTWeaken.
  exact D.
  instantiate (1:=nil).
  simpl.
  rewrite app_nil_r.
  reflexivity.
  reflexivity.

- unfold ExpSRed, PrmsSRed.
  intros.
  inversion X0; subst.

  eapply inj_pair2 in H8.
  eapply inj_pair2 in H8.
  inversion H8; subst.
  clear XF2 H1.
  econstructor.
  unfold VTyping.
  unfold MatchEnvs.
  reflexivity.

  eapply inj_pair2 in H8.
  eapply inj_pair2 in H8.
  inversion H8; subst.
  clear XF2 H1.
  econstructor.

  eapply X.
  exact H.
  exact H0.
  exact X1.

- unfold ExpSRed, PrmsSRed.
  intros.
  inversion X.

- unfold ExpSRed, PrmsSRed.
  intros.
  inversion X1; subst.
  econstructor.
  exact e0.
  eapply (X0 H env H0).
  exact X2.
  econstructor.
  eapply (X H env H0).
  exact X2.
  exact p.
Defined.  



Lemma PrmsSubjectRed (fenv: funEnv) (D: FEnvWT fenv) :
  forall (ftenv: funTC) (tenv: valTC) 
   (ps: Prms) (pt: PTyp)
   (k: PrmsTyping ftenv tenv ps pt),
   PrmsSRed fenv D ftenv tenv ps pt k.
    
Proof.
eapply (PrmsSRed_mut fenv D).
- unfold ExpSRed.
  intros.
  inversion X.
- unfold ExpSRed.
  intros.
  inversion X; subst.
  inversion i; subst.
  constructor.
  unfold VTyping.
  eapply (RelatedByEnv valueVTyp).
  exact H0.
  exact H4.
  assumption.
- unfold ExpSRed.
  intros.
  inversion X1; subst.
  exact e0.
  econstructor.
  specialize (X H env H0 e1' s s' n n' X2).
  exact X.
  exact e0.
- unfold ExpSRed.
  intros.
  inversion X1; subst.
  assert (EnvTyping (singleE x v) (singleE x t1)) as K.
  {- unfold EnvTyping.
     unfold MatchEnvs.
     unfold singleE.
     unfold emptyE.
     unfold thicken.
     simpl.
     inversion e0; subst.
     inversion H4; subst.
     reflexivity.
  }
  econstructor.
  {- exact K. }
  {- reflexivity. }
  {- eapply e3. }
  econstructor.
  exact m0.
  reflexivity.
  eapply (X H env H0).
  exact X2.
  eapply e3.
- unfold ExpSRed.
  intros.
  inversion X0; subst.
  inversion e2; subst.
  econstructor.
  assumption.

  econstructor.
  exact e0.
  reflexivity.
  eapply X.
  exact H.
  eapply overrideEnvLemma.
  exact e0.
  exact H0.
  exact X1.
- unfold ExpSRed.
  intros.
  inversion X2; subst.
  exact e0.
  exact e4.
  econstructor.
  eapply (X H env H0).
  exact X3.
  exact e0.
  exact e4.
- unfold ExpSRed, PrmsSRed.
  intros.

  inversion X1; subst.
  econstructor.
  eapply Pure_step_inv1.
  exact p.
  exact X2.
  exact i.
  exact p0.

  eapply X0.
  exact H.
  exact H0.
  exact X2.

  econstructor.
  constructor.
  exact i.
  eapply X.
  exact H.
  exact H0.
  exact X2.
  exact e0.
  
  inversion X1; subst.

  econstructor.
  exact i.
  exact p0.
    
- unfold ExpSRed, PrmsSRed.
  intros.
  inversion X0; subst.
  destruct ps' as [ls'].
  econstructor.
  exact i.
  eapply (X H env H0).
  exact X1.

  assert (FTyping f (FT pt t)).
  eapply RelatedByEnv.
  exact H.
  exact H8.
  exact i.

  destruct f.
  simpl in *.
  inversion H1; subst.
  constructor.
  constructor.

  assert (FTyping f (FT pt t)) as K1.
  eapply RelatedByEnv.
  exact H.
  exact H8.
  exact i.

  inversion X0; subst.
  rewrite H8 in H9.
  inversion H9; subst.
  econstructor.
  instantiate (1:=funValTC f0).
  eapply mkVEnv_typing_lemma1.
  exact K1.
  instantiate (1:=tenv).
  instantiate (1:=ftenv).
  inversion X1; subst.
  inversion X2; subst.
  eapply mapEq in H2.
  inversion H2; subst.
  exact p.
  reflexivity.

  unfold FEnvWT in D.
  specialize (D ftenv H x).
  specialize (D f0 H8).
  unfold FunWT in D.
  
  destruct f0.
  inversion K1; subst.
  simpl in *.

  eapply ExpTWeaken.
  exact D.
  instantiate (1:=nil).
  simpl.
  rewrite app_nil_r.
  reflexivity.
  reflexivity.

- unfold ExpSRed, PrmsSRed.
  intros.
  inversion X0; subst.

  eapply inj_pair2 in H8.
  eapply inj_pair2 in H8.
  inversion H8; subst.
  clear XF2 H1.
  econstructor.
  unfold VTyping.
  unfold MatchEnvs.
  reflexivity.

  eapply inj_pair2 in H8.
  eapply inj_pair2 in H8.
  inversion H8; subst.
  clear XF2 H1.
  econstructor.

  eapply X.
  exact H.
  exact H0.
  exact X1.

- unfold ExpSRed, PrmsSRed.
  intros.
  inversion X.

- unfold ExpSRed, PrmsSRed.
  intros.
  inversion X1; subst.
  econstructor.
  exact e0.
  eapply (X0 H env H0).
  exact X2.
  econstructor.
  eapply (X H env H0).
  exact X2.
  exact p.
Defined.  


End SReduc.
