(*  DEC 2.0 language specification.
   Paolo Torrini  
   Universite' de Lille - CRIStAL-CNRS
*)

Require Import List.
Require Import Equality.

Require Import AuxLibI1.
Require Import TypSpecI1. 
Require Import ModTypI1. 
Require Import LangSpecI1. 
Require Import StaticSemI1.
Require Import DynamicSemI1.

Import ListNotations.

(** Weakening lemmas *)

Module Weaken (IdT: ModTyp) <: ModTyp.

Module DynamicSemL := DynamicSem IdT.
Export DynamicSemL.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.


Definition EStepWeaken_def :
  forall (fenv: funEnv) (env: valEnv) (a1 a2: AConfig Exp), 
      EStep fenv env a1 a2 -> Type
  := fun (fenv: funEnv) (env: valEnv)
      (a1 a2: AConfig Exp)
      (k: EStep fenv env a1 a2) =>
       forall (fenv': funEnv) (env': valEnv),
         EStep (fenv ++ fenv') (env ++ env') a1 a2.

Definition PStepWeaken_def :
  forall (fenv: funEnv) (env: valEnv) (a1 a2: AConfig Prms), 
      PStep fenv env a1 a2 -> Type
  := fun (fenv: funEnv) (env: valEnv)
      (a1 a2: AConfig Prms)
      (k: PStep fenv env a1 a2) =>
       forall (fenv': funEnv) (env': valEnv),
         PStep (fenv ++ fenv') (env ++ env') a1 a2.

Definition Weaken_EStep_mut := EStep_mut EStepWeaken_def PStepWeaken_def.
  
Definition Weaken_PStep_mut := PStep_mut EStepWeaken_def PStepWeaken_def.
  

(**********************************************************************)

Definition EStep_mut2
   (P1 : forall (fenv: funEnv) (env: valEnv)
                (s1 s2: W) (n1 n2: nat) (e1 e2: Exp),    
       EStep fenv env (Conf Exp s1 n1 e1) (Conf Exp s2 n2 e2) -> Type)
   (P2 : forall (fenv: funEnv) (env: valEnv)
                (s1 s2: W) (n1 n2: nat) (ps1 ps2: Prms),    
       PStep fenv env (Conf Prms s1 n1 ps1) (Conf Prms s2 n2 ps2) -> Type) :=
  EStep_mut (fun fenv env a1 a2 => match a1 with Conf _ s1 n1 e1 =>
                                   match a2 with Conf _ s2 n2 e2 =>
                                   P1 fenv env s1 s2 n1 n2 e1 e2 end end)
            (fun fenv env a1 a2 => match a1 with Conf _ s1 n1 ps1 =>
                                   match a2 with Conf _ s2 n2 ps2 =>
                                   P2 fenv env s1 s2 n1 n2 ps1 ps2 end end).

Definition EStepWeaken_def2 :
  forall (fenv: funEnv) (env: valEnv)
         (s1 s2: W) (n1 n2: nat) (e1 e2: Exp),
      EStep fenv env (Conf Exp s1 n1 e1) (Conf Exp s2 n2 e2) -> Type
  := fun (fenv: funEnv) (env: valEnv)
         (s1 s2: W) (n1 n2: nat) (e1 e2: Exp)
         (k: EStep fenv env (Conf Exp s1 n1 e1) (Conf Exp s2 n2 e2)) =>
       forall env': valEnv, EStep fenv (env ++ env')
                            (Conf Exp s1 n1 e1) (Conf Exp s2 n2 e2).

Definition PStepWeaken_def2 :
  forall (fenv: funEnv) (env: valEnv)
         (s1 s2: W) (n1 n2: nat) (ps1 ps2: Prms),
      PStep fenv env (Conf Prms s1 n1 ps1) (Conf Prms s2 n2 ps2) -> Type
  := fun (fenv: funEnv) (env: valEnv)
         (s1 s2: W) (n1 n2: nat) (ps1 ps2: Prms)
         (k: PStep fenv env (Conf Prms s1 n1 ps1) (Conf Prms s2 n2 ps2)) =>
       forall env': valEnv, PStep fenv (env ++ env')
                            (Conf Prms s1 n1 ps1) (Conf Prms s2 n2 ps2).

Definition Weaken_EStep_mut2 := EStep_mut2 EStepWeaken_def2 PStepWeaken_def2.
            
            
(*************************************************************************)

Lemma EStepWeakenA
           (fenv fenv': funEnv) (env env': valEnv)
           (a1 a2: AConfig Exp):
      EStep fenv env a1 a2 ->
      EStep (fenv ++ fenv') (env ++ env') a1 a2.
Proof.
  intros.
  eapply Weaken_EStep_mut.
  - intros.
    unfold EStepWeaken_def.
    intros fenv1 env1.
    constructor.
    generalize e as e1; intro.
    eapply override_simpl1 with (env2:=env0) in e.
    rewrite e.
    exact e1.
  - intros.
    unfold EStepWeaken_def.
    intros fenv1 env1.
    constructor.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0.
  - intros.
    unfold EStepWeaken_def.
    intros fenv1 env1.
    constructor.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    econstructor.  
    reflexivity.
    specialize (X0 fenv1 env1).
    rewrite e0 in X0.
    rewrite app_assoc.
    exact X0.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    rewrite e in *.
    rewrite e0 in *.
    econstructor.
    exact f.
    reflexivity.
    exact i.
    reflexivity.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0.   
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    econstructor.
    generalize e as e4; intro.   
    eapply (override_simpl1 fenv0 fenv1 x f) in e.
    rewrite e.
    exact e4.
    exact i.
    exact e0.
    exact e1.
    exact e2.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    econstructor.
    exact i.
    generalize e0 as e4; intro.   
    eapply (override_simpl1 fenv0 fenv1 x f) in e0.
    rewrite e0.
    exact e4.
    exact e1.
    exact e2.
    exact e3.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0.
  - intros.
    unfold EStepWeaken_def, PStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0.
  - intros.
    unfold EStepWeaken_def, PStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0. 
  - exact X.
Defined.    
    

Lemma PStepWeakenA 
           (fenv fenv': funEnv) (env env': valEnv)
           (a1 a2: AConfig Prms):
      PStep fenv env a1 a2 ->
      PStep (fenv ++ fenv') (env ++ env') a1 a2.
Proof.
  intros.
  eapply Weaken_PStep_mut.
  - intros.
    unfold EStepWeaken_def.
    intros fenv1 env1.
    constructor.
    generalize e as e1; intro.
    eapply override_simpl1 with (env2:=env0) in e.
    rewrite e.
    exact e1.
  - intros.
    unfold EStepWeaken_def.
    intros fenv1 env1.
    constructor.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0.
  - intros.
    unfold EStepWeaken_def.
    intros fenv1 env1.
    constructor.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    econstructor.  
    reflexivity.
    specialize (X0 fenv1 env1).
    rewrite e0 in X0.
    rewrite app_assoc.
    exact X0.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    rewrite e in *.
    rewrite e0 in *.
    econstructor.
    exact f.
    reflexivity.
    exact i.
    reflexivity.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0.  
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    econstructor.
    generalize e as e4; intro.   
    eapply (override_simpl1 fenv0 fenv1 x f) in e.
    rewrite e.
    exact e4.
    exact i.
    exact e0.
    exact e1.
    exact e2.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    econstructor.
    exact i.
    generalize e0 as e4; intro.   
    eapply (override_simpl1 fenv0 fenv1 x f) in e0.
    rewrite e0.
    exact e4.
    exact e1.
    exact e2.
    exact e3.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
  - intros.
    unfold EStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0.
  - intros.
    unfold EStepWeaken_def, PStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0.
  - intros.
    unfold EStepWeaken_def, PStepWeaken_def in *.
    intros fenv1 env1.
    constructor.
    apply X0. 
  - exact X.
Defined.    


Lemma EClosWeakenA 
      (fenv fenv': funEnv) (env env': valEnv)
      (a1 a2: AConfig Exp):
      EClosure fenv env a1 a2 ->
      EClosure (fenv ++ fenv') (env ++ env') a1 a2.
Proof.
  intros.
  dependent induction X.
  constructor.
  eapply EStepWeakenA with (fenv':=fenv') (env':=env') in e.
  econstructor.
  exact e.
  exact IHX.
Defined.

Lemma PClosWeakenA 
      (fenv fenv': funEnv) (env env': valEnv)
      (a1 a2: AConfig Prms):
      PClosure fenv env a1 a2 ->
      PClosure (fenv ++ fenv') (env ++ env') a1 a2.
Proof.
  intros.
  dependent induction X.
  constructor.
  eapply PStepWeakenA with (fenv':=fenv') (env':=env') in p.
  econstructor.
  exact p.
  exact IHX.
Defined.


Lemma EClosWeakenA1 
      (fenv: funEnv) (env env': valEnv)
      (a1 a2: AConfig Exp):
      EClosure fenv env a1 a2 ->
      EClosure fenv (env ++ env') a1 a2.
Proof.
  intros.
  dependent induction X.
  constructor.
  eapply EStepWeakenA with (fenv':=nil) (env':=env') in e.
  rewrite app_nil_r in e.
  econstructor.
  exact e.
  exact IHX.
Defined.

Lemma PClosWeakenA1 
      (fenv: funEnv) (env env': valEnv)
      (a1 a2: AConfig Prms):
      PClosure fenv env a1 a2 ->
      PClosure fenv (env ++ env') a1 a2.
Proof.
  intros.
  dependent induction X.
  constructor.
  eapply PStepWeakenA with (fenv':=nil) (env':=env') in p.
  rewrite app_nil_r in p.
  econstructor.
  exact p.
  exact IHX.
Defined.


Lemma EStepWeaken
           (fenv fenv1 fenv2: funEnv) (env env1 env2: valEnv)
           (a1 a2: AConfig Exp):
  EStep fenv1 env1 a1 a2 ->
  fenv = fenv1 ++ fenv2 ->
  env = env1 ++ env2 ->
  EStep fenv env a1 a2.
Proof.
  intros.
  inversion H; subst.
  eapply EStepWeakenA.
  auto.
Defined.  

Lemma PStepWeaken 
           (fenv fenv1 fenv2: funEnv) (env env1 env2: valEnv)
           (a1 a2: AConfig Prms):
  PStep fenv1 env1 a1 a2 ->
  fenv = fenv1 ++ fenv2 ->
  env = env1 ++ env2 ->
  PStep fenv env a1 a2.
  intros.
  inversion H; subst.
  eapply PStepWeakenA.
  auto.
Defined.  

Lemma EClosWeaken 
      (fenv fenv1 fenv2: funEnv) (env env1 env2: valEnv)
      (a1 a2: AConfig Exp):
  EClosure fenv1 env1 a1 a2 ->
  fenv = fenv1 ++ fenv2 ->
  env = env1 ++ env2 ->
  EClosure fenv env a1 a2.
  intros.
  inversion H; subst.
  eapply EClosWeakenA.
  auto.
Defined.  

Lemma PClosWeaken 
      (fenv fenv1 fenv2: funEnv) (env env1 env2: valEnv)
      (a1 a2: AConfig Prms):
  PClosure fenv1 env1 a1 a2 ->
  fenv = fenv1 ++ fenv2 ->
  env = env1 ++ env2 ->
  PClosure fenv env a1 a2.
  intros.
  inversion H; subst.
  eapply PClosWeakenA.
  auto.
Defined.  
  
  
(***************************************************************************)

Lemma EnvrWeaken (T: Type) (env env': Envr Id T) (x: Id) (t: T) :   
 EnvrAssign env x t -> EnvrAssign (env ++ env') x t.
  intros.
  inversion H; subst.
 (* inversion X0; subst. *)
  unfold EnvrAssign.
 (* constructor. *)
  erewrite override_simpl1.
  exact H.
  exact H1.
Defined.  

Lemma IdTWeaken (tenv tenv': valTC) (x: Id) (t: VTyp) : 
  IdTyping tenv x t -> IdTyping (tenv ++ tenv') x t.
  apply EnvrWeaken.
Defined.  

Lemma IdFTWeaken (ftenv ftenv': funTC) (x: Id) (ft: FTyp) : 
  IdFTyping ftenv x ft -> IdFTyping (ftenv ++ ftenv') x ft.
  apply EnvrWeaken.
Defined.  
  
Definition ExpTWeaken_def :
  forall (ftenv: funTC) (tenv: valTC) (e: Exp) (t: VTyp), 
      ExpTyping ftenv tenv e t -> Type
  := fun (ftenv: funTC) (tenv: valTC)
      (e: Exp) (t: VTyp)
      (k: ExpTyping ftenv tenv e t) =>
   forall (ftenv': funTC) (tenv': valTC),
       ExpTyping (ftenv ++ ftenv') (tenv ++ tenv') e t.

Definition PrmsTWeaken_def :
  forall (ftenv: funTC) (tenv: valTC) (ps: Prms) (pt: PTyp),
    PrmsTyping ftenv tenv ps pt -> Type 
  := fun (ftenv: funTC) (tenv: valTC) (ps: Prms) (pt: PTyp)
          (k: PrmsTyping ftenv tenv ps pt) => 
   forall (ftenv': funTC) (tenv': valTC),
       PrmsTyping (ftenv ++ ftenv') (tenv ++ tenv') ps pt.

Definition Weaken_ExpTyping_mut :=
  ExpTyping_mut ExpTWeaken_def PrmsTWeaken_def.
  
Definition Weaken_PrmsTyping_mut :=
  PrmsTyping_mut ExpTWeaken_def PrmsTWeaken_def.


Lemma ExpTWeakenA
         (ftenv: funTC) (tenv: valTC) 
         (e: Exp) (t: VTyp) 
         (k: ExpTyping ftenv tenv e t) :
   forall (ftenv': funTC) (tenv': valTC),
       ExpTyping (ftenv ++ ftenv') (tenv ++ tenv') e t.
  intros.
  eapply Weaken_ExpTyping_mut.
  - intros.
    unfold ExpTWeaken_def.
    intros ftenv1 tenv1.
    constructor.
    exact v0.
  - intros.
    unfold ExpTWeaken_def.
    intros ftenv1 tenv1.
    constructor.
    eapply IdTWeaken.
    exact i.
  - intros.
    unfold ExpTWeaken_def in *.
    intros ftenv1 tenv1.
    econstructor.
    apply X.
    apply X0.
  - intros.
    unfold ExpTWeaken_def in *.
    intros ftenv1 tenv1.
    inversion m0; subst.
    + econstructor.
      eassumption.
      reflexivity.
      apply X.
      rewrite app_comm_cons.
      eapply X0.
    + econstructor.
      eassumption.
      reflexivity.
      apply X.
      simpl.
      rewrite app_comm_cons.
      eapply X0.
  - intros.
    unfold ExpTWeaken_def in *.
    intros ftenv3 tenv3.
    econstructor.
    eassumption.
    reflexivity.
    rewrite e2 in X.
    rewrite app_assoc.
    apply X.
  - intros.
    unfold ExpTWeaken_def in *.
    intros ftenv3 tenv3.
    econstructor.
    apply X.
    apply X0.
    apply X1.
  - intros.
    unfold ExpTWeaken_def, PrmsTWeaken_def in *.
    intros ftenv3 tenv3.
    inversion p; subst.
    + econstructor.
      assumption.
      eapply IdFTWeaken.
      exact i.
      apply X.
      apply X0.
    + econstructor.
      assumption.
      eapply IdFTWeaken.
      exact i.
      apply X.
      apply X0.
  - intros.
    unfold ExpTWeaken_def, PrmsTWeaken_def in *.
    intros ftenv3 tenv3.
    econstructor.
    eapply IdFTWeaken.
    exact i.
    apply X.
  - intros.
    unfold ExpTWeaken_def, PrmsTWeaken_def in *.
    intros ftenv3 tenv3.
    econstructor.
    apply X.
  - intros.
    unfold PrmsTWeaken_def in *.
    intros ftenv3 tenv3.
    constructor.
  - intros.
    unfold PrmsTWeaken_def in *.
    intros ftenv3 tenv3.
    constructor.
    apply X.
    apply X0.
  - exact k.
Defined.    
        
Lemma PrmsTWeakenA
         (ftenv: funTC) (tenv: valTC) 
         (ps: Prms) (pt: PTyp) 
         (k: PrmsTyping ftenv tenv ps pt) :
   forall (ftenv': funTC) (tenv': valTC),
       PrmsTyping (ftenv ++ ftenv') (tenv ++ tenv') ps pt.
  intros.
  eapply Weaken_PrmsTyping_mut.
  - intros.
    unfold ExpTWeaken_def.
    intros ftenv1 tenv1.
    constructor.
    exact v0.
  - intros.
    unfold ExpTWeaken_def.
    intros ftenv1 tenv1.
    constructor.
    eapply IdTWeaken.
    exact i.
  - intros.
    unfold ExpTWeaken_def in *.
    intros ftenv1 tenv1.
    econstructor.
    apply X.
    apply X0.
  - intros.
    unfold ExpTWeaken_def in *.
    intros ftenv1 tenv1.
    inversion m0; subst.
    + econstructor.
      eassumption.
      reflexivity.
      apply X.
      rewrite app_comm_cons.
      eapply X0.
    + econstructor.
      eassumption.
      reflexivity.
      apply X.
      simpl.
      rewrite app_comm_cons.
      eapply X0.
  - intros.
    unfold ExpTWeaken_def in *.
    intros ftenv3 tenv3.
    econstructor.
    eassumption.
    reflexivity.
    rewrite e1 in X.
    rewrite app_assoc.
    apply X.
  - intros.
    unfold ExpTWeaken_def in *.
    intros ftenv3 tenv3.
    econstructor.
    apply X.
    apply X0.
    apply X1.
  - intros.
    unfold ExpTWeaken_def, PrmsTWeaken_def in *.
    intros ftenv3 tenv3.
    inversion p; subst.
    + econstructor.
      assumption.
      eapply IdFTWeaken.
      exact i.
      apply X.
      apply X0.
    + econstructor.
      assumption.
      eapply IdFTWeaken.
      exact i.
      apply X.
      apply X0.
  - intros.
    unfold ExpTWeaken_def, PrmsTWeaken_def in *.
    intros ftenv3 tenv3.
    econstructor.
    eapply IdFTWeaken.
    exact i.
    apply X.
  - intros.
    unfold ExpTWeaken_def, PrmsTWeaken_def in *.
    intros ftenv3 tenv3.
    econstructor.
    apply X.
  - intros.
    unfold PrmsTWeaken_def in *.
    intros ftenv3 tenv3.
    constructor.
  - intros.
    unfold PrmsTWeaken_def in *.
    intros ftenv3 tenv3.
    constructor.
    apply X.
    apply X0.
  - exact k.
Defined.    


Lemma ExpTWeaken
         (ftenv ftenv1 ftenv2: funTC) (tenv tenv1 tenv2: valTC) 
         (e: Exp) (t: VTyp) 
         (k: ExpTyping ftenv1 tenv1 e t) :
  ftenv = ftenv1 ++ ftenv2 ->
  tenv = tenv1 ++ tenv2 ->
  ExpTyping ftenv tenv e t.
  intros.
  inversion H; subst.
  eapply ExpTWeakenA.
  auto.
Defined.
  
Lemma PrmsTWeaken
         (ftenv ftenv1 ftenv2: funTC) (tenv tenv1 tenv2: valTC) 
         (ps: Prms) (pt: PTyp) 
         (k: PrmsTyping ftenv1 tenv1 ps pt) :
  ftenv = ftenv1 ++ ftenv2 ->
  tenv = tenv1 ++ tenv2 ->
  PrmsTyping ftenv tenv ps pt.
  intros.
  inversion H; subst.
  eapply PrmsTWeakenA.
  auto.
Defined.


End Weaken.



