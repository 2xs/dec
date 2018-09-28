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
Require Import DetermI1.
Require Import PreReflI1.
Require Import ReflectI1.
Require Import PreInterI1.

Import ListNotations.


Module InterprBase (IdT: ModTyp) <: ModTyp.

Module PreInterL := PreInter IdT.
Export PreInterL.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Open Scope type_scope.


Program Definition InterpExp2Prms (fenv: funEnv)     
    (ET : forall (tenv: valTC) (e: Exp) (t: VTyp) 
    (k: ExpTyping (funEnv2funTC fenv) tenv e t)
    (sfenv: tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv)))), 
    (valTC_Trans tenv -> MM WW (sVTyp t)))  
    (k1: FEnvWT fenv) (k2: noDup fenv) 
     : forall (tenv: valTC) (ps: Prms) (pt: PTyp) 
     (k: PrmsTyping (funEnv2funTC fenv) tenv ps pt)
     (sfenv: tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv)))),
    (valTC_Trans tenv -> MM WW (PTyp_TRN pt)) := _.
Next Obligation. 
  intros.
  destruct pt.
  destruct ps.
  dependent induction k.
  unfold MM.
  intro.
  
  split.
  unfold PTyp_TRN.
  simpl.
  exact tt.
  exact X0.

  unfold MM.
  intro ww.
  
  generalize ET; intro.
  specialize (ET tenv e t e0 sfenv X ww).
  destruct ET as [v1 ww1].

  specialize (IHk ts0 es0 fenv ET0 k1 k2 eq_refl eq_refl eq_refl sfenv X).
  specialize (IHk ww1).
  destruct IHk as [vs2 ww2].

  split.
  unfold PTyp_TRN.
  simpl.
  split.
  exact v1.
  exact vs2.
  exact ww2.
Defined.
  
  
  
(**************************************************************)

Definition InterpExp0 (fenv: funEnv) (env: valEnv)
                     (e: Exp) (t: VTyp) (s: W) (n: nat) : Type :=
sigT (fun I1: forall (s: W) (n0: nat),
            n0 <= n -> SoundExp fenv env e t s n0 =>   
(**)  
sigT (fun I2: (tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) -> 
                 valTC_Trans ((valEnv2valTC env)) ->                
                 MM WW (sVTyp t)) => 
(**)
sigT (fun FE: nat -> tlist2type
                    (map snd (FunTC_ListTrans (funEnv2funTC fenv))) =>  
(**)
forall (n0: nat) (q: n0 <= n), 
  SOS_Exp1 fenv env e t s n0 (I1 s n0 q) =
     I2 (FE n0) (ValEnvTRN env) (s, n0)))).


Definition InterpPrms0 (fenv: funEnv) (env: valEnv)
                     (ps: Prms) (pt: PTyp) (s: W) (n: nat) : Type := 
sigT (fun I1: forall (s: W) (n0: nat),
            n0 <= n -> SoundPrms fenv env ps pt s n0 =>   
(**)  
sigT (fun I2: (tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) -> 
                 valTC_Trans ((valEnv2valTC env)) ->                
                 MM WW (PTyp_TRN pt)) => 
(**)
sigT (fun FE: nat -> tlist2type
                    (map snd (FunTC_ListTrans (funEnv2funTC fenv))) =>  
(**)
forall (n0: nat) (q: n0 <= n), 
  SOS_Prms fenv env ps pt s n0 (I1 s n0 q) =
     I2 (FE n0) (ValEnvTRN env) (s, n0)))).



Definition InterpExp1 (fenv: funEnv) (env: valEnv)
                     (e: Exp) (t: VTyp) (s: W) (n: nat) : Type :=
forall (n0: nat) (q: n0 <= n),
  sigT (fun I1: 
            SoundExp fenv env e t s n0 =>   
(**)  
sigT (fun I2: (tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) -> 
                 valTC_Trans ((valEnv2valTC env)) ->                
                 MM WW (sVTyp t)) => 
(**)
sigT (fun FE: nat -> tlist2type
                    (map snd (FunTC_ListTrans (funEnv2funTC fenv))) =>  
(**)
  SOS_Exp1 fenv env e t s n0 I1 =
     I2 (FE n0) (ValEnvTRN env) (s, n0)))).


Definition InterpPrms1 (fenv: funEnv) (env: valEnv)
                     (ps: Prms) (pt: PTyp) (s: W) (n: nat) : Type := 
forall (n0: nat) (q: n0 <= n), 
sigT (fun I1: SoundPrms fenv env ps pt s n0 =>   
(**)  
sigT (fun I2: (tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) -> 
                 valTC_Trans ((valEnv2valTC env)) ->                
                 MM WW (PTyp_TRN pt)) => 
(**)
sigT (fun FE: nat -> tlist2type
                    (map snd (FunTC_ListTrans (funEnv2funTC fenv))) =>  
(**)
  SOS_Prms fenv env ps pt s n0 I1 =
     I2 (FE n0) (ValEnvTRN env) (s, n0)))).


(***********************************************************)

Definition ExpSoundness1_def (n: nat) 
   (ftenv: funTC) (tenv: valTC)
   (e: Exp) (t: VTyp) 
   (k: ExpTyping ftenv tenv e t) (s: W) : Type := 
   forall (fenv: funEnv) (env: valEnv) (D: FEnvWT fenv),                      
   FEnvTyping fenv ftenv ->
   EnvTyping env tenv ->
   forall (n0: nat), n0 <= n -> SoundExp fenv env e t s n0.

Definition PrmsSoundness1_def (n: nat) 
   (ftenv: funTC) (tenv: valTC)
   (ps: Prms) (pt: PTyp) 
   (k: PrmsTyping ftenv tenv ps pt) (s: W) : Type :=  
   forall (fenv: funEnv) (env: valEnv) (D: FEnvWT fenv),                      
   FEnvTyping fenv ftenv ->
   EnvTyping env tenv ->
   forall (n0: nat), n0 <= n -> SoundPrms fenv env ps pt s n0.  


(************************************************)


Lemma ValEnvTRN3 (tenv: valTC) (env: valEnv)
      (m: EnvTyping env tenv) : valTC_Trans tenv.
  intros.
  inversion m; subst.
  eapply ValEnvTRN.
Defined.  


Lemma InterpExp2Prms_Z (ftenv: funTC) (fenv: funEnv)
    (m: FEnvTyping fenv ftenv)    
    (ET : forall (tenv: valTC) (e: Exp) (t: VTyp) 
          (k: ExpTyping ftenv tenv e t)
          (sfenv: tlist2type (map snd (FunTC_ListTrans ftenv))), 
        (valTC_Trans tenv -> MM WW (sVTyp t))) 
    (k1: FEnvWT fenv) (k2: noDup fenv) 
     : forall (tenv: valTC) (ps: Prms) (pt: PTyp) 
          (k: PrmsTyping ftenv tenv ps pt)
          (sfenv: tlist2type (map snd (FunTC_ListTrans ftenv))),
    (valTC_Trans tenv -> MM WW (PTyp_TRN pt)).
  intros.
  inversion m; subst.
  eapply InterpExp2Prms.
  eassumption.
  assumption.
  assumption.
  eassumption.
  assumption.
  assumption.
Defined.  

(******************************************************************)
(* not used *)

(** other version in TransPrelim *)

Lemma extract_from_funTC_Trans3 (ftenv: funTC)
      (sftenv : list (Id * Type))
      (sfenv: tlist2type (map snd sftenv))             
      (x: Id) (ft: FTyp) (k: findE ftenv x = Some ft) :
  sftenv = FunTC_ListTrans ftenv ->
  FTyp_TRN2 ft.
  intros.
  unfold FTyp_TRN2.
  unfold FType_mk2.
  unfold FunTC_ListTrans in H.
  unfold FTyp_TRN2 in H.
  unfold FType_mk2 in H.
  rewrite H in sfenv.
  rewrite map_map in sfenv.
  simpl in sfenv.
  clear H.
  clear sftenv.
  induction ftenv.
  inversion k.
  intros.
  simpl in *.
  destruct a.
  destruct (IdT.IdEqDec x i).
  inversion e; subst.
  inversion k; subst.
  clear k H.
  simpl in sfenv.
  destruct sfenv.
  eapply (m X).
  simpl in *.
  destruct sfenv.
  specialize (IHftenv t k).
  eapply (IHftenv X).
Defined.  
  

Lemma extract_from_funTC_Trans4 (fenv: funEnv)
      (sftenv : list (Id * Type))
      (sfenv: tlist2type (map snd sftenv))             
      (x: Id) (f: Fun)
      (H: sftenv = FunTC_ListTrans (map (thicken StaticSemL.Id funFTyp) fenv)) 
      (k: findE fenv x = Some f) :
  FTyp_TRN2 (funFTyp f).
  intros.
  unfold FTyp_TRN2.
  unfold FType_mk2.
  unfold FunTC_ListTrans in H.
  unfold FTyp_TRN2 in H.
  unfold FType_mk2 in H.
  rewrite H in sfenv.
  rewrite map_map in sfenv.
  simpl in sfenv.
  clear H.
  clear sftenv.
  induction fenv.
  inversion k.
  intros.
  simpl in *.
  destruct a.
  destruct (IdT.IdEqDec x i).
  inversion e; subst.
  inversion k; subst.
  clear k H.
  simpl in sfenv.
  destruct sfenv.
  eapply (m X).
  simpl in *.
  destruct sfenv.
  specialize (IHfenv t k).
  eapply (IHfenv X).
Defined.  



Lemma extract_from_funTC_Trans5 (ftenv: funTC)
      (sftenv : list (Id * Type))
      (sfenv: tlist2type (map snd sftenv))             
      (x: Id) (ft: FTyp) :
  sftenv = FunTC_ListTrans ((x,ft)::ftenv) ->
  FTyp_TRN2 ft.
  revert sfenv.
  revert sftenv.
  intros.
  inversion H; subst.
  simpl in sfenv.
  exact (fst sfenv).
Defined.  


Lemma extract_from_funTC_Trans6 (ftenv: funTC) (x: Id) (ft: FTyp)
      (sfenv: tlist2type (map snd (FunTC_ListTrans ((x,ft)::ftenv))))    
      :
  FTyp_TRN2 ft.
  intros.
  simpl in sfenv.
  exact (fst sfenv).
Defined.  
  

Lemma extract_from_funTC_TransS1 (ftenv: funTC)
      (sftenv : list (Id * Type))
      (sfenv: tlist2type (map snd (FunTC_ListTrans ftenv)))             
      (x: Id) (ft: FTyp) (k: findE ftenv x = Some ft) :
  FTyp_TRN2 ft.
  revert sfenv.
  revert sftenv.
  induction ftenv.
  - intros.
    simpl in *.
    inversion k.
  - destruct a as [x0 ft0].
    destruct ft.
    intros.
    simpl in k.
    destruct (IdT.IdEqDec x x0) in k.
    + inversion e; subst.
      inversion k; subst.
      simpl in *.
      intro X.
      eapply (fst sfenv).
      exact X.
    + specialize (IHftenv k).
      specialize (IHftenv (FunTC_ListTrans ftenv)).
      simpl in *.
      intros.
      specialize (IHftenv (snd sfenv)).
      eapply IHftenv.
Defined.      


Lemma extract_from_funTC_Trans3A (ftenv: funTC)
      (sfenv: tlist2type (map snd (FunTC_ListTrans ftenv)))             
      (x: Id) (ft: FTyp) (k: findE ftenv x = Some ft) :
  FTyp_TRN2 ft.
  intros.
  unfold FTyp_TRN2.
  unfold FType_mk2.
  unfold FunTC_ListTrans in sfenv.
  unfold FTyp_TRN2 in sfenv.
  unfold FType_mk2 in sfenv.
  rewrite map_map in sfenv.
  simpl in sfenv.
  induction ftenv.
  inversion k.
  intros.
  simpl in *.
  destruct a.
  destruct (IdT.IdEqDec x i).
  inversion e; subst.
  inversion k; subst.
  clear k H.
  simpl in sfenv.
  destruct sfenv.
  eapply (m X).
  simpl in *.
  destruct sfenv.
  specialize (IHftenv t k).
  eapply (IHftenv X).
Defined.  

Lemma extract_from_funTC_Trans4A (fenv: funEnv)
  (sfenv: tlist2type
    (map snd (FunTC_ListTrans (map (thicken StaticSemL.Id funFTyp) fenv))))     
      (x: Id) (f: Fun)
      (k: findE fenv x = Some f) :
  FTyp_TRN2 (funFTyp f).
  intros.
  unfold FTyp_TRN2.
  unfold FType_mk2.
  unfold FunTC_ListTrans in sfenv.
  unfold FTyp_TRN2 in sfenv.
  unfold FType_mk2 in sfenv.
  rewrite map_map in sfenv.
  simpl in sfenv.
  induction fenv.
  inversion k.
  intros.
  simpl in *.
  destruct a.
  destruct (IdT.IdEqDec x i).
  inversion e; subst.
  inversion k; subst.
  clear k H.
  simpl in sfenv.
  destruct sfenv.
  eapply (m X).
  simpl in *.
  destruct sfenv.
  specialize (IHfenv t k).
  eapply (IHfenv X).
Defined.  


Lemma extract_from_funTC_Trans4B (fenv: funEnv) (x0 x1: Id) (f0 f1: Fun)
  (sfenv: tlist2type
            (map snd (FunTC_ListTrans (map (thicken StaticSemL.Id funFTyp)
                                           ((x1,f1)::fenv)))))     
      (k: findE fenv x0 = Some f0) (k0: x0 <> x1) :
  FTyp_TRN2 (funFTyp f0).
  intros.
  assert (findE ((x1,f1)::fenv) x0 = Some f0). 
  simpl.
  destruct (IdT.IdEqDec x0 x1).
  rewrite e in k0.
  intuition k0.
  exact k.
  eapply (extract_from_funTC_Trans4A ((x1, f1) :: fenv) sfenv x0 f0 H).
Defined.  
  

(************************************************************************)

(* not used *)

Lemma SoundExp_BindN : forall (n n1: nat) (s s1: W)
    (fenv : funEnv) (env : valEnv)
    (e1 e2 : Exp) (v: Value) 
    (t1 t2 : VTyp),
  EClosure fenv env (Conf Exp s n e1)
         (Conf Exp s1 n1 (Val v)) ->
  SoundExp fenv env e2 t2 s1 n1 ->
  SoundExp fenv env (BindN e1 e2) t2 s n.
    unfold SoundExp.
    intros.
    destruct X0 as [v2 m3 X0].
    destruct X0 as [w2 X0].
    constructor 1 with (x:=v2).
    assumption.
    destruct w2 as [s2 n2].
    constructor 1 with (x:=(s2,n2)).
    simpl in *.
    eapply BindN_FStep.
    eassumption. 
    assumption.
Defined.    


Lemma SoundExp_BindS : forall (n n1: nat) (s s1: W)
    (fenv : funEnv) (env : valEnv)
    (e1 e2 : Exp) (v: Value) (x: Id) (m: option VTyp)
    (t1 t2 : VTyp),
  EClosure fenv env (Conf Exp s n e1)
         (Conf Exp s1 n1 (Val v)) ->
  SoundExp fenv ((x,v)::env) e2 t2 s1 n1 ->
  SoundExp fenv env (BindS x m e1 e2) t2 s n.
    unfold SoundExp.
    intros.
    destruct X0 as [v2 m3 X0].
    destruct X0 as [w2 X0].
    constructor 1 with (x:=v2).
    assumption.
    destruct w2 as [s2 n2].
    constructor 1 with (x:=(s2,n2)).
    simpl in *.
    eapply BindS_FStep.
    eassumption. 
    assumption.
Defined.    



Lemma SoundExp_BindMS : forall (n n1: nat) (s s1: W)
    (fenv : funEnv) (env env0: valEnv)
    (e : Exp) 
    (t : VTyp)
    (v: Value)
    (m1 : VTyping v t),
  EClosure fenv (env0++env) (Conf Exp s n e)
         (Conf Exp s1 n1 (Val v)) ->
  SoundExp fenv env (BindMS env0 e) t s n.
    unfold SoundExp.
    intros.
    constructor 1 with (x:=v).
    assumption.
    constructor 1 with (x:=(s1,n1)).
    simpl in *.
    eapply BindMS_FStep.
    eassumption. 
Defined.    


Lemma SoundExp_IfThenElse10 : forall (n n1: nat) (s s1: W)
    (fenv : funEnv) (env : valEnv)
    (e1 e2 : Exp) (v: Value) 
    (t : VTyp)
    (m1 : VTyping v t),
  EClosure fenv env (Conf Exp s n e1)
         (Conf Exp s1 n1 (Val v)) ->
  SoundExp fenv env (IfThenElse (Val (cst Bool true)) e1 e2) t s n.
    unfold SoundExp.
    intros.
    constructor 1 with (x:=v).
    assumption.
    constructor 1 with (x:=(s1,n1)).
    simpl in *.
    eapply IfThenElse_FStep1.
    econstructor.
    assumption. 
Defined.    

Lemma SoundExp_IfThenElse20 : forall (n n1: nat) (s s1: W)
    (fenv : funEnv) (env : valEnv)
    (e1 e2 : Exp) (v: Value) 
    (t : VTyp)
    (m1 : VTyping v t),
  EClosure fenv env (Conf Exp s n e2)
         (Conf Exp s1 n1 (Val v)) ->
  SoundExp fenv env (IfThenElse (Val (cst Bool false)) e1 e2) t s n.
    unfold SoundExp.
    intros.
    constructor 1 with (x:=v).
    assumption.
    constructor 1 with (x:=(s1,n1)).
    simpl in *.
    eapply IfThenElse_FStep2.
    econstructor.
    assumption. 
Defined.    

Lemma SoundExp_IfThenElse1 : forall (n n1: nat) (s s1: W)
    (fenv : funEnv) (env : valEnv)
    (e1 e2 e3: Exp) 
    (t : VTyp),
  EClosure fenv env (Conf Exp s n e1)
           (Conf Exp s1 n1 (Val (cst Bool true))) -> 
  SoundExp fenv env e2 t s1 n1 ->
  SoundExp fenv env (IfThenElse e1 e2 e3) t s n.
    unfold SoundExp.
    intros.
    destruct X0 as [v2 m3 X0].
    destruct X0 as [w2 X0].
    
    constructor 1 with (x:=v2).
    assumption.
    constructor 1 with (x:=w2).
    destruct w2.
    simpl in *.
    eapply IfThenElse_FStep1.
    eassumption.
    assumption. 
Defined.

Lemma SoundExp_IfThenElse2 : forall (n n1: nat) (s s1: W)
    (fenv : funEnv) (env : valEnv)
    (e1 e2 e3: Exp) 
    (t : VTyp),
  EClosure fenv env (Conf Exp s n e1)
           (Conf Exp s1 n1 (Val (cst Bool false))) -> 
  SoundExp fenv env e3 t s1 n1 ->
  SoundExp fenv env (IfThenElse e1 e2 e3) t s n.
    unfold SoundExp.
    intros.
    destruct X0 as [v2 m3 X0].
    destruct X0 as [w2 X0].
    
    constructor 1 with (x:=v2).
    assumption.
    constructor 1 with (x:=w2).
    destruct w2.
    simpl in *.
    eapply IfThenElse_FStep2.
    eassumption.
    assumption. 
Defined.    


Lemma SoundExp_Call0 : forall (s: W) (ftenv: funTC)
                             (fenv : funEnv) (env : valEnv)
                            (* (k1: FEnvWT fenv) (k2: noDup fenv) *)
                             (x: Id) (ps: Prms)  
                             (pt: PTyp) (t : VTyp)
                             (m: FEnvTyping fenv ftenv), 
        IdFTyping ftenv x (FT pt t) -> 
        SoundPrms fenv env ps pt s 0 ->            
        SoundExp fenv env (Call x ps) t s 0.     
    unfold SoundPrms, SoundExp.
    intros.
    rename X into X0.
    rename H into X.
    destruct X0 as [es2 X0].
    destruct X0 as [vs2 m3 X0].
    destruct X0 as [m4 X0].
    destruct X0 as [w2 X0].
    unfold IdFTyping in X.
    unfold EnvrAssign in X.
    generalize X.
    intro X2.
    eapply ExtRelVal2 with (f:=funFTyp) (venv:=fenv) in X.
    destruct X as [f m5].
    
    destruct f.
    econstructor 1 with (x:=v).

    inversion e; subst.
    reflexivity.
    
    econstructor 1 with (x:=w2).
    destruct w2.
    simpl in *.
    eapply EClosConcat.
    instantiate (1:=(Conf Exp w n (Call x (PS es2)))).
    eapply Call_extended_congruence.
    exact X0.
    inversion m3; subst.
    assert (n <= 0).
    eapply PrmsDecrease.
    exact X0.
    assert (n = 0).
    omega.
    inversion H0; subst.
    clear H1.
    eapply StepIsEClos.
    econstructor.
    exact m5.
    exact m3.
    unfold funArity.
    destruct pt.
    inversion e; subst.
    eapply PrmsArity_lemma in m4.
    rewrite lengthVal in m4.
    rewrite lengthSnd in m4.
    symmetry.
    exact m4.
    reflexivity.
    simpl.
    reflexivity.
    exact m.
Defined.

Lemma SoundExp_Call01 : forall (s0 s1: W) (n1: nat) (ftenv: funTC)
                             (fenv : funEnv) (env : valEnv)
                             (x: Id) (ps: Prms)  
                             (pt: PTyp) (t : VTyp)
                             (m: FEnvTyping fenv ftenv) 
                             (X: IdFTyping ftenv x (FT pt t))
                             (vs: list Value)
  (m4 : PrmsTyping emptyE emptyE (PS (map Val vs)) pt)
  (X0 : PClosure fenv env (Conf Prms s0 0 ps)
                          (Conf Prms s1 n1 (PS (map Val vs)))),
        SoundExp fenv env (Call x ps) t s0 0.     
    unfold SoundExp.
    intros.
    unfold IdFTyping in X.
    unfold EnvrAssign in X.
    generalize X.
    intro X2.
    eapply ExtRelVal2 with (f:=funFTyp) (venv:=fenv) in X.
    destruct X as [f m5].
    
    destruct f.
    econstructor 1 with (x:=v).

    inversion e; subst.
    reflexivity.
    econstructor 1 with (x:=(s1,n1)).
    simpl in *.
    eapply EClosConcat.
    instantiate (1:=(Conf Exp s1 n1 (Call x (PS (map Val vs))))).
    eapply Call_extended_congruence.
    exact X0.
    assert (n1 <= 0).
    eapply PrmsDecrease.
    exact X0.
    assert (n1 = 0).
    omega.
    inversion H0; subst.
    clear H1.
    eapply StepIsEClos.
    econstructor.
    exact m5.
    instantiate (1:=vs).
    constructor.
    unfold funArity.
    destruct pt.
    inversion e; subst.
    eapply PrmsArity_lemma in m4.
    rewrite lengthVal in m4.
    rewrite lengthSnd in m4.
    symmetry.
    exact m4.
    reflexivity.
    simpl.
    reflexivity.
    exact m.
Defined.


Lemma SoundExp_Call02 : forall (s0 s1: W) (ftenv: funTC)
                               (fenv : funEnv)
                               (tenv : valTC) (env : valEnv)
                             (x: Id) (ps: Prms)  
                             (pt: PTyp) (t : VTyp)
                             (m: FEnvTyping fenv ftenv) 
                             (m0: EnvTyping env tenv) 
                             (vs: list Value) (f: Fun)
  (m4 : PrmsTyping ftenv tenv (PS (map Val vs)) pt)
  (X0 : PClosure fenv env (Conf Prms s0 0 ps)
                 (Conf Prms s1 0 (PS (map Val vs))))
  (k3: findE fenv x = Some f)
  (X: funFTyp f = FT pt t), 
    sigT (fun I : SoundExp fenv env (Call x ps) t s0 0 =>
            (proj1_of_sigT2 I = fun0Exp f) *
            (projT1 (projT2 (snd_sigT_of_sigT2 I)) = (s1, 0))).    
    unfold SoundExp.
    intros.
    
    destruct f.

    assert ({v0 : Value & (VTyping v0 t * (v0 = v)) &
    {x0 : TSoundnessL.W * nat & x0 = (s1,0) &
    EClosure fenv env (Conf Exp s0 0 (Call x ps))
      (Conf Exp (fst x0) (snd x0) (Val v0))}}) as X1.
    
    econstructor 1 with (x:=v).
    split.

    inversion X; subst.
    reflexivity.
    reflexivity.
    econstructor 1 with (x:=(s1,0)).
    reflexivity.
    simpl.
    eapply EClosConcat.
    eapply Call_extended_congruence.
    exact X0.
    eapply StepIsEClos.
    econstructor.
    exact k3.
    unfold isValueList2T.
    reflexivity.
    unfold funArity.
    unfold funFTyp in X.
    inversion X; subst.
    generalize m4; intro m5.
    eapply PrmsArity_lemma in m5.
    rewrite map_length in m5.
    rewrite map_length in m5.
    symmetry.
    exact m5.  
    reflexivity.
    reflexivity.

    destruct X1.
    destruct p.
    destruct s.

    econstructor 1 with (x:=
       existT2 _ _ x0 v0 (existT _ x1 e2)).                     
    simpl.
    split.
    unfold proj1_of_sigT2.
    simpl.
    exact e0.
    exact e1.
Defined.    


(*******************************************************************)

Program Fixpoint ValEnvTRN_extend_P (env0 env: valEnv)
        (senv: valTC_Trans (valEnv2valTC env)) :
  valTC_Trans (valEnv2valTC (env0 ++ env)) := _.
Next Obligation.
  intros.
  unfold valTC_Trans.
  unfold VTList_Trans.
  unfold TList_Type.
  unfold valEnv2valTC.
  unfold VTyp_Trans.
  unfold thicken.
  unfold valueVTyp.
  induction env0.
  exact senv.

  destruct a.
  simpl in *.
  split.
  exact (sValue v).
  eapply IHenv0.
Defined.  


Definition ValEnvTRN_extend : forall (env0 env: valEnv),
             valTC_Trans (valEnv2valTC env) ->
             valTC_Trans (valEnv2valTC (env0 ++ env)) :=
fun (env0 env : valEnv) (senv : valTC_Trans (valEnv2valTC env)) =>
  list_rect
   (fun env1 : list (LangSpecL.Id * Value) =>
    tlist2type
      (map (fun t : VTyp => sVTyp t)
         (map snd
            (map (fun p : StaticSemL.Id * Value => (fst p, projT1 (snd p)))
               (env1 ++ env))))) senv
   (fun (a : LangSpecL.Id * Value) (env1 : list (LangSpecL.Id * Value))
      (IHenv0 : tlist2type
                  (map (fun t : VTyp => sVTyp t)
                     (map snd
                        (map
                           (fun p : StaticSemL.Id * Value =>
                            (fst p, projT1 (snd p))) 
                           (env1 ++ env))))) =>
    let
      (i, v) as p
       return
         (tlist2type
            (map (fun t : VTyp => sVTyp t)
               (map snd
                  (map
                     (fun p0 : StaticSemL.Id * Value =>
                      (fst p0, projT1 (snd p0))) ((p :: env1) ++ env))))) :=
      a in
    (sValue v, IHenv0)) env0.


Lemma ValEnvTRN_lemma (env0 env: valEnv) :
  ( ValEnvTRN (env0 ++ env) =
             ValEnvTRN_extend env0 env (ValEnvTRN env) ).
  induction env0.
  simpl.
  reflexivity.
  destruct a.
  simpl in *.
  rewrite IHenv0.
  reflexivity.
Defined.


Lemma iiiAux (y: Id) (t: Type) (ct: CTyp t) (v: t) (e: Exp) (fenv: funEnv)
              (tenv0: valTC) :
      IdFTyping
        (thicken StaticSemL.Id funFTyp
           (y,
           FC tenv0 (existT ValueI (VT t ct) (Cst (VT t ct) v)) e)
         :: map (thicken StaticSemL.Id funFTyp) fenv) y
        (FT (PT (map snd tenv0)) (VT t ct)).
  unfold IdFTyping.
  unfold EnvrAssign.
  simpl.
  destruct (IdT.IdEqDec y y).
  reflexivity.
  intuition n.
Defined.  


Definition SoundExp_Call01TYPEsp1 (s0: W) (ftenv: funTC)
                             (fenv : funEnv) (env : valEnv)
                             (y: Id) (f: Fun)     
                             (t: VTyp)
                             (k: funFTyp f = FT (PT []) t)
(m: FEnvTyping ((y, f) :: fenv)
    (map (thicken StaticSemL.Id funFTyp) ((y, f) :: fenv)))  
(X: IdFTyping (map (thicken StaticSemL.Id funFTyp) ((y,f)::fenv))
              y (FT (PT []) t)) :=
  SoundExp_Call01 s0 s0 0 (map (thicken StaticSemL.Id funFTyp) ((y,f)::fenv))
                  ((y,f)::fenv) env y (PS []) (PT []) t m X []
                  (PSNil_Typing emptyE emptyE)
                  (PrmsC_Base ((y,f)::fenv) env (Conf Prms s0 0 (PS []))).

Lemma SoundExp_Call01_esp (s0: W) (ftenv: funTC)
                             (fenv : funEnv) (env : valEnv)
                             (y: Id) (f: Fun)     
                             (t: VTyp)
                             (k: funFTyp f = FT (PT []) t)
(m: FEnvTyping ((y, f) :: fenv)
    (map (thicken StaticSemL.Id funFTyp) ((y, f) :: fenv)))  
(X: IdFTyping (map (thicken StaticSemL.Id funFTyp) ((y,f)::fenv))
              y (FT (PT []) t)) :
  {v : Value & VTyping v t &
  {x0 : TSoundnessL.W * nat &
  EClosure ((y,f)::fenv) env (Conf Exp s0 0 (Call y (PS [])))
    (Conf Exp (fst x0) (snd x0) (Val v))}}.
  intros.
  destruct f.
  inversion k; subst.
  apply map_eq_nil in H0.
  inversion H0; subst.
  clear H.
  unfold funFTyp in k.
  econstructor 1 with (x:=v).

  assert (findE ((y, FC [] v e) :: fenv) y = Some (FC [] v e)).
  simpl.
  destruct (IdT.IdEqDec y y).
  auto.
  intuition.

  reflexivity.
  econstructor 1 with (x:=(s0,0)).
  simpl.
  eapply StepIsEClos.
  econstructor.
  simpl.
  destruct (IdT.IdEqDec y y).
  reflexivity.
  intuition.
  unfold isValueList2T.
  instantiate (1:=[]).
  unfold map.
  auto.
  unfold funArity.
  auto.
  reflexivity.
  unfold fun0Exp.
  auto.
Defined.


(*******************************************************************)

Lemma funTrnType_lemma (f: Fun) :
  sVTyp (projT1 (fun0Exp f)) = snd (FTyp_TRN (funFTyp f)).
  destruct f.
  reflexivity.
Defined.  


Lemma ftypFrom_lemma (fenv : funEnv)
     (x : Id)
     (f : Fun) (kk : findE fenv x = Some f) :
     findE (map (thicken StaticSemL.Id funFTyp) fenv) x = Some (funFTyp f). 
  destruct f.
  destruct v.
  simpl in *.
  induction fenv.
  inversion kk.
  destruct a.
  simpl in *.
  destruct (IdT.IdEqDec x i).
  clear IHfenv.
  inversion e0; subst.
  destruct f.
  inversion kk; subst.
  simpl.
  reflexivity.
  eapply IHfenv.
  eapply kk.
Defined.  
  

(**********************************************************************)

Lemma deptyp_aux1 (f: Fun) (env: valEnv) (k1: EnvTyping env (funValTC f)) :
  valTC_Trans (valEnv2valTC env) = tlist2type (fst (FTyp_TRN (funFTyp f))).   
  unfold valTC_Trans.
  unfold FTyp_TRN.
  destruct f.
  simpl.
  unfold VTList_Trans.
  unfold TList_Type.
  unfold VTyp_Trans.
  inversion k1; subst.
  simpl in *.
  inversion H; subst.
  rewrite map_map.
  rewrite map_map.
  rewrite map_map.
  simpl.
  f_equal.
  unfold valEnv2valTC.
  rewrite map_map.
  simpl.
  reflexivity.
Defined.  

Lemma deptyp_aux2 (f: Fun) :
  sVTyp (projT1 (fun0Exp f)) = snd (FTyp_TRN (funFTyp f)).
  destruct f.
  simpl.
  reflexivity.
Defined.  


(** good. 
DEPTYP idea: replace the equality parameters, and work
through by simplification on them *)
Lemma extract_from_funTC_Trans4AA (fenv: funEnv)
      (x: Id) (f: Fun)
      (env: valEnv)
  (m: EnvTyping env (funValTC f))    
  (te1: valTC_Trans (valEnv2valTC env) =
        tlist2type (fst (FTyp_TRN (funFTyp f))))
  (te2: sVTyp (projT1 (fun0Exp f)) = snd (FTyp_TRN (funFTyp f)))
      (k: findE fenv x = Some f) :
  sigT (fun I : FTyp_TRN2 (funFTyp f) =>
          forall s: W, I (match te1 with eq_refl => ValEnvTRN env end) (s, 0) =
               match te2 with eq_refl => (sValue (fun0Exp f), (s, 0)) end).
  intros.
  replace te1 with (deptyp_aux1 f env m).
  clear te1.
  replace te2 with (deptyp_aux2 f).
  unfold FTyp_TRN2.
  unfold FType_mk2.
  econstructor 1 with (x:= preZero f).
  intros.
  unfold preZero.
  destruct f.
  unfold deptyp_aux2.
  reflexivity.
  
  unfold deptyp_aux2.
  destruct f.
  dependent destruction te2.
  auto.

  destruct f.
  destruct (deptyp_aux1 (FC tenv v e) env m).
  dependent destruction te1.
  reflexivity.
Defined.  

(*********************************************************************)


Lemma deptyp_aux11 (tenv: valTC) (vs: list Value) :
      tenv = map (thicken Id valueVTyp) (mkVEnv tenv vs) ->
      (PTyp_TRN (PT (map snd tenv)) =
       valTC_Trans (valEnv2valTC (mkVEnv tenv vs))).
Proof. 
    intros.
    rewrite H.
    unfold PTyp_TRN.
    unfold valTC_Trans.
    unfold VTList_Trans.
    unfold TList_Type.
    unfold PTyp_ListTrans.
    unfold VTyp_Trans.
    unfold valEnv2valTC.
    unfold valueVTyp.
    unfold sVTyp.
    rewrite map_map.
    rewrite map_map.
    rewrite map_map.
    rewrite map_map.
    f_equal.
    f_equal.
    f_equal.
    exact H.
Defined.    


Lemma deptyp_aux12 (fenv: funEnv) (env: valEnv) (tenv0: valTC)
      (vs: list Value)
      (kp: PrmsTyping (funEnv2funTC fenv)
                      (valEnv2valTC env) (PS (map Val vs)) (PT (map snd tenv0)))
      (w0 w1: WW) :
  forall (qq: valTC_Trans (valEnv2valTC (mkVEnv tenv0 vs)) =
              PTyp_TRN (PT (map snd tenv0))), 
          {I2
      : valTC_Trans (valEnv2valTC env) ->
        MM WW (PTyp_TRN (PT (map snd tenv0))) &
  (Eval_vls (map snd tenv0) vs
      (matchListsAux02_T (funEnv2funTC fenv)
         (valEnv2valTC env) (map snd tenv0) (map Val vs) vs eq_refl kp), w1) =
  I2 (ValEnvTRN env) w0} =
    {I2
      : valTC_Trans (valEnv2valTC env) ->
        MM WW (valTC_Trans (valEnv2valTC (mkVEnv tenv0 vs))) &
  (Eval_vls (map snd tenv0) vs
      (matchListsAux02_T (funEnv2funTC fenv)
         (valEnv2valTC env) (map snd tenv0) (map Val vs) vs eq_refl kp), w1) =
   match qq with eq_refl => I2 (ValEnvTRN env) w0 end}.           
  intros.
  revert qq.
  assert (tenv0 = map (thicken Id valueVTyp) (mkVEnv tenv0 vs)) as k.
  eapply mkVEnv_lemma2.
  eauto.
(*  inversion kp. *)
  rewrite <- (deptyp_aux11 tenv0 vs k).
  intro.
  dependent destruction qq.
  auto.
Defined.


Lemma deptyp_aux13 (fenv: funEnv) (env: valEnv) (tenv0: valTC)
      (vs: list Value)
      (kp: PrmsTyping (funEnv2funTC fenv)
                      (valEnv2valTC env) (PS (map Val vs)) (PT (map snd tenv0)))
      (w0 w1: WW) :
  forall (qq: PTyp_TRN (PT (map snd tenv0)) =
         valTC_Trans (valEnv2valTC (mkVEnv tenv0 vs))), 
    {I2 : valTC_Trans (valEnv2valTC env) ->
          MM WW (PTyp_TRN (PT (map snd tenv0))) &
  I2 (ValEnvTRN env) w0 =         
  (Eval_vls (map snd tenv0) vs
      (matchListsAux02_T (funEnv2funTC fenv)
         (valEnv2valTC env) (map snd tenv0) (map Val vs) vs eq_refl kp), w1) 
  } =
    {I2 : valTC_Trans (valEnv2valTC env) ->
        MM WW (valTC_Trans (valEnv2valTC (mkVEnv tenv0 vs))) &
        I2 (ValEnvTRN env) w0 =
        match qq with eq_refl =>
  (Eval_vls (map snd tenv0) vs
      (matchListsAux02_T (funEnv2funTC fenv)
          (valEnv2valTC env) (map snd tenv0) (map Val vs) vs eq_refl kp), w1)
        end}.           
  intros.
  revert qq.
  assert (tenv0 = map (thicken Id valueVTyp) (mkVEnv tenv0 vs)) as k.
  eapply mkVEnv_lemma2.
  eauto.
  rewrite <- (deptyp_aux11 tenv0 vs k).
  intro.
  
  dependent destruction qq.
  f_equal.
Defined.


(*************************************************************************)

Lemma deptyp_aux3a (f: Fun) (vs: list Value)
          (k: vlsTyping vs (map snd (funValTC f))) :
           valTC_Trans (valEnv2valTC (mkVEnv (funValTC f) vs)) =
           tlist2type (fst (FTyp_TRN (funFTyp f))).
  unfold valTC_Trans.
  unfold FTyp_TRN.
  unfold VTList_Trans.
  unfold TList_Type.
  destruct f.
  simpl in *.
  dependent induction k.
  symmetry in x.
  eapply map_eq_nil in x.
  inversion x; subst.
  simpl.
  reflexivity.
  destruct tenv.
  simpl in x.
  inversion x.
  simpl in x.
  destruct p.
  simpl in *.
  inversion x; subst.
  unfold VTyp_Trans.
  inversion r; subst.
  f_equal.
  eapply IHk.
  reflexivity.
Defined.

Lemma deptyp_aux3b (f: Fun) (vs: list Value)
          (k: vlsTyping vs (map snd (funValTC f))) :
           valTC_Trans (valEnv2valTC (mkVEnv (funValTC f) vs)) =
           tlist2type (fst (FTyp_TRN (funFTyp f))).
  unfold valTC_Trans.
  unfold FTyp_TRN.
  unfold VTList_Trans.
  unfold TList_Type.
  destruct f.
  simpl in *.
  f_equal.
  f_equal.
  f_equal.
  unfold valEnv2valTC.
  unfold vlsTyping in k.
  unfold mkVEnv.
  unfold thicken.
  
  revert k.
  revert tenv.
  induction vs.
  intros.
  inversion k; subst.
  symmetry in H.
  eapply map_eq_nil in H.
  inversion H; subst.
  simpl.
  reflexivity.
  intros.
  inversion k; subst.
  destruct tenv.
  simpl.
  reflexivity.
  simpl.
  destruct p.
  simpl in H2.
  inversion H2; subst.
  simpl.
  inversion H0; subst.
  rewrite IHvs.
  reflexivity.
  exact X.
Defined.  
  
Lemma deptyp_aux3c (f: Fun) (vs: list Value)
          (k: vlsTyping vs (map snd (funValTC f))) :
           valTC_Trans (valEnv2valTC (mkVEnv (funValTC f) vs)) =
           tlist2type (fst (FTyp_TRN (funFTyp f))).
  unfold valTC_Trans.
  unfold FTyp_TRN.
  unfold VTList_Trans.
  unfold TList_Type.
  destruct f.
  simpl in *.
  f_equal.
  f_equal.
  f_equal.
  unfold valEnv2valTC.
  unfold vlsTyping in k.
  unfold mkVEnv.
  unfold thicken.
  
  dependent induction k.
  symmetry in x.
  eapply map_eq_nil in x.
  inversion x; subst.
  simpl.
  reflexivity.
  destruct tenv.
  simpl.
  reflexivity.
  simpl.
  destruct p.
  simpl in x.
  inversion x; subst.
  simpl.
  inversion r; subst.
  rewrite IHk.
  reflexivity.
  reflexivity.
Defined.  


Lemma deptyp_aux3d (tenv : valTC) (vs: list Value)
          (k: vlsTyping vs (map snd tenv)) :
           valTC_Trans (valEnv2valTC (mkVEnv tenv vs)) =
           tlist2type (map (fun t : VTyp => sVTyp t) (map snd tenv)).
  unfold valTC_Trans.
  f_equal.
  f_equal.
  f_equal.
  unfold valEnv2valTC.
  unfold vlsTyping in k.
  unfold mkVEnv.
  unfold thicken.
  
  revert k.
  revert tenv.
  induction vs.
  intros.
  inversion k; subst.
  symmetry in H.
  eapply map_eq_nil in H.
  inversion H; subst.
  simpl.
  reflexivity.
  intros.
  inversion k; subst.
  destruct tenv.
  simpl.
  reflexivity.
  simpl.
  destruct p.
  simpl in H2.
  inversion H2; subst.
  simpl.
  inversion H0; subst.
  rewrite IHvs.
  reflexivity.
  exact X.
Defined.  


Lemma deptyp_aux4 (tenv: valTC) (vs: list Value)
    (kp: Forall2T VTyping vs (map snd tenv)) : 
    tlist2type
          (map (fun t : VTyp => sVTyp t)
               (map snd (valEnv2valTC (interleave (map fst tenv) vs)))) =
         tlist2type (map (fun t : VTyp => sVTyp t) (map snd tenv)).      
  f_equal.
  f_equal.
  f_equal.
  unfold valEnv2valTC.
  unfold thicken.
  dependent induction kp.
  symmetry in x.
  eapply map_eq_nil in x.
  inversion x; subst.
  simpl.
  reflexivity.
  destruct tenv.
  inversion x.
  simpl in x.
  inversion x; subst.
  destruct p.
  simpl in *.
  inversion r; subst.
  rewrite IHkp.
  reflexivity.
  reflexivity.
Defined.  

(*********************************************************************)

(* good.
DEPTYP: works through a product
*)
Lemma eval_vls_aux1 (fenv: funEnv) (env: valEnv) (f: Fun)
      (vs: list Value) 
  (kp1: PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env)
                   (PS (map Val vs)) (PT (map snd (funValTC f))))
  (kp2: vlsTyping vs (map snd (funValTC f)))
  (et2: 
     valTC_Trans (valEnv2valTC (mkVEnv (funValTC f) vs)) =
      tlist2type (map (fun t : VTyp => sVTyp t) (map snd (funValTC f)))
       ) : 

  Eval_vls (map snd (funValTC f)) vs kp2 =
 match et2 with  
 | eq_refl => ValEnvTRN (mkVEnv (funValTC f) vs)
 end.                       
  destruct f.
  simpl in *.
  unfold vlsTyping in kp2.
  dependent induction kp1.
  
  symmetry in x0.
  eapply map_eq_nil in x0.
  inversion x0; subst.
  symmetry in x.
  eapply map_eq_nil in x.
  inversion x; subst.
  clear H0 H.
  simpl in *.
  dependent destruction kp2.
  simpl.
  
  dependent destruction et2.
  reflexivity.

  destruct vs.
  inversion x0.
  destruct tenv.
  inversion x.
  simpl in x0, x.
  inversion x0; subst.
  destruct p.
  inversion x; subst.
  simpl in *.
  clear x0 x.
  generalize kp2 as kp3.
  intro.
  dependent destruction kp3.
  inversion v2; subst.
  unfold VTyping in v2.
  dependent destruction v2.
  
  assert ( 
      Eval_vls (valueVTyp v0 :: map snd tenv) (v0 :: vs)
         (Forall2_consT VTyping v0
           (valueVTyp v0) vs (map snd tenv) eq_refl kp3)       
           =
             (sValue v0, Eval_vls (map snd tenv) (vs) kp3 ) ) as S3.
    unfold Eval_vls.
    simpl.
    destruct v0.
    destruct v0.
    unfold sValue.
    unfold sValueI.
    simpl.
    f_equal.

    rewrite S3.
    unfold mkVEnv in IHkp1.
    
  unfold valTC_Trans in et2.
  unfold VTList_Trans in et2.
  unfold TList_Type in et2.
  simpl in et2.
  unfold VTyp_Trans in et2.

  assert (tlist2type
          (map (fun t : VTyp => sVTyp t)
               (map snd (valEnv2valTC (interleave (map fst tenv) vs)))) =
          tlist2type (map (fun t : VTyp => sVTyp t) (map snd tenv))) as S4.
  eapply deptyp_aux4.
  exact kp3.
  destruct v0.
  destruct v0.
  unfold valueVTyp in et2.
  simpl in et2.
  destruct x.
  unfold sVTyp in et2.
  
  replace et2 with (@prod_eq st st _ _  eq_refl S4).

    rewrite (IHkp1 fenv env tenv vs eq_refl eq_refl eq_refl eq_refl kp3 S4).

    generalize (ValEnvTRN (interleave (map fst tenv) vs)).
    generalize S4.
    erewrite <- (deptyp_aux4 tenv vs kp3).
    intros.
    dependent destruction S0.
    unfold prod_eq.
    simpl.
    reflexivity.    
eapply proof_irrelevance.
Defined.


(* DEPTYP: similar to eval_vls_aux1 *)
Lemma eval_vls_aux2 (fenv: funEnv) (env: valEnv) 
      (tenv0: valTC)              
      (vs: list Value) 
  (kp1: PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env)
                   (PS (map Val vs)) (PT (map snd tenv0)))
  (kp2: vlsTyping vs (map snd tenv0))
  (et2: 
     valTC_Trans (valEnv2valTC (mkVEnv tenv0 vs)) =
      tlist2type (map (fun t : VTyp => sVTyp t) (map snd tenv0))
       ) : 
  Eval_vls (map snd tenv0) vs kp2 =
 match et2 with  
 | eq_refl => ValEnvTRN (mkVEnv tenv0 vs)
 end.                       
  simpl in *.
  unfold vlsTyping in kp2.
  dependent induction kp1.
  
  symmetry in x0.
  eapply map_eq_nil in x0.
  inversion x0; subst.
  symmetry in x.
  eapply map_eq_nil in x.
  inversion x; subst.
  clear H0 H.
  simpl in *.
  dependent destruction kp2.
  simpl.
  
  dependent destruction et2.
  reflexivity.

  destruct vs.
  inversion x0.
  destruct tenv0.
  inversion x.
  simpl in x0, x.
  inversion x0; subst.
  destruct p.
  inversion x; subst.
  simpl in *.
  clear x0 x.
  generalize kp2 as kp3.
  intro.
  dependent destruction kp3.
  inversion v1; subst.
  unfold VTyping in v1.
  dependent destruction v1.
  
  assert ( 
      Eval_vls (valueVTyp v :: map snd tenv0) (v :: vs)
         (Forall2_consT VTyping v
           (valueVTyp v) vs (map snd tenv0) eq_refl kp3)       
           =
             (sValue v, Eval_vls (map snd tenv0) (vs) kp3 ) ) as S3.
    unfold Eval_vls.
    simpl.
    destruct v.
    destruct v.
    unfold sValue.
    unfold sValueI.
    simpl.
    f_equal.

    rewrite S3.
    unfold mkVEnv in IHkp1.
    
  unfold valTC_Trans in et2.
  unfold VTList_Trans in et2.
  unfold TList_Type in et2.
  simpl in et2.
  unfold VTyp_Trans in et2.

  assert (tlist2type
          (map (fun t : VTyp => sVTyp t)
               (map snd (valEnv2valTC (interleave (map fst tenv0) vs)))) =
          tlist2type (map (fun t : VTyp => sVTyp t) (map snd tenv0))) as S4.
  eapply deptyp_aux4.
  exact kp3.
  destruct v.
  destruct v.
  unfold valueVTyp in et2.
  simpl in et2.
  destruct x.
  unfold sVTyp in et2.
  
  replace et2 with (@prod_eq st st _ _  eq_refl S4).

    rewrite (IHkp1 fenv env tenv0 vs eq_refl eq_refl eq_refl eq_refl kp3 S4).

    generalize (ValEnvTRN (interleave (map fst tenv0) vs)).
    generalize S4.
    erewrite <- (deptyp_aux4 tenv0 vs kp3).
    intros.
    dependent destruction S0.
    unfold prod_eq.
    simpl.
    reflexivity.    
eapply proof_irrelevance.
Defined.


(*************************************************************************)


Definition DenExp_ext (t: VTyp) (n1: nat) :
  (sVTyp t * W) * sigT (fun n2 => n2 <= n1) ->
  (sVTyp t * (W * nat)) := fun r => 
  (fst (fst r), (snd (fst r), projT1 (snd r))). 

Definition DenPrms_ext (pt: PTyp) (n1: nat) :
  (PTyp_TRN pt * W) * sigT (fun n2 => n2 <= n1) ->
  (PTyp_TRN pt * (W * nat)) := fun r => 
  (fst (fst r), (snd (fst r), projT1 (snd r))). 


(************************************************************************)
(* superseded *)
Definition PInterpExpA (ftenv: funTC) (tenv: valTC)
                       (fenv: funEnv) (env: valEnv)
                       (m1: FEnvTyping fenv ftenv)
                       (m2: EnvTyping env tenv)  
                       (k1: FEnvWT fenv) 
                        (e: Exp) (t: VTyp)
                      (k: ExpTyping ftenv tenv e t)
                     (s: W) (n: nat) : Type :=
forall (n0: nat) (q: n0 <= n),
  sigT (fun I1: 
            SoundExp fenv env e t s n0 =>   
(**)  
          SOS_Exp1 fenv env e t s n0 I1 =
           DenExp_ext t n0 (ExpTransB fenv k1 n ftenv tenv e t k m1 
                            (ValEnvTRN3 tenv env m2) n0 q s)).
 

Definition PInterpPrmsA (ftenv: funTC) (tenv: valTC)
                       (fenv: funEnv) (env: valEnv)
                       (m1: FEnvTyping fenv ftenv)
                       (m2: EnvTyping env tenv)  
              (k1: FEnvWT fenv) (ps: Prms) (pt: PTyp) 
              (k: PrmsTyping ftenv tenv ps pt)
              (s: W) (n: nat) : Type := 
forall (n0: nat) (q: n0 <= n), 
   sigT (fun I1: SoundPrms fenv env ps pt s n0 =>   
(**)  
           SOS_Prms fenv env ps pt s n0 I1 =
           DenPrms_ext pt n0 (PrmsTransB fenv k1 n ftenv tenv ps pt k m1 
                            (ValEnvTRN3 tenv env m2) n0 q s)).

(***********************************************************************)

Definition ValEnv_agree (tenv: valTC) (env: valEnv) (k: EnvTyping env tenv)
   (senv: valTC_Trans tenv) : Type :=
  forall (x: Id) (t: VTyp) (v: sVTyp t)
      (k1: findE tenv x = Some t)
      (k2: findE env x = Some (cst t v)),
    v = extract_from_valTC_TransB tenv senv x t k1.

Lemma ValEnvTRN_OK (tenv: valTC) (env: valEnv) (k: EnvTyping env tenv) :
  ValEnv_agree tenv env k (ValEnvTRN3 tenv env k).
  unfold ValEnv_agree.
  unfold ValEnvTRN3.  
  unfold EnvTyping in k.
  unfold MatchEnvs in k.
  inversion k; subst.
  clear H.
  eapply ValEnvTRN_ok.
Defined.  


(**********************************************************************)

(* superseded *)
Definition PInterpExp1 (n: nat)
           (ftenv: funTC) (tenv: valTC)
           (e: Exp) (t: VTyp)
           (k: ExpTyping ftenv tenv e t) : Type := 
           forall (fenv: funEnv) (env: valEnv) (k: FEnvWT fenv) 
                  (m1: FEnvTyping fenv ftenv)
                  (m2: EnvTyping env tenv)
                  (senv: valTC_Trans tenv)
                  (kk: ValEnv_agree tenv env m2 senv)
                  (s0: W) (n0: nat)
                  (q: n0 <= n), 
  sigT (fun I1: 
              forall (n': nat) (q1: n' <= n) (s: W),
                SoundExp fenv env e t s n' =>   
(**)  
  sigT (fun I2: forall (n': nat) (q2: n' <= n), W -> 
                    (sVTyp t * W) * sigT (fun n1 => n1 <= n') => 
(**)
          SOS_Exp1 fenv env e t s0 n0 (I1 n0 q s0) =
           DenExp_ext t n0 (I2 n0 q s0))).
 

Definition PInterpPrms1 (n: nat)
           (ftenv: funTC) (tenv: valTC)
           (ps: Prms) (pt: PTyp)
           (k: PrmsTyping ftenv tenv ps pt) : Type := 
           forall (fenv: funEnv) (env: valEnv) (k: FEnvWT fenv) 
                  (m1: FEnvTyping fenv ftenv)
                  (m2: EnvTyping env tenv)
                  (senv: valTC_Trans tenv)
                  (kk: ValEnv_agree tenv env m2 senv)
                  (s0: W) (n0: nat)
                  (q: n0 <= n),  
  sigT (fun I1: 
              forall (n': nat) (q1: n' <= n) (s: W),
                SoundPrms fenv env ps pt s n' =>   
(**)  
  sigT (fun I2: forall (n': nat) (q2: n' <= n), W -> 
                    (PTyp_TRN pt * W) * sigT (fun n1 => n1 <= n') => 
(**)
           SOS_Prms fenv env ps pt s0 n0 (I1 n0 q s0) =
           DenPrms_ext pt n0 (I2 n0 q s0))).


(***********************************************************************)

(* superseded *)
Definition PInterpExp2 (n: nat)
           (ftenv: funTC) (tenv: valTC)
           (e: Exp) (t: VTyp)
           (k: ExpTyping ftenv tenv e t) : Type := 
           forall (fenv: funEnv) (k: FEnvWT fenv) 
                  (m1: FEnvTyping fenv ftenv)              
                  (env: valEnv) (m2: EnvTyping env tenv)
                  (senv: valTC_Trans tenv)                  
                  (kk: ValEnv_agree tenv env m2 senv)
                  (s0: W) (n0: nat)
                  (q: n0 <= n), 
  sigT (fun I1: forall (n': nat) (q1: n' <= n) (s: W),
                SoundExp fenv env e t s n' =>   
(**)  
  sigT (fun I2: forall (n': nat) (q2: n' <= n), W -> 
                    (sVTyp t * W) * sigT (fun n1 => n1 <= n') => 
(**)
          SOS_Exp1 fenv env e t s0 n0 (I1 n0 q s0) =
           DenExp_ext t n0 (I2 n0 q s0))).
 

Definition PInterpPrms2 (n: nat)
           (ftenv: funTC) (tenv: valTC)
           (ps: Prms) (pt: PTyp)
           (k: PrmsTyping ftenv tenv ps pt) : Type := 
           forall (fenv: funEnv) (k: FEnvWT fenv) 
                  (m1: FEnvTyping fenv ftenv)
                  (env: valEnv)
                  (m2: EnvTyping env tenv)
                  (senv: valTC_Trans tenv)
                  (kk: ValEnv_agree tenv env m2 senv)
                  (s0: W) (n0: nat)
                  (q: n0 <= n),  
  sigT (fun I1: 
              forall (n': nat) (q1: n' <= n) (s: W),
                SoundPrms fenv env ps pt s n' =>   
(**)  
  sigT (fun I2: forall (n': nat) (q2: n' <= n), W -> 
                    (PTyp_TRN pt * W) * sigT (fun n1 => n1 <= n') => 
(**)
           SOS_Prms fenv env ps pt s0 n0 (I1 n0 q s0) =
           DenPrms_ext pt n0 (I2 n0 q s0))).

(**********************************************************************)

(** IMPORTANT **)

Definition PInterpExp (fenv: funEnv) (k: FEnvWT fenv) (n: nat)
           (ftenv: funTC) (tenv: valTC)
           (e: Exp) (t: VTyp)
           (k: ExpTyping ftenv tenv e t) : Type := 
 forall  (m1: FEnvTyping fenv ftenv),  
  sigT (fun I1: forall (m1: FEnvTyping fenv ftenv)
            (env: valEnv) (m2: EnvTyping env tenv)
                       (n': nat) (q1: n' <= n) (s: W),
                SoundExp fenv env e t s n' =>   
(**)  
  sigT (fun I2: forall (m1: FEnvTyping fenv ftenv)
                    (senv: valTC_Trans tenv)
                       (n': nat) (q2: n' <= n), W -> 
                (sVTyp t * W) * sigT (fun n1 => n1 <= n') =>
(**)
  forall (s0: W) (n0: nat) (q: n0 <= n)               
         (env: valEnv) (m2: EnvTyping env tenv)
         (senv: valTC_Trans tenv)                  
         (kk: ValEnv_agree tenv env m2 senv),
           SOS_Exp1 fenv env e t s0 n0 (I1 m1 env m2 n0 q s0) =
           DenExp_ext t n0 (I2 m1 senv n0 q s0))).
 

Definition PInterpPrms (fenv: funEnv) (k: FEnvWT fenv) (n: nat)
           (ftenv: funTC) (tenv: valTC)
           (ps: Prms) (pt: PTyp)
           (k: PrmsTyping ftenv tenv ps pt) : Type := 
forall  (m1: FEnvTyping fenv ftenv),  
  sigT (fun I1: forall (m1: FEnvTyping fenv ftenv)
                       (env: valEnv) (m2: EnvTyping env tenv)
                       (n': nat) (q1: n' <= n) (s: W),
                SoundPrms fenv env ps pt s n' =>   
(**)  
  sigT (fun I2: forall (m1: FEnvTyping fenv ftenv)
                               (senv: valTC_Trans tenv) 
                       (n': nat) (q2: n' <= n), W -> 
                (PTyp_TRN pt * W) * sigT (fun n1 => n1 <= n') => 
(**)
  forall (s0: W) (n0: nat) (q: n0 <= n)
         (env: valEnv) (m2: EnvTyping env tenv)
         (senv: valTC_Trans tenv)
         (kk: ValEnv_agree tenv env m2 senv),      
           SOS_Prms fenv env ps pt s0 n0 (I1 m1 env m2 n0 q s0) =
           DenPrms_ext pt n0 (I2 m1 senv n0 q s0))).


Definition PInterp_ExpTyping_mut (fenv: funEnv) (k: FEnvWT fenv) (n: nat) :=
  ExpTyping_mut (PInterpExp fenv k n) (PInterpPrms fenv k n). 

Definition PInterp_PrmsTyping_mut (fenv: funEnv) (k: FEnvWT fenv) (n: nat) :=
  PrmsTyping_mut (PInterpExp fenv k n) (PInterpPrms fenv k n). 


End InterprBase.


