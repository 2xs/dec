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


Import ListNotations.


Module PreInter (IdT: ModTyp) <: ModTyp.

Module ReflectL := Reflect IdT.
Export ReflectL.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Open Scope type_scope.


Lemma Eval_vls (ts : list VTyp) (vs : list Value) :
    Forall2T VTyping vs ts -> 
    tlist2type (map (fun t : VTyp => sVTyp t) ts).
  intros.
  induction X.
  simpl.
  exact tt.
  simpl.
  split.
  inversion r; subst.
  destruct x.
  destruct v.
  exact v.
  exact IHX.
Defined.  


(*******************************************************************)

Program Definition SOS_Exp 
                   (fenv: funEnv) (env: valEnv)
                   (e: Exp) (t: VTyp) (s: W) (n: nat)
                   (k: SoundExp fenv env e t s n) :
                              sVTyp t * (W * nat) := _.

Next Obligation.
  intros.
  unfold SoundExp in k.
  destruct k.
  split.
  - unfold VTyping in *.
    rewrite <- v.
    exact (sValue x).
  - destruct s0.
    exact x0.
Defined.


Program Definition SOS_Exp1 
                   (fenv: funEnv) (env: valEnv)
                   (e: Exp) (t: VTyp) (s: W) (n: nat) 
                   (k: SoundExp fenv env e t s n) :
  sVTyp t * (W * nat) :=
  let (x, vt, s0) := k in
  (match vt in (_ = y0) return (sVTyp y0) with
   | eq_refl => sValue x
   end, projT1 s0).


Definition ExpEvalSOS_TRN (fenv: funEnv)        
           (k1: FEnvWT fenv) 
           (env: valEnv) (e: Exp) (t: VTyp) 
           (k3: ExpTyping (funEnv2funTC fenv) (valEnv2valTC env) e t)
           (s: W) (n: nat) : (sVTyp t * (W * nat)) := 
  SOS_Exp1 fenv env e t s n 
  (ExpSoundness fenv k1 (funEnv2funTC fenv) (valEnv2valTC env) e t k3
                eq_refl env eq_refl s n).



Program Definition SOS_Prms 
                   (fenv: funEnv) (env: valEnv)
                   (ps: Prms) (pt: PTyp) (s: W) (n: nat)
                   (k: SoundPrms fenv env ps pt s n) :
                              PTyp_TRN pt * (W * nat) := _.
Next Obligation.
  intros.
  destruct pt.
  unfold SoundPrms in k.
  destruct k as [es k].
  destruct k as [vs k1 k2].
  unfold isValueList2T in k1.
  rewrite k1 in *.
  clear k1.
  clear es.  
  destruct ps.
  destruct k2 as [k2 k3].
  destruct k3 as [s1 k3].
  unfold PTyp_TRN.
  unfold PTyp_ListTrans.
  
  split.

  eapply matchListsAux02_T with (vs:=vs) in k2.
  unfold vlsTyping in k2.
  eapply Eval_vls.
  exact k2.

  constructor.
  exact s1.
Defined.  
  

Definition PrmsEvalSOS_TRN (fenv: funEnv)        
           (k1: FEnvWT fenv) 
           (env: valEnv) (ps: Prms) (pt: PTyp) 
           (k3: PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) ps pt)
           (s: W) (n: nat) : (PTyp_TRN pt * (W * nat)) := 
  SOS_Prms fenv env ps pt s n 
  (PrmsSoundness fenv k1 (funEnv2funTC fenv) (valEnv2valTC env) ps pt k3
                 eq_refl env eq_refl s n).


(**********************************************************************)

(* experiments *)

Program Definition noDupNil : @noDup Id Fun [] := _.
Next Obligation.
  constructor.
Defined.  

Program Definition FEnvWTNil : FEnvWT [] := _.
Next Obligation.
  unfold FEnvWT.
  intros.
  unfold FunWT.
  inversion H0.
Defined.  

Program Definition ExpT1 (n: nat) :
  ExpTyping [] [] (Val (existT ValueI Nat (Cst Nat n))) Nat := _.
Next Obligation.
  constructor.
  unfold VTyping.
  simpl.
  auto.
Defined.  


Lemma ExpAgree        
           (n: nat) :
   ExpEvalTRN nil FEnvWTNil noDupNil nil (Val (existT ValueI Nat (Cst Nat n))) Nat (ExpT1 n) = 
      fun w => ExpEvalSOS_TRN nil FEnvWTNil nil (Val (existT ValueI Nat (Cst Nat n))) Nat (ExpT1 n) (fst w) (snd w).
Proof.
  eapply functional_extensionality_dep.
  intro w.
  destruct w.
  simpl in *.
  simpl.
  induction n0.
  compute.
  auto.
  compute.
  auto.
Defined.
  

Program Definition ExpT11 (T: Type) (C: CTyp)    
           (n: T) :
  ExpTyping [] [] (Val (existT ValueI (VT T C) (Cst (VT T C) n))) (VT T C) := _.
Next Obligation.
  constructor.
  unfold VTyping.
  simpl.
  auto.
Defined.  


Lemma ExpAgree1
      (T: Type) (C: CTyp) (n: T) :
  ExpEvalTRN nil FEnvWTNil noDupNil nil (Val (existT ValueI (VT T C)
            (Cst (VT T C) n))) (VT T C) (ExpT11 T C n) = 
  fun w => ExpEvalSOS_TRN nil FEnvWTNil nil (Val (existT ValueI (VT T C)
       (Cst (VT T C) n))) (VT T C) (ExpT11 T C n) (fst w) (snd w).
Proof.
  eapply functional_extensionality_dep.
  intro w.
  destruct w.
  simpl in *.
  induction n0.
  compute.
  auto.
  compute.
  auto.
Defined.


Program Definition ExpT12 (T: Type) (C: CTyp)        
           (n: T) (fenv: funEnv) (env: valEnv) :
  ExpTyping (funEnv2funTC fenv) (valEnv2valTC env)
    (Val (existT ValueI (VT T C) (Cst (VT T C) n))) (VT T C) := _.
Next Obligation.
  constructor.
  unfold VTyping.
  simpl.
  auto.
Defined.  


Lemma ExpAgree2 (fenv: funEnv)        
           (k1: FEnvWT fenv) (k2: noDup fenv)
           (env: valEnv)
      (T: Type) (C: CTyp) (n: T) :
  ExpEvalTRN fenv k1 k2 env (Val (existT ValueI (VT T C)
        (Cst (VT T C) n))) (VT T C) (ExpT12 T C n fenv env) = 
  fun w => ExpEvalSOS_TRN fenv k1 env (Val (existT ValueI (VT T C)
    (Cst (VT T C) n))) (VT T C) (ExpT12 T C n fenv env) (fst w) (snd w).
Proof.
  eapply functional_extensionality_dep.
  intro w.
  destruct w.
  simpl in *.
  induction n0.
  induction fenv.
  compute.
  auto.
  compute.
  auto.
  induction fenv.
  compute.
  auto.
  compute.
  auto.
Defined.

  
Lemma ExpAgree2n (fenv: funEnv)        
           (k1: FEnvWT fenv) (k2: noDup fenv)
           (env: valEnv)
      (T: Type) (C: CTyp) (n: T) :
  ExpEvalTRN fenv k1 k2 env (Val (existT ValueI (VT T C)
      (Cst (VT T C) n))) (VT T C) (ExpT12 T C n fenv env) = ret n.
  eapply functional_extensionality_dep.
  intro w.
  destruct w.
  simpl in *.
  induction n0.
  induction fenv.
  compute.
  auto.
  compute.
  auto.
  induction fenv.
  compute.
  auto.
  compute.
  auto.
Defined.

Program Definition ExpT13 (T: Type) (C: CTyp)    
        (x: Id) (fenv: funEnv) (env: valEnv) 
        (H: findE (valEnv2valTC env) x = Some (VT T C)) :  
  ExpTyping (funEnv2funTC fenv) (valEnv2valTC env) (Var x)
            (VT T C) := _.
Next Obligation.
  constructor.
  exact H.
Defined.  



Lemma xxxAA (env: valEnv) (i0: Id) : (if IdT.IdEqDec i0 i0
       then Some (VT nat (CInt I32 Unsigned))
       else findE (valEnv2valTC env) i0) = Some (VT nat (CInt I32 Unsigned)).
  destruct (IdT.IdEqDec i0 i0).
  reflexivity.
  intuition n.
Defined.


Lemma ExpSoundnessA_Val : forall (n: nat)
    (ftenv : funTC) (tenv : valTC) (v : Value) 
    (t : VTyp) (v0 : VTyping v t),
   forall (fenv: funEnv) (env: valEnv)
           (k1: FEnvWT fenv),                      
   FEnvTyping fenv ftenv ->
   EnvTyping env tenv ->    
   forall (s0 : W) (n0 : nat), n0 <= n -> SoundExp fenv env (Val v) t s0 n0.
    unfold SoundExp.
    intros.
    constructor 1 with (x:=v).
    assumption.
    constructor 1 with (x:=(s0,n0)).
    simpl.
    constructor.
Defined.


Lemma ExpSoundnessA1_Val : forall (n: nat)
    (ftenv : funTC) (tenv : valTC) (v : Value) 
    (t : VTyp) (v0 : VTyping v t),
   forall (fenv: funEnv) (env: valEnv)
           (k1: FEnvWT fenv),                      
   FEnvTyping fenv ftenv ->
   EnvTyping env tenv ->    
   forall (s : W), SoundExp fenv env (Val v) t s n.
    unfold SoundExp.
    intros.
    constructor 1 with (x:=v).
    assumption.
    constructor 1 with (x:=(s,n)).
    simpl.
    constructor.
Defined.


Lemma ExpDenotA_Val : forall (n: nat)
    (ftenv : funTC) (tenv : valTC) (v : Value) 
    (t : VTyp) (v0 : VTyping v t),
   forall (fenv: funEnv) (env: valEnv) (k1: FEnvWT fenv),                      
   FEnvTyping fenv ftenv ->
   EnvTyping env tenv ->    
  tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) ->
    valTC_Trans (valEnv2valTC env) -> MM WW (sVTyp t).  
     intros.
     inversion v0; subst.
     exact (ret (sValue v)).
Defined.    



(**********************************************************************)


Lemma ExpSoundnessA_Var : forall (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id) 
    (t : VTyp) (i : IdTyping tenv x t),
   forall (fenv: funEnv) (env: valEnv)
           (k1: FEnvWT fenv),                      
   FEnvTyping fenv ftenv ->
   EnvTyping env tenv ->    
   forall (s0 : W) (n0 : nat), n0 <= n -> SoundExp fenv env (Var x) t s0 n0.
    unfold SoundExp.
    intros.
    inversion i; subst.
    inversion H0; subst.
    unfold EnvTyping in H0.    
    eapply ExtRelVal2 with (f:=valueVTyp) (venv:=env) in H3.
    destruct H3.
    constructor 1 with (x:=x0).
    unfold VTyping.
    exact e0.
    constructor 1 with (x:=(s0,n0)).
    simpl.
    eapply StepIsEClos.
    constructor.
    assumption.
    assumption.
Defined.

Lemma ExpSoundnessB_Var : forall (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id) 
    (t : VTyp) (i : IdTyping tenv x t),
   forall (fenv: funEnv) (env: valEnv)
           (k1: FEnvWT fenv),                      
   FEnvTyping fenv ftenv ->
   EnvTyping env tenv ->    
   forall (s0 : W) (n0 : nat), n0 <= n -> SoundExp fenv env (Var x) t s0 n0.
  unfold SoundExp.
  intros.
  unfold IdTyping in i.
  unfold EnvrAssign in i.
  unfold EnvTyping in H0.
  unfold MatchEnvs in H0.
  rewrite H0 in i.
  clear H0.
  eapply ExtRelVal2 with (f:=valueVTyp) (venv:=env) in i.
  destruct i.
  constructor 1 with (x:=x0).
  unfold VTyping.
  exact e0.
  constructor 1 with (x:=(s0,n0)).
  simpl.
  eapply StepIsEClos.
  constructor.
  assumption.
  constructor.
Defined.
    
Lemma ExpDenotA_Var : forall (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id) 
    (t : VTyp) (i : IdTyping tenv x t),
   forall (fenv: funEnv) (env: valEnv) (k1: FEnvWT fenv),                      
   FEnvTyping fenv ftenv ->
   EnvTyping env tenv ->    
  tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) ->
    valTC_Trans (valEnv2valTC env) -> MM WW (sVTyp t).  
     intros.
     inversion i; subst.
     unfold MM.
     intro.
     split.
     inversion H0; subst.
     eapply (extract_from_valTC_TransB _ X0 x).
     exact H2.
     exact X1.
Defined.

Lemma ExpDenotB_Var : forall (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id) 
    (t : VTyp) (i : IdTyping tenv x t),
   forall (fenv: funEnv) (env: valEnv) (k1: FEnvWT fenv),                      
   FEnvTyping fenv ftenv ->
   EnvTyping env tenv ->    
  tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) ->
    valTC_Trans (valEnv2valTC env) -> MM WW (sVTyp t).  
  intros.
  unfold IdTyping in i.
  unfold EnvrAssign in i.
  unfold MM.
  intro.
  split.
  unfold EnvTyping in H0.
  unfold MatchEnvs in H0.
  rewrite H0 in i.
  clear H0.
  eapply (extract_from_valTC_TransB _ X0 x).
  exact i.
  exact X1.
Defined.


Lemma ExpSoundnessDenotC_Var : forall (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id) 
    (t : VTyp) (i : IdTyping tenv x t),
   forall (fenv: funEnv) (env: valEnv)
           (k1: FEnvWT fenv),                      
   FEnvTyping fenv ftenv ->
   EnvTyping env tenv ->    
   forall (s0 : W) (n0 : nat), n0 <= n ->
                   (SoundExp fenv env (Var x) t s0 n0 * sVTyp t).
  unfold SoundExp.
  intros.
  unfold IdTyping in i.
  unfold EnvrAssign in i.
  rename H into X.
  rename H0 into X0.
  rename H1 into H.
  unfold EnvTyping in X0.
  unfold MatchEnvs in X0.
  rewrite X0 in i.
  clear X0.
  eapply ExtRelVal2 with (f:=valueVTyp) (venv:=env) in i.
  destruct i.
  split.
  constructor 1 with (x:=x0).
  unfold VTyping.
  exact e0.
  constructor 1 with (x:=(s0,n0)).
  simpl.
  eapply StepIsEClos.
  constructor.
  assumption.
  unfold valueVTyp in e0.
  destruct x0.
  rewrite <- e0.
  simpl.
  destruct v.
  exact v.
  constructor.
Defined.


Lemma ExpSoundnessDenotE_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id)
    (v : Value) 
    (t : VTyp) (i : IdTyping tenv x t) (mB: valueVTyp v = t)
    (fenv: funEnv) (env: valEnv) (mA: findE env x = Some v)
    (k1: FEnvWT fenv)                       
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)    
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
                   (SoundExp fenv env (Var x) t s0 n0 * sVTyp t).
  unfold SoundExp.
  intros.
  unfold IdTyping in i.
  unfold EnvrAssign in i.
  unfold EnvTyping in m2.
  unfold MatchEnvs in m2.
  rewrite m2 in i.
  clear m2.
(*  eapply ExtRelVal2 with (f:=valueVTyp) (venv:=env) in e. *)
  split.
  constructor 1 with (x:=v).
  unfold VTyping.
  exact mB.
  constructor 1 with (x:=(s0,n0)).
  simpl.
  eapply StepIsEClos.
  constructor.
  assumption.
  unfold valueVTyp in mB.
  destruct v.
  rewrite <- mB.
  simpl.
  destruct v.
  exact v.
Defined.


Lemma ExpSoundnessDenotF_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id)
    (v : Value) 
    (t : VTyp) (i : IdTyping tenv x t) (mB: valueVTyp v = t)
    (fenv: funEnv) (env: valEnv) (mA: findE env x = Some v)
    (k1: FEnvWT fenv)                       
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)    
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
     sigT (fun I: SoundExp fenv env (Var x) t s0 n0 * sVTyp t => 
             SOS_Exp1 fenv env (Var x) t s0 n0 (fst I) = (snd I, (s0, n0))).
Proof.
  intros.
  econstructor 1 with (x:=ExpSoundnessDenotE_Var n ftenv tenv x v t i mB 
                                            fenv env mA k1 m1 m2 s0 n0 m3).
  unfold SOS_Exp1.
  simpl.
  unfold valueVTyp in mB.
  destruct v.
  destruct v.
  compute.
  destruct mB.
  reflexivity.
Defined.  


Lemma ExpSoundnessDenotG_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id)
    (v : Value) 
    (t : VTyp) (mB: valueVTyp v = t)
    (fenv: funEnv) (env: valEnv) (mA: findE env x = Some v)
    (k1: FEnvWT fenv)                       
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)    
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
                   (SoundExp fenv env (Var x) t s0 n0 * sVTyp t).
(*
  sigT (fun I: SoundExp fenv env (Var x) t s0 n0 * sVTyp t => 
             SOS_Exp1 fenv env (Var x) t s0 n0 (fst I) = (snd I, (s0, n0))).
*)
Proof.
  unfold SoundExp.
  intros.
  intros.  
  assert (IdTyping tenv x t) as i.
  eapply (ExtRelTyp tenv x v t mB env m2 mA).    
  unfold EnvTyping in m2.
  unfold MatchEnvs in m2.
  rewrite m2 in i.
  clear m2.
  split.
  constructor 1 with (x:=v).
  unfold VTyping.
  exact mB.
  constructor 1 with (x:=(s0,n0)).
  simpl.
  eapply StepIsEClos.
  constructor.
  assumption.
  unfold valueVTyp in mB.
  destruct v.
  rewrite <- mB.
  simpl.
  destruct v.
  exact v.
Defined.

Lemma ExpSoundnessDenotG1_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id)
    (v : Value) 
    (t : VTyp) (mB: valueVTyp v = t)
    (fenv: funEnv) (env: valEnv) (mA: findE env x = Some v)
    (k1: FEnvWT fenv)                       
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)    
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
                   (SoundExp fenv env (Var x) t s0 n0 * sVTyp t).
Proof.
  eapply (ExpSoundnessDenotE_Var n ftenv tenv x v t
                                 (ExtRelTyp tenv x v t mB env m2 mA)
                                 mB fenv env mA k1 m1 m2 s0 n0 m3).
Defined.
  

Lemma ExpSoundnessDenotH_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id) (t: VTyp)
    (i : IdTyping tenv x t) (*mB: valueVTyp v = t*)
    (fenv: funEnv) (env: valEnv) (*mA: findE env x = Some v*)
    (k1: FEnvWT fenv)                       
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)    
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
     sigT (fun I: SoundExp fenv env (Var x) t s0 n0 * sVTyp t => 
             SOS_Exp1 fenv env (Var x) t s0 n0 (fst I) = (snd I, (s0, n0))).
Proof.
  intros.
  unfold EnvTyping in m2.
  econstructor 1 with (x:=ExpSoundnessDenotG1_Var n ftenv tenv x
       (*v*)(ExtRelVal2A_1 valueVTyp tenv env x t m2 i) t
       (*mB*)(ExtRelVal2A_4 valueVTyp tenv env x t m2 i)     
        fenv env                                          
       (*mA*)(ExtRelVal2A_2 valueVTyp tenv env x t m2 i) 
        k1 m1 m2 s0 n0 m3).
  unfold ExpSoundnessDenotG1_Var.
  unfold SOS_Exp1.
  simpl.
  remember (ExtRelVal2A valueVTyp tenv env x t m2 i) as K.
  destruct K as [v mA mB].
  unfold ExtRelVal2A_1.
  unfold ExtRelVal2A_4.
  unfold ExtRelVal2A_2.
  rewrite <- HeqK.
  
  unfold valueVTyp.
  destruct v.
  destruct v.
  compute.
  destruct mB.
  reflexivity.
Defined.  


Definition FunEnvTRN2 (fenv : funEnv) (k1: FEnvWT fenv) (k2: noDup fenv)
  (n: nat) : tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) :=
  FunEnvTRN fenv k1 k2 n.  

Lemma ExpDenotI_Var' 
  (ftenv : funTC)
  (tenv : valTC)
  (x : Id)
  (t : VTyp)
  (i :  IdTyping tenv x t)
  (v: Value)
  (mB : valueVTyp v = t) :
  tlist2type (map snd (FunTC_ListTrans ftenv)) ->
  valTC_Trans tenv -> MM WW (sVTyp t).
  unfold valueVTyp in mB.
  destruct v.
(**)
  destruct x0.
  destruct v.
  simpl in *.
  inversion mB; subst.
  clear H.
  intros.
  unfold MM.
  intro.
  simpl.
  exact (v,X1).
Defined.  
(**)

Lemma ExpDenotI_Var'' 
  (ftenv : funTC)
  (tenv : valTC)
  (x : Id)
  (t : VTyp)
  (i :  IdTyping tenv x t)
  (v: Value)
  (mB : valueVTyp v = t) :
  tlist2type (map snd (FunTC_ListTrans ftenv)) ->
  valTC_Trans tenv -> MM WW (sVTyp t).
  unfold valueVTyp in mB.
  destruct v.

  rewrite <- mB.
  simpl.
  destruct v.
  unfold MM.
  intros.
  exact (v, X1).
Defined.


Lemma ExpDenotI_VarS 
  (tenv : valTC)
  (x : Id)
  (t : VTyp)
  (i :  IdTyping tenv x t)
  (v: Value)
  (mB : valueVTyp v = t) : MM WW (sVTyp t).
  unfold valueVTyp in mB.
  destruct v.
(**)
  destruct x0.
  destruct v.
  simpl in *.
  inversion mB; subst.
  clear H.
  intros.
  unfold MM.
  intro.
  simpl.
  exact (v,X).
Defined.  


Program Fixpoint ValEnvTRN2 (tenv: valTC) (env: valEnv)
        (k: EnvTyping env tenv) :
  valTC_Trans tenv := _.
Next Obligation.
  intros.
  inversion k; subst.
  eapply ValEnvTRN.
Defined.  

Lemma valenvtrn_eq (env: valEnv) :
    ((ValEnvTRN2 (map (thicken StaticSemL.Id valueVTyp) env) env
                      eq_refl) = ValEnvTRN env).
  induction env.
  simpl.
  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  reflexivity.
  simpl.
  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  reflexivity.
Defined.


(***** interesting for the proof *********************)
Lemma compare_den_var 
  (tenv : valTC)
  (x : Id)
  (t : VTyp)
  (i :  IdTyping tenv x t)
  (v: Value)
  (env: valEnv)
  (k: EnvTyping env tenv)
  (mB : valueVTyp v = t)
  (mA: findE env x = Some v)
  (senv: valTC_Trans tenv)
  (k1: senv = ValEnvTRN2 tenv env k)
   :
  (ExpDenI_Var tenv x t i) senv = ExpDenotI_VarS tenv x t i v mB.
  destruct t.
  destruct v.
  destruct v.
  destruct x0.
  simpl in v.
  simpl in mB.
  inversion mB; subst.
  inversion k; subst.
  simpl in *.
  dependent destruction mB.
  simpl.
  unfold ExpDenI_Var.
  eapply functional_extensionality_dep.
  intro.
  unfold IdTyping in i.
  unfold EnvrAssign in i.
  dependent induction env.
  inversion mA.
  destruct a.
  simpl in mA.
  simpl in i.
  revert mA.
  revert i.
  simpl.
  destruct (IdT.IdEqDec x i0).
  intros.
  inversion i; subst.
  inversion mA; subst.
  simpl in i.
  simpl in H0.
  clear H0.
  clear mA.
  dependent destruction i.
  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  f_equal.
  unfold ValEnvTRN2_obligation_1.
  unfold EnvTyping in k.
  unfold MatchEnvs in k.
  dependent destruction k.
  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  simpl.
  reflexivity.

(**)  

  unfold EnvTyping in k.
  unfold MatchEnvs in k.
  dependent destruction k.
  intros.
  unfold ValEnvTRN2_obligation_1.
  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  simpl.
  specialize (IHenv eq_refl i v mA x1).
  rewrite valenvtrn_eq in IHenv.
  exact IHenv.
Defined.  


(* senv not really used *)
Lemma ExpSoundnessDenotI_Var' (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id)
    (v : Value) 
    (t : VTyp) (i : IdTyping tenv x t) (mB: valueVTyp v = t)
    (fenv: funEnv) (env: valEnv) (mA: findE env x = Some v)
    (k1: FEnvWT fenv)                       
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)    
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
  (SoundExp fenv env (Var x) t s0 n0 *
   (tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) -> 
    (* senv: *) valTC_Trans (valEnv2valTC env) ->
    MM WW (sVTyp t))).
  unfold SoundExp.
  intros.
  unfold IdTyping in i.
  unfold EnvrAssign in i.
  unfold EnvTyping in m2.
  unfold MatchEnvs in m2.
  rewrite m2 in i.
  clear m2.
(*  eapply ExtRelVal2 with (f:=valueVTyp) (venv:=env) in e. *)
  split.
  constructor 1 with (x:=v).
  unfold VTyping.
  exact mB.
  constructor 1 with (x:=(s0,n0)).
  simpl.
  eapply StepIsEClos.
  constructor.
  assumption.
  intros.
  eapply ExpDenotI_VarS.
  exact i.
  exact mB.
Defined.

    
Lemma ExpSoundnessDenotI_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id)
    (v : Value) 
    (t : VTyp) (i : IdTyping tenv x t) (mB: valueVTyp v = t)
    (fenv: funEnv) (env: valEnv) (mA: findE env x = Some v)
    (k1: FEnvWT fenv)                       
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)    
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
  (SoundExp fenv env (Var x) t s0 n0 *
   (tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) -> 
                valTC_Trans (valEnv2valTC env) -> MM WW (sVTyp t))).
  unfold SoundExp.
  intros.
  unfold IdTyping in i.
  unfold EnvrAssign in i.
  unfold EnvTyping in m2.
  unfold MatchEnvs in m2.
  rewrite m2 in i.
  clear m2.
(*  eapply ExtRelVal2 with (f:=valueVTyp) (venv:=env) in e. *)
  split.
  constructor 1 with (x:=v).
  unfold VTyping.
  exact mB.
  constructor 1 with (x:=(s0,n0)).
  simpl.
  eapply StepIsEClos.
  constructor.
  assumption.
  eapply ExpDenotI_Var.
  exact i.
Defined.


Lemma ExpSoundnessDenotI1_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id)
    (v : Value) 
    (t : VTyp) (mB: valueVTyp v = t)
    (fenv: funEnv) (env: valEnv) (mA: findE env x = Some v)
    (k1: FEnvWT fenv)                       
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)    
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
  (SoundExp fenv env (Var x) t s0 n0 *
   (tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) -> 
                valTC_Trans (valEnv2valTC env) -> MM WW (sVTyp t))).
Proof.
  eapply (ExpSoundnessDenotI_Var n ftenv tenv x v t
                                 (ExtRelTyp tenv x v t mB env m2 mA)
                                 mB fenv env mA k1 m1 m2 s0 n0 m3).
Defined.

Lemma ExpSoundnessDenotI1_Var' (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id)
    (v : Value) 
    (t : VTyp) (mB: valueVTyp v = t)
    (fenv: funEnv) (env: valEnv) (mA: findE env x = Some v)
    (k1: FEnvWT fenv)                       
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)    
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
  (SoundExp fenv env (Var x) t s0 n0 *
   (tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) -> 
                valTC_Trans (valEnv2valTC env) -> MM WW (sVTyp t))).
Proof.
  eapply (ExpSoundnessDenotI_Var' n ftenv tenv x v t
                                 (ExtRelTyp tenv x v t mB env m2 mA)
                                 mB fenv env mA k1 m1 m2 s0 n0 m3).
Defined.


Lemma ExpSoundnessDenotJ_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id) (t: VTyp)
    (i : IdTyping tenv x t) (*mB: valueVTyp v = t*)
    (fenv: funEnv) (env: valEnv) (*mA: findE env x = Some v*)
    (k1: FEnvWT fenv)
    (k2: noDup fenv)
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)    
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
  sigT (fun I: SoundExp fenv env (Var x) t s0 n0 *
      (tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) ->
         valTC_Trans (valEnv2valTC env) -> MM WW (sVTyp t)) => 
          SOS_Exp1 fenv env (Var x) t s0 n0 (fst I) =
          (snd I) (FunEnvTRN2 fenv k1 k2 n) (ValEnvTRN env) (s0, n0)).
Proof.
  intros.
  unfold EnvTyping in m2.
  econstructor 1 with (x:=ExpSoundnessDenotI1_Var' n ftenv tenv x
       (*v*)(ExtRelVal2A_1 valueVTyp tenv env x t m2 i) t
       (*mB*)(ExtRelVal2A_4 valueVTyp tenv env x t m2 i)     
        fenv env                                          
       (*mA*)(ExtRelVal2A_2 valueVTyp tenv env x t m2 i) 
        k1 m1 m2 s0 n0 m3).
  unfold ExpSoundnessDenotG1_Var.
(*  destruct i as [tenv x t i]. *)
  unfold SOS_Exp1.
  simpl.
  remember (ExtRelVal2A valueVTyp tenv env x t m2 i) as K.
  destruct K as [v mA mB].
  unfold ExtRelVal2A_1.
  unfold ExtRelVal2A_4.
  unfold ExtRelVal2A_2.
  rewrite <- HeqK.
  
  unfold valueVTyp.
  destruct v.
  destruct v.

  unfold MatchEnvs in m2.
  unfold FEnvTyping in m1.
  unfold MatchEnvs in m1.
  inversion m1; subst.
  clear H.
  simpl in mA.
  destruct x0.
  unfold IdTyping in i.
  unfold EnvrAssign in i.
  simpl in v.
  compute.
  reflexivity.
Defined.  


Lemma ExpSoundnessDenotI2_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id)
    (v : Value) 
    (t : VTyp) (i : IdTyping tenv x t) (mB: valueVTyp v = t)
    (fenv: funEnv) (env: valEnv) (mA: findE env x = Some v)
    (k1: FEnvWT fenv)                       
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)    
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
  (SoundExp fenv env (Var x) t s0 n0 *
   (valTC_Trans (valEnv2valTC env) -> nat -> W -> (sVTyp t * WW))).
  unfold SoundExp.
  intros.
  unfold IdTyping in i.
  unfold EnvrAssign in i.
  unfold EnvTyping in m2.
  unfold MatchEnvs in m2.
  rewrite m2 in i.
  clear m2.
(*  eapply ExtRelVal2 with (f:=valueVTyp) (venv:=env) in e. *)
  split.
  constructor 1 with (x:=v).
  unfold VTyping.
  exact mB.
  constructor 1 with (x:=(s0,n0)).
  simpl.
  eapply StepIsEClos.
  constructor.
  assumption.
  intros.
  eapply ExpDenotI_VarS.
  exact i.
  exact mB.
  exact (s0,n0).
Defined.

Lemma ExpSoundnessDenotI2_VarA (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id)
    (v : Value) 
    (t : VTyp) (mB: valueVTyp v = t)
    (fenv: funEnv) (env: valEnv) (mA: findE env x = Some v)
    (k1: FEnvWT fenv)                       
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)    
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
  (SoundExp fenv env (Var x) t s0 n0 *
   (valTC_Trans (valEnv2valTC env) -> nat -> W -> (sVTyp t * WW))).
Proof.
  eapply (ExpSoundnessDenotI2_Var n ftenv tenv x v t
                                 (ExtRelTyp tenv x v t mB env m2 mA)
                                 mB fenv env mA k1 m1 m2 s0 n0 m3).
Defined.


Lemma ExpSoundnessDenotJ2_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id) (t: VTyp)
    (i : IdTyping tenv x t) (*mB: valueVTyp v = t*)
    (fenv: funEnv) (env: valEnv) (*mA: findE env x = Some v*)
    (k1: FEnvWT fenv)
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)    
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
  sigT (fun I: SoundExp fenv env (Var x) t s0 n0 *
      (valTC_Trans (valEnv2valTC env) -> nat -> W -> (sVTyp t * WW)) => 
          SOS_Exp1 fenv env (Var x) t s0 n0 (fst I) =
          (snd I) (ValEnvTRN env) n0 s0).
Proof.
  intros.
(*  destruct i as [tenv x t i]. *)
  unfold EnvTyping in m2.
  econstructor 1 with (x:=ExpSoundnessDenotI2_VarA n ftenv tenv x
       (*v*)(ExtRelVal2A_1 valueVTyp tenv env x t m2 i) t
       (*mB*)(ExtRelVal2A_4 valueVTyp tenv env x t m2 i)     
        fenv env                                          
       (*mA*)(ExtRelVal2A_2 valueVTyp tenv env x t m2 i) 
        k1 m1 m2 s0 n0 m3).
(*  destruct i as [tenv x t i]. *)
  unfold SOS_Exp1.
  simpl.
  remember (ExtRelVal2A valueVTyp tenv env x t m2 i) as K.
  destruct K as [v mA mB].
  unfold ExtRelVal2A_1.
  unfold ExtRelVal2A_4.
  unfold ExtRelVal2A_2.
  rewrite <- HeqK.
  
  unfold valueVTyp.
  destruct v.
  destruct v.

  unfold MatchEnvs in m2.
  unfold FEnvTyping in m1.
  unfold MatchEnvs in m1.
  inversion m1; subst.
  clear H.
  simpl in mA.
  destruct x0.
  unfold IdTyping in i.
  unfold EnvrAssign in i.
  simpl in v.
  compute.
  reflexivity.
Defined.  

Definition ExpSoundnessJ2_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id) 
    (t : VTyp) (i : IdTyping tenv x t) 
    (fenv: funEnv) (env: valEnv)
    (k1: FEnvWT fenv)                      
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)   
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
  SoundExp fenv env (Var x) t s0 n0 := fst (projT1
  (ExpSoundnessDenotJ2_Var n ftenv tenv x t i fenv env k1 m1 m2 s0 n0 m3)).

Definition ExpDenotJ2_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id) 
    (t : VTyp) (i : IdTyping tenv x t) 
    (fenv: funEnv) (env: valEnv)
    (k1: FEnvWT fenv)                      
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)   
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
  valTC_Trans (valEnv2valTC env) -> nat -> W -> (sVTyp t * WW) :=
  snd (projT1 
  (ExpSoundnessDenotJ2_Var n ftenv tenv x t i fenv env k1 m1 m2 s0 n0 m3)).


(***************************************************************
******************************************************************)


Definition ExpSoundnessH_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id) 
    (t : VTyp) (i : IdTyping tenv x t) 
    (fenv: funEnv) (env: valEnv)
    (k1: FEnvWT fenv)                      
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)   
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
  SoundExp fenv env (Var x) t s0 n0 := fst (projT1
  (ExpSoundnessDenotH_Var n ftenv tenv x t i fenv env k1 m1 m2 s0 n0 m3)).

Definition ExpDenotH_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id) 
    (t : VTyp) (i : IdTyping tenv x t) 
    (fenv: funEnv) (env: valEnv)
    (k1: FEnvWT fenv)                      
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)   
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
  tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) ->
  valTC_Trans (valEnv2valTC env) -> MM WW (sVTyp t) :=
  fun stf sf s => (snd (projT1 
  (ExpSoundnessDenotH_Var n ftenv tenv x t i fenv env k1 m1 m2 s0 n0 m3)), s).

Definition ExpSoundnessJ_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id) 
    (t : VTyp) (i : IdTyping tenv x t) 
    (fenv: funEnv) (env: valEnv)
    (k1: FEnvWT fenv)                      
    (k2: noDup fenv)
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)   
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
  SoundExp fenv env (Var x) t s0 n0 := fst (projT1
  (ExpSoundnessDenotJ_Var n ftenv tenv x t i fenv env k1 k2 m1 m2 s0 n0 m3)).

Definition ExpDenotJ_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id) 
    (t : VTyp) (i : IdTyping tenv x t) 
    (fenv: funEnv) (env: valEnv)
    (k1: FEnvWT fenv)                      
    (k2: noDup fenv)
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)   
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
  tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) ->
  valTC_Trans (valEnv2valTC env) -> MM WW (sVTyp t) :=
  snd (projT1 
  (ExpSoundnessDenotJ_Var n ftenv tenv x t i fenv env k1 k2 m1 m2 s0 n0 m3)).



Lemma PushOutForAll1 (ftenv : funTC) (tenv : valTC) 
  (e : Exp)
  (t : VTyp)
  (m : ExpTyping ftenv tenv e t)
  (fenv : funEnv)
  (env : valEnv)
  (k1: FEnvWT fenv)                      
  (k2: noDup fenv)
  (m1: FEnvTyping fenv ftenv)
  (m2: EnvTyping env tenv)   
  (n: nat) :
  {I1 : forall (s : W) (n0 : nat), n0 <= n -> SoundExp fenv env e t s n0
      &
      {I2
      : tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) ->
        valTC_Trans (valEnv2valTC env) -> MM WW (sVTyp t) &
      {FE : nat -> tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv)))
      &
      forall (s : W) (n0 : nat) (q : n0 <= n),
      SOS_Exp1 fenv env e t s n0 (I1 s n0 q) =
      I2 (FE n0) (ValEnvTRN env) (s, n0)}}} ->
 forall (s : W) (n0 : nat), n0 <= n ->  
  {I3 : SoundExp fenv env e t s n0
      &
      {I4
      : tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) ->
        valTC_Trans (valEnv2valTC env) -> MM WW (sVTyp t) &
      {FE : nat -> tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv)))
      &
      SOS_Exp1 fenv env e t s n0 I3 =
      I4 (FE n0) (ValEnvTRN env) (s, n0)}}}.
  intros.
  destruct X as [k4 X].
  destruct X as [k5 X].
  destruct X as [k6 X].
  econstructor 1 with (x:=k4 s n0 H).
  econstructor 1 with (x:=k5).
  econstructor 1 with (x:=k6).
  specialize (X s n0 H).
  eapply X.
Defined.  

Lemma PushOutForAll1aux (ftenv : funTC) (tenv : valTC) 
  (e : Exp)
  (t : VTyp)
  (m : ExpTyping ftenv tenv e t)
  (fenv : funEnv)
  (env : valEnv)
  (k1: FEnvWT fenv)                      
  (k2: noDup fenv)
  (m1: FEnvTyping fenv ftenv)
  (m2: EnvTyping env tenv)   
  (n: nat) :
( {I1 : forall (s0 : W) (n1 : nat), n1 <= n -> SoundExp fenv env e t s0 n1
      &
      {I2
      : tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) ->
        valTC_Trans (valEnv2valTC env) -> MM WW (sVTyp t) &
      {FE : nat -> tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv)))
      &
      forall (s : W) (n1 : nat) (q : n1 <= n),
      SOS_Exp1 fenv env e t s n1 (I1 s n1 q) =
      I2 (FE n1) (ValEnvTRN env) (s, n1)}}}) ->

  {I1 : forall (s : W) (n0 : nat), n0 <= n -> SoundExp fenv env e t s n0
      &
      {I2
      : tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) ->
        valTC_Trans (valEnv2valTC env) -> MM WW (sVTyp t) &
      {FE : nat -> tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv)))
      &
      forall (s: W) (n0 : nat) (q : n0 <= n),
      SOS_Exp1 fenv env e t s n0 (I1 s n0 q) =
      I2 (FE n0) (ValEnvTRN env) (s, n0)}}}.
  intros.  
  destruct X as [k4 X].
  destruct X as [k5 X].
  destruct X as [k6 X].
  econstructor 1 with (x:=k4).
  econstructor 1 with (x:=k5).
  econstructor 1 with (x:=k6).
  intros.
  eapply X.
Defined.  


(************************************************************************)

Program Definition preSucc_Y
    (fenv: funEnv)      
    (ET : forall (tenv: valTC) (e: Exp) (t: VTyp) 
          (k: ExpTyping (funEnv2funTC fenv) tenv e t)
  (sfenv: nat -> tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv)))),      (valTC_Trans tenv -> MM WW (sVTyp t)))
         
    (k: FEnvWT fenv) (x: Id) (f: Fun) :
  findE fenv x = Some f -> 
  forall (sfenv: nat -> tlist2type
                   (map snd (FunTC_ListTrans (funEnv2funTC fenv)))), 
  FunTyp_TRN f := _.
Next Obligation.
  intros.
  set (tenv := funValTC f).
  set (e := funSExp f).
  set (t := funVTyp f).
  set (ftenv := funEnv2funTC fenv).
  
  assert (ExpTyping ftenv tenv e t) as k1.
  unfold FEnvWT in k.
  specialize (k ftenv eq_refl x f H).
  unfold FunWT in k.
  destruct f.
  subst e.
  subst t.
  subst tenv.
  simpl in *.
  exact k.

  unfold FunTyp_TRN.
  unfold FTyp_TRN2.
  unfold FType_mk2.

(* apply ET (the translation) to e (the function body) in shallow
   environment sfenv *)  
  specialize (ET tenv e t k1 sfenv). 
  unfold valTC_Trans in ET.
  unfold VTList_Trans in ET.
  destruct f.
  subst tenv e t.
  simpl in *.
  intro.
  specialize (ET X).    
  exact ET.
Defined.


Program Definition ZeroTRN4 (ftenv: funTC) (fenv: funEnv)
        (m: FEnvTyping fenv ftenv) :
  tlist2type (map snd (FunTC_ListTrans ftenv)) := _.
Next Obligation.
  intros.
  inversion m; subst.
  rewrite <- FunEnv_Trans_lemma.
  eapply ZeroTRN1. 
Defined.


Program Definition preSucc_Z
        (ftenv: funTC) (fenv: funEnv)
        (m: FEnvTyping fenv ftenv)
    (ET : forall (tenv: valTC) (e: Exp) (t: VTyp) 
          (k: ExpTyping ftenv tenv e t)
          (sfenv: nat -> tlist2type (map snd (FunTC_ListTrans ftenv))),
        (valTC_Trans tenv -> MM WW (sVTyp t)))
         
    (k: FEnvWT fenv) (x: Id) (f: Fun) :
  findE fenv x = Some f -> 
  forall (sfenv: nat -> tlist2type
                   (map snd (FunTC_ListTrans (funEnv2funTC fenv)))), 
  FunTyp_TRN f := _.
Next Obligation.
  intros.
  inversion m; subst.
  eapply preSucc_Y.
  eassumption.
  assumption.
  eassumption.
  assumption.
Defined.  
  
End PreInter.

