(*  DEC 2.0 language specification.
   Paolo Torrini  
   Universite' Lille-1 - CRIStAL-CNRS
*)

Require Import List.
Require Import Equality.
Require Import Eqdep.
Require Import PeanoNat.
Require Import Omega.

Require Import ModTypE1. 
Require Import TypSpecE1. 
Require Import LangSpecE1. 
Require Import StaticSemE2.
Require Import DynamicSemE2.
Require Import WeakenE2.
Require Import UniqueTypE2.
Require Import DerivDynE2.

Import ListNotations.


Module TSoundness (IdT: ModTyp) <: ModTyp.

Module DerivDynL := DerivDyn IdT.
Export DerivDynL.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.


(**********************************************************************)

Definition ExpDecrease_def :=     
  fun (fenv: funEnv) (env: valEnv)
      (a1 a2: AConfig Exp)  
      (k: EStep fenv env a1 a2) => 
    confFuel a2 <= confFuel a1.

Definition PrmsDecrease_def :=     
  fun (fenv: funEnv) (env: valEnv)
      (a1 a2: AConfig Prms) 
      (k: PStep fenv env a1 a2) =>
    confFuel a2 <= confFuel a1.

Definition Decrease_EStep_mut :=
  EStep_mut ExpDecrease_def PrmsDecrease_def. 

Definition Decrease_PStep_mut :=
  PStep_mut ExpDecrease_def PrmsDecrease_def. 

Lemma min_idem1 (n0 n1: nat) : min n0 n1 <= n0.   
    dependent induction n0.
    simpl.
    auto.
    simpl.
    destruct n1.
    omega.
    specialize (IHn0 n1).
    omega.
Defined.

Lemma min_eq (n0 n1: nat) : min n0 n1 <= min n1 n0.
  dependent induction n0.
  simpl.
  omega.
  simpl.
  destruct n1.
  omega.
  simpl.
  specialize (IHn0 n1).
  omega.
Defined.

Lemma min_idem2 (n0 n1: nat) : min n0 n1 <= n1.
  rewrite min_eq.
  eapply min_idem1.
Defined.
  

Lemma ExpSDecrease : forall (fenv: funEnv) (env: valEnv)
      (a1 a2: AConfig Exp)  
      (k: EStep fenv env a1 a2),
    confFuel a2 <= confFuel a1.
  intros.
  destruct a1.
  destruct a2.
  eapply Decrease_EStep_mut.
  - intros.
    unfold ExpDecrease_def.
    auto.
  - intros.
    unfold ExpDecrease_def.
    auto.
  - intros.
    unfold ExpDecrease_def in *.
    auto.
  - intros.
    unfold ExpDecrease_def.
    auto.
  - intros.
    unfold ExpDecrease_def in *.
    auto.
  - intros.
    unfold ExpDecrease_def.
    auto.
  - intros.
    unfold ExpDecrease_def in *.
    auto.
  - intros.
    unfold ExpDecrease_def.
    auto.
  - intros.
    unfold ExpDecrease_def.
    auto.
  - intros.
    unfold ExpDecrease_def in *.
    auto.
  - intros.
    unfold ExpDecrease_def in *.
    auto.
  - intros.
    unfold ExpDecrease_def in *.
    auto.
  - intros.
    unfold ExpDecrease_def.
    rewrite e0.
    simpl.
    eapply min_idem1.
  - intros.
    unfold ExpDecrease_def.
    auto.
  - intros.
    unfold ExpDecrease_def.
    simpl.
    auto.
  - intros.
    unfold ExpDecrease_def.
    simpl.
    auto.
  - intros.
    unfold ExpDecrease_def in *.
    auto.
  - intros.
    unfold PrmsDecrease_def in *.
    auto.
  - intros.
    unfold ExpDecrease_def, PrmsDecrease_def in *.
    auto.
  - intros.
    unfold ExpDecrease_def, PrmsDecrease_def in *.
    auto.    
    Unshelve.
    exact fenv.
    exact env.
    exact k.
Defined.    

Lemma PrmsSDecrease : forall (fenv: funEnv) (env: valEnv)
      (a1 a2: AConfig Prms)  
      (k: PStep fenv env a1 a2),
    confFuel a2 <= confFuel a1.
  intros.
  destruct a1.
  destruct a2.
  eapply Decrease_PStep_mut.
  - intros.
    unfold ExpDecrease_def.
    auto.
  - intros.
    unfold ExpDecrease_def.
    auto.
  - intros.
    unfold ExpDecrease_def in *.
    auto.
  - intros.
    unfold ExpDecrease_def.
    auto.
  - intros.
    unfold ExpDecrease_def in *.
    auto.
  - intros.
    unfold ExpDecrease_def.
    auto.
  - intros.
    unfold ExpDecrease_def in *.
    auto.
  - intros.
    unfold ExpDecrease_def.
    auto.
  - intros.
    unfold ExpDecrease_def.
    auto.
  - intros.
    unfold ExpDecrease_def in *.
    auto.
  - intros.
    unfold ExpDecrease_def in *.
    auto.
  - intros.
    unfold ExpDecrease_def in *.
    auto.
  - intros.
    unfold ExpDecrease_def.
    rewrite e0.
    simpl.
    eapply min_idem1.
  - intros.
    unfold ExpDecrease_def.
    auto.
  - intros.
    unfold ExpDecrease_def.
    simpl.
    auto.
  - intros.
    unfold ExpDecrease_def.
    simpl.
    auto.
  - intros.
    unfold ExpDecrease_def in *.
    auto.
  - intros.
    unfold PrmsDecrease_def in *.
    auto.
  - intros.
    unfold ExpDecrease_def, PrmsDecrease_def in *.
    auto.
  - intros.
    unfold ExpDecrease_def, PrmsDecrease_def in *.
    auto.
    Unshelve.
    exact fenv.
    exact env.
    exact k.
Defined.   

Lemma ExpTDecrease : forall (fenv: funEnv) (env: valEnv)
      (a1 a2: AConfig Exp)  
      (k: EClosure fenv env a1 a2),
    confFuel a2 <= confFuel a1.
  intros.
  dependent induction k.
  auto.
  eapply ExpSDecrease in e.
  omega.
Defined.

Lemma PrmsTDecrease : forall (fenv: funEnv) (env: valEnv)
      (a1 a2: AConfig Prms)  
      (k: PClosure fenv env a1 a2),
    confFuel a2 <= confFuel a1.
  intros.
  dependent induction k.
  auto.
  eapply PrmsSDecrease in p.
  omega.
Defined.
  
Lemma ExpDecrease : forall (fenv: funEnv) (env: valEnv)
      (s1 s2: W) (n1 n2: nat) (e1 e2: Exp)  
      (k: EClosure fenv env (Conf Exp s1 n1 e1) (Conf Exp s2 n2 e2)),
    n2 <= n1.
  intros.
  eapply ExpTDecrease in k.
  simpl in *.
  assumption.
Defined.  

Lemma PrmsDecrease : forall (fenv: funEnv) (env: valEnv)
      (s1 s2: W) (n1 n2: nat) (ps1 ps2: Prms)  
      (k: PClosure fenv env (Conf Prms s1 n1 ps1) (Conf Prms s2 n2 ps2)),
    n2 <= n1.
  intros.
  eapply PrmsTDecrease in k.
  simpl in *.
  assumption.
Defined.  


(**************************************************************************)

(** Type soundness *)

Definition SoundExp (fenv: funEnv) (env: valEnv)
                     (e: Exp) (t: VTyp) (s: W) (n: nat) : Type 
  := sigT2 (fun v: Value => VTyping v t)
           (fun v: Value => sigT (fun x: W * nat =>
                         EClosure fenv env (Conf Exp s n e)
                                           (Conf Exp (fst x) (snd x) (Val v)))).


Definition SoundPrms (fenv: funEnv) (env: valEnv)
                     (ps: Prms) (pt: PTyp) (s: W) (n: nat)  : Type
  := sigT (fun es: list Exp =>
       sigT2 (isValueList2T es) 
             (fun vs: list Value =>
               prod (PrmsTyping emptyE emptyE (PS es) pt)
                    (sigT (fun x: W * nat =>
                      PClosure fenv env (Conf Prms s n ps)
                                  (Conf Prms (fst x) (snd x) (PS es)))))).

(***********************************************************************)


(*
Definition IH_pack (n: nat): Type :=
                      forall (ftenv: funTC) (tenv: valTC) (t: VTyp) (e: Exp), 
                               ExpTyping ftenv tenv e t ->
                               forall (fenv: funEnv) (env: valEnv),   
                                   FEnvTyping fenv ftenv ->
                                   EnvTyping env tenv ->
                                   forall (s: W) (n': nat), n' < n ->
                                      SoundExp fenv env e t s n'. 

Definition IH_pack1 (n: nat) (e: Exp) : Type :=
                      forall (ftenv: funTC) (tenv: valTC) (t: VTyp), 
                               ExpTyping ftenv tenv e t ->
                               forall (fenv: funEnv) (env: valEnv),   
                                   FEnvTyping fenv ftenv ->
                                   EnvTyping env tenv ->
                                   forall (s: W) (n': nat), n' < n ->
                                      SoundExp fenv env e t s n'. 

Definition IH_pack2 (ftenv: funTC) (tenv: valTC) (e: Exp) (t: VTyp) 
                     (k: ExpTyping ftenv tenv e t) (n: nat) : Type :=
                               forall (fenv: funEnv) (env: valEnv),   
                                   FEnvTyping fenv ftenv ->
                                   EnvTyping env tenv ->
                                   forall (s: W) (n': nat), n' < n ->
                                      SoundExp fenv env e t s n'. 

Inductive packIA : Type := 
| packIA_E: forall (ftenv: funTC) (tenv: valTC) (e: Exp) (t: VTyp) 
                   (k: ExpTyping ftenv tenv e t) (n: nat), packIA
| packIA_P: forall (ftenv: funTC) (tenv: valTC) (ps: Prms) (pt: PTyp) 
                   (k: PrmsTyping ftenv tenv ps pt) (n: nat), packIA. 

(** datatype including expressions and expression lists *)
Inductive abspackIA : Type :=
| abspackIA_E : forall (e: Exp) (n: nat), abspackIA
| abspackIA_P : forall (es: list Exp) (n: nat), abspackIA.     
*)

Definition ExpSoundness_def (n9: nat) :=
     fun (ftenv: funTC) (tenv: valTC)
         (e: Exp) (t: VTyp) 
         (k: ExpTyping ftenv tenv e t) =>
   forall (fenv: funEnv) (env: valEnv) (D: FEnvWT fenv),                      
   FEnvTyping fenv ftenv ->
   EnvTyping env tenv ->
   forall (s: W) (n: nat), n <= n9 -> SoundExp fenv env e t s n.

Definition PrmsSoundness_def (n9: nat) :=
     fun (ftenv: funTC) (tenv: valTC)
         (ps: Prms) (pt: PTyp) 
         (k: PrmsTyping ftenv tenv ps pt) => 
   forall (fenv: funEnv) (env: valEnv) (D: FEnvWT fenv),                      
   FEnvTyping fenv ftenv ->
   EnvTyping env tenv ->
   forall (s: W) (n: nat), n <= n9 -> SoundPrms fenv env ps pt s n.  


Definition TSoundness_ExpTyping_mut (n: nat) :=
  ExpTyping_mut (ExpSoundness_def n) (PrmsSoundness_def n). 

Definition TSoundness_PrmsTyping_mut (n: nat) :=
  PrmsTyping_mut (ExpSoundness_def n) (PrmsSoundness_def n). 


Lemma ExpSoundness_Val: forall (n: nat)
    (ftenv : funTC) (tenv : valTC) (v : Value) 
    (t : VTyp) (v0 : VTyping v t),
  ExpSoundness_def n ftenv tenv (Val v) t (Val_Typing ftenv tenv v t v0).
    unfold ExpSoundness_def, SoundExp.
    intros.
    constructor 1 with (x:=v).
    assumption.
    constructor 1 with (x:=(s,n0)).
    simpl.
    constructor.
Defined.

Lemma ExpSoundness_Var : forall (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (t : VTyp) (i : IdTyping tenv x t),
   ExpSoundness_def n ftenv tenv (Var x) t (Var_Typing ftenv tenv x t i).
unfold ExpSoundness_def, SoundExp.
    intros.
    inversion i; subst.
    inversion X0; subst.
    unfold EnvTyping in X0.    
    eapply ExtRelVal2 with (f:=valueVTyp) (venv:=env) in H0.
    destruct H0.
    constructor 1 with (x:=x0).
    unfold VTyping.
    exact e0.
    constructor 1 with (x:=(s,n0)).
    simpl.
    eapply StepIsEClos.
    constructor.
    assumption.
    assumption.
Defined.
    
Lemma ExpSoundness_BindN : forall (n: nat)
    (ftenv : funTC) (tenv : valTC) (e1 e2 : Exp) 
    (t1 t2 : VTyp) (e : ExpTyping ftenv tenv e1 t1),
  ExpSoundness_def n ftenv tenv e1 t1 e ->
  forall e0 : ExpTyping ftenv tenv e2 t2,
  ExpSoundness_def n ftenv tenv e2 t2 e0 ->
  ExpSoundness_def n ftenv tenv (BindN e1 e2) t2
    (BindN_Typing ftenv tenv e1 e2 t1 t2 e e0).
    unfold ExpSoundness_def, SoundExp.
    intros.
    specialize (X fenv env D X1 X2 s n0 H).
    destruct X as [v1 k1 X].
    destruct X as [w1 H1].
    destruct w1 as [s1 n1].
    assert (n1 <= n) as H2.
    eapply ExpDecrease in H1.
    simpl in H1.
    omega.
    specialize (X0 fenv env D X1 X2 s1 n1 H2).
    destruct X0 as [v2 k3 X0].
    destruct X0 as [w2 H3].
    destruct w2 as [s2 n2].
    simpl in *.
    constructor 1 with (x:=v2).
    assumption.
    constructor 1 with (x:=(s2,n2)).
    simpl.
    eapply BindN_FStep.
    eassumption. 
    assumption.
Defined.

Lemma ExpSoundness_BindS : forall (n: nat)
    (ftenv : funTC) (tenv tenv' : valTC) (x : StaticSemL.Id)
    (e1 e2 : Exp) (t1 t2 : VTyp) (m : option VTyp) 
    (m0 : Maybe t1 m) (e : tenv' = (x, t1) :: tenv)
    (e0 : ExpTyping ftenv tenv e1 t1),
  ExpSoundness_def n ftenv tenv e1 t1 e0 ->
  forall e3 : ExpTyping ftenv tenv' e2 t2,
  ExpSoundness_def n ftenv tenv' e2 t2 e3 ->
  ExpSoundness_def n ftenv tenv (BindS x m e1 e2) t2
    (BindS_Typing ftenv tenv tenv' x e1 e2 t1 t2 m m0 e e0 e3).
    unfold ExpSoundness_def, SoundExp.
    intros.
    specialize (X fenv env D X1 X2 s n0 H).
    destruct X as [v1 k1 X]. 
    destruct X as [w1 H1].
    destruct w1 as [s1 n1].
    simpl in H1.
    assert (EnvTyping ((x,v1)::env) ((x,t1)::tenv)) as X3.
    {+ eapply updateEnvLemma.
       assumption.
       inversion k1; subst.
       reflexivity.
    }
    inversion e; subst.
    specialize (X0 fenv ((x,v1)::env) D X1 X3 s1 n1).
    assert (n1 <= n) as K2.
    eapply ExpDecrease in H1.
    omega.
    specialize (X0 K2).
    destruct X0 as [v2 k3 X0].
    destruct X0 as [w2 H2].
    destruct w2 as [s2 n2].
    simpl in *.
    constructor 1 with (x:=v2).
    assumption.
    constructor 1 with (x:=(s2,n2)).
    simpl.
    eapply BindS_FStep.
    eassumption. 
    assumption.
Defined.

Lemma ExpSoundness_BindMS : forall (n: nat)
    (ftenv : funTC) (tenv tenv0 tenv1 : valTC) 
    (env0 : valEnv) (e : Exp) (t : VTyp) (e0 : EnvTyping env0 tenv0)
    (e1 : tenv1 = tenv0 ++ tenv) (e2 : ExpTyping ftenv tenv1 e t),
  ExpSoundness_def n ftenv tenv1 e t e2 ->
  ExpSoundness_def n ftenv tenv (BindMS env0 e) t
             (BindMS_Typing ftenv tenv tenv0 tenv1 env0 e t e0 e1 e2).
    unfold ExpSoundness_def, SoundExp.
    intros.
    inversion e1; subst.
    eapply (overrideEnvLemma valueVTyp env0 env tenv0 tenv e0) in X1.
    specialize (X fenv (env0 ++ env) D X0 X1 s n0 H).
    destruct X as [v1 k1 X].
    destruct X as [w1 H1].
    destruct w1 as [s1 n1].
    simpl in *.
    constructor 1 with (x:=v1).
    assumption.
    constructor 1 with (x:=(s1,n1)).
    simpl.
    eapply BindMS_FStep.
    eassumption. 
Defined.

Lemma ExpSoundness_IfThenElse : forall (n: nat)
    (ftenv : funTC) (tenv : valTC) (e1 e2 e3 : Exp) 
    (t : VTyp) (e : ExpTyping ftenv tenv e1 Bool),
  ExpSoundness_def n ftenv tenv e1 Bool e ->
  forall e0 : ExpTyping ftenv tenv e2 t,
  ExpSoundness_def n ftenv tenv e2 t e0 ->
  forall e4 : ExpTyping ftenv tenv e3 t,
  ExpSoundness_def n ftenv tenv e3 t e4 ->
  ExpSoundness_def n ftenv tenv (IfThenElse e1 e2 e3) t
    (IfThenElse_Typing ftenv tenv e1 e2 e3 t e e0 e4).
    unfold ExpSoundness_def, SoundExp.
    intros.
    specialize (X fenv env D X2 X3 s n0 H).
    destruct X as [v1 k1 X].
    destruct X as [w1 H1].
    destruct w1 as [s1 n1].
    simpl in *.
    destruct v1.
    destruct v; unfold sVTyp in v.
    inversion k1; subst.
    simpl in *.
    inversion H0; subst.
    simpl in v.
    destruct v.
    + specialize (X0 fenv env D X2 X3 s1 n1).
      assert (n1 <= n) as K.
      eapply ExpDecrease in H1.
      omega.
      specialize (X0 K).
      destruct X0 as [v2 k3 X0].
      destruct X0 as [w2 H3].
      destruct w2 as [s2 n2].
      simpl in *.
      constructor 1 with (x:=v2).
      assumption.
      constructor 1 with (x:=(s2,n2)).
      simpl in *.
      eapply IfThenElse_FStep1.
      eassumption.
      assumption.
    + specialize (X1 fenv env D X2 X3 s1 n1).
      assert (n1 <= n) as K.
      eapply ExpDecrease in H1.
      omega.
      specialize (X1 K).      
      destruct X1 as [v2 k3 X1].
      destruct X1 as [w2 H3].
      destruct w2 as [s2 n2].
      simpl in *.
      constructor 1 with (x:=v2).
      assumption.
      constructor 1 with (x:=(s2,n2)).
      simpl in *.
      eapply IfThenElse_FStep2.
      eassumption.
      assumption.
Defined.

Lemma ExpSoundness_Apply0 :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (e : Exp) (ps : Prms) (pt : PTyp) (t : VTyp) (p : Pure e)
    (i : IdFTyping ftenv x (FT pt t)) (p0 : PrmsTyping ftenv tenv ps pt),
  PrmsSoundness_def 0 ftenv tenv ps pt p0 ->
  forall e0 : ExpTyping ftenv tenv e Nat,
  ExpSoundness_def 0 ftenv tenv e Nat e0 ->
  ExpSoundness_def 0 ftenv tenv (Apply x ps e) t
                   (Apply_Typing ftenv tenv x e ps pt t p i p0 e0).
    unfold ExpSoundness_def, SoundExp, PrmsSoundness_def, SoundPrms.
    intros.
    specialize (X0 fenv env D X1 X2 s n H).
    destruct X0 as [v1 k1 X0].
    destruct X0 as [w X0].
    destruct w as [s1 n1].
    simpl in *.
    generalize X0.
    intro X3.
    eapply (Pure_sideffect _ _ _ _ _ _ _ _ p) in X0.
    destruct X0.
    inversion H0; subst.
    
    specialize (X fenv env D X1 X2 s1 n1 H).
    destruct X as [es X].
    destruct X as [vs k2 X].
    destruct X as [k3 X].
    destruct X as [w2 H4].
    destruct w2 as [s2 n2].
    simpl in *.
    inversion k2; subst.
    eapply VTyping_lemma in k1.
    destruct k1 as [n0 k1].
    cbv in n0.
    (* unfold sVTyp in n0; unfold Nat in n0; simpl in n0. *)
    inversion i; subst.
    unfold FEnvTyping in X1.
    eapply ExtRelVal2 with (f:=funFTyp) (venv:=fenv) in H0.
    destruct H0 as [f H0 H3].
    remember (min n2 n0) as n3.

    assert (funArity f = length vs) as H5.
    {+ destruct pt.
       eapply PrmsArity_lemma in k3.
       destruct f.
       inversion H3; subst.
       unfold funArity.
       rewrite map_length in k3.
       rewrite map_length in k3.
       symmetry.
       exact k3.
    }
    
    eapply (Apply_FStep0 fenv env s1 s2 n1 n2 n0 x e
                         (cst Nat n0) _ vs f ps X3) in H4.
    instantiate (1:=fun0Exp f) in H4.
    
    econstructor 1 with (x:=fun0Exp f).

    eapply FunTyping0_lemma.
    exact D.
    exact X1.
    exact H0.
    reflexivity.
    unfold funFTyp in H3.
    unfold funVTyp.
    destruct f.
    inversion H3; subst.
    reflexivity.

    econstructor 1 with (x:= (s2,n2)).
    simpl.
    exact H4.
    assumption.
    reflexivity.
    reflexivity.
    assert (n1 = 0) as H6.
    omega.
    assert (n2 <= n1) as H7.
    eapply PrmsDecrease in H4.
    assumption.
    omega.
    assumption.
    assumption.
Defined.
    
Lemma ExpSoundness_Call0 :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  PrmsSoundness_def 0 ftenv tenv (PS ls) pt p ->
  ExpSoundness_def 0 ftenv tenv (Call x (PS ls)) t
                   (Call_Typing ftenv tenv x ls pt t i p).
    unfold ExpSoundness_def, SoundExp, PrmsSoundness_def, SoundPrms.
    intros.
    specialize (X fenv env D X0 X1 s n H).
    destruct X as [es X].
    destruct X as [vs k2 X].
    destruct X as [k3 X].
    destruct X as [w2 H4].
    destruct w2 as [s2 n2].
    simpl in *.
    inversion k2; subst.
    assert (n = 0) as H2.
    omega.
    inversion H2; subst.
    clear H H0.
    
    inversion i; subst.
    unfold FEnvTyping in X0.
    eapply ExtRelVal2 with (f:=funFTyp) (venv:=fenv) in H.
    destruct H as [f H0 H3].

    assert (funArity f = length vs) as H5.
    {+ destruct pt.
       eapply PrmsArity_lemma in k3.
       destruct f.
       inversion H3; subst.
       unfold funArity.
       rewrite map_length in k3.
       rewrite map_length in k3.
       symmetry.
       exact k3.
    }
    
    eapply Call_FStep01 with (x:=x) (v:=fun0Exp f) in H4.
   
    econstructor 1 with (x:=fun0Exp f).

    eapply FunTyping0_lemma.
    exact D.
    exact X0.
    exact H0.
    reflexivity.
    unfold funFTyp in H3.
    unfold funVTyp.
    destruct f.
    inversion H3; subst.
    reflexivity.

    econstructor 1 with (x:= (s2,n2)).
    simpl.
    exact H4.
    eassumption.
    reflexivity.
    assumption.
    assert (n2 <= 0) as H6.
    eapply PrmsDecrease in H4.
    assumption.
    omega.
    assumption.
Defined.    
(*
Lemma Modify_FStep1 :   
   forall (n: nat) (fenv: funEnv) (env: valEnv)
          (s0 s1 s2: W) (n0 n1: nat) (t1 t2: VTyp)
          (xf: XFun t1 t2)
          (e: Exp) (v1: sVTyp t1) (v2: Value),
     EClosure [] env (Conf Exp s0 n0 e) (Conf Exp s1 n1 (Val (cst t1 v1))) ->
     v2 = (cst t2 (x_eval t1 t2 xf s1 v1)) ->
     s2 = x_exec t1 t2 xf s1 v1 -> 
     EClosure fenv env (Conf Exp s0 n0 (Modify t1 t2 xf e))
                       (Conf Exp s2 n1 (Val v2)).
  intros.
  unfold cst in X.
*)  


Lemma ExpSoundness_Modify :
forall (n: nat) (ftenv : funTC) (tenv : valTC) (t1 t2 : VTyp) 
    (XF : XFun t1 t2) (e : Exp) (e0 : ExpTyping ftenv tenv e t1),
  ExpSoundness_def n ftenv tenv e t1 e0 ->
  ExpSoundness_def n ftenv tenv (Modify t1 t2 XF e) t2
    (Modify_Typing ftenv tenv t1 t2 XF e e0).
    unfold ExpSoundness_def, SoundExp.
    intros.
    specialize (X fenv env D X0 X1 s n0 H).
    destruct X as [v1 k1 X].
    destruct X as [w1 H1].
    destruct w1 as [s1 n1].
    simpl in *.
    destruct v1.
    destruct v.
    inversion k1; subst.
    eapply (Modify_FStep 0) with (t2:=t2) (xf:=XF)
         (s2:= x_exec (valueVTyp (existT ValueI x (Cst x v))) t2 XF v s1)
         (v2 := cst t2 (x_eval x t2 XF v s1)) in H1.
    econstructor 1 with (x:=cst t2 (x_eval x t2 XF v s1)).
    constructor.
    simpl in *.
    econstructor 1 with (x:= (x_exec x t2 XF v s1, n1)).
    simpl.
    eassumption.
    simpl.
    auto.
    auto.
Defined.    


Lemma ExpSoundness_PrmsNil : forall (n: nat) (ftenv : funTC) (tenv : valTC),
    PrmsSoundness_def n ftenv tenv (PS []) (PT []) (PSNil_Typing ftenv tenv).
    unfold PrmsSoundness_def, SoundPrms.
    intros.
    econstructor 1 with (x:=nil).
    econstructor 1 with (x:=nil).
    econstructor.
    simpl.
    auto.
    econstructor.
    econstructor.
    econstructor 1 with (x:=(s,n0)).
    simpl.
    constructor.
Defined.    

Lemma ExpSoundness_PrmsCons :
  forall (n: nat) (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp) 
    (es : list Exp) (ts : list VTyp) (e0 : ExpTyping ftenv tenv e t),
  ExpSoundness_def n ftenv tenv e t e0 ->
  forall p : PrmsTyping ftenv tenv (PS es) (PT ts),
  PrmsSoundness_def n ftenv tenv (PS es) (PT ts) p ->
  PrmsSoundness_def n ftenv tenv (PS (e :: es)) (PT (t :: ts))
                    (PSCons_Typing ftenv tenv e t es ts e0 p).
    unfold PrmsSoundness_def, SoundPrms.
    unfold ExpSoundness_def, SoundExp.
    intros.
    specialize (X fenv env D X1 X2 s n0 H).
    destruct X as [v1 k1 X].
    destruct X as [w X].
    destruct w as [s1 n1].
    simpl in *.
    assert (n1 <= n0).
    eapply ExpDecrease in X.
    assumption.
    assert (n1 <= n).
    omega.
    specialize (X0 fenv env D X1 X2 s1 n1 H1).
    destruct X0 as [es0 X0].
    destruct X0 as [vs k2 X0].
    destruct X0 as [k3 X0].
    destruct X0 as [w k4].
    destruct w as [s2 n2].
    econstructor 1 with (x:= (Val v1)::es0).
    econstructor 1 with (x:= v1::vs).
    econstructor.
    simpl.
    inversion k2; subst.
    auto.
    split.
    econstructor.
    econstructor.
    assumption.
    assumption.
    econstructor 1 with (x:=(s2,n2)).
    simpl in *.
    eapply PConcat.
    eapply Prms_extended_congruence2.
    eassumption.
    eapply Prms_extended_congruence1.
    assumption.
Defined.    
    
Lemma ExpSoundness_Call : forall (n: nat)
    (IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
        ExpTyping ftenv tenv e t ->
        forall (fenv : funEnv) (env : valEnv),
        FEnvWT fenv ->
        FEnvTyping fenv ftenv ->
        EnvTyping env tenv ->
        forall (s : W) (n0 : nat), n0 <= n -> SoundExp fenv env e t s n0), 
 forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
      (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
      (p : PrmsTyping ftenv tenv (PS ls) pt),
    PrmsSoundness_def (S n) ftenv tenv (PS ls) pt p ->
    ExpSoundness_def (S n) ftenv tenv (Call x (PS ls)) t
    (Call_Typing ftenv tenv x ls pt t i p).
    unfold ExpSoundness_def, SoundExp, PrmsSoundness_def, SoundPrms.
    intros.
    specialize (X fenv env D X0 X1 s n0 H).
    destruct X as [es X].
    destruct X as [vs k2 X].
    destruct X as [k3 X].
    destruct X as [w2 H4].
    destruct w2 as [s2 n2].
    simpl in *.
    inversion k2; subst.
(*    assert (n = 0) as H2.
    omega.
    inversion H2; subst.
    clear H H0.*)
    
    inversion i; subst.
    unfold FEnvTyping in X0.
    eapply ExtRelVal2 with (f:=funFTyp) (venv:=fenv) in H0.
    destruct H0 as [f H0 H3].

    assert (funArity f = length vs) as H5.
    {+ destruct pt.
       eapply PrmsArity_lemma in k3.
       destruct f.
       inversion H3; subst.
       unfold funArity.
       rewrite map_length in k3.
       rewrite map_length in k3.
       symmetry.
       exact k3.
    }

    destruct n2.
    
    eapply Call_FStep01 with (x:=x) (v:=fun0Exp f) in H4.
   
    econstructor 1 with (x:=fun0Exp f).
    
    eapply FunTyping0_lemma.
    exact D.
    exact X0.
    exact H0.
    reflexivity.
    symmetry.
    eapply funFTyp_lemma.
    eassumption.
    
    econstructor 1 with (x:= (s2,0)).
    simpl.
    exact H4.
    eassumption.
    reflexivity.
    assumption.
    auto.
   
(**)
    specialize (IHn ftenv tenv (BindMS (mkVEnv (funValTC f) vs) (funSExp f)) t).
    
    assert (ExpTyping ftenv tenv
                      (BindMS (mkVEnv (funValTC f) vs) (funSExp f)) t) as X.
    econstructor.
    instantiate (1:=funValTC f).
    eapply mkVEnv_typing_lemma.
    eassumption.
    assumption.
    reflexivity.
    
    eapply ExpTWeaken with (ftenv1:=ftenv) (tenv1:=funValTC f).
    eapply  FunTypingS_lemma.
    exact D.
    assumption.
    eassumption.
    auto.
    auto.
    symmetry.
    eapply funFTyp_lemma.
    eassumption.
    instantiate (1:=nil).
    
    rewrite app_nil_r.
    auto.
    reflexivity.
    
    specialize (IHn X fenv env D X0 X1 s2 n2).
    assert (S n2 <= n0) as H1.
    eapply PrmsDecrease in H4.
    assumption.
    assert (n2 <= n) as H6.
    omega.
    specialize (IHn H6).

    destruct IHn as [v3 k1 IH].
    destruct IH as [w IH].
    destruct w as [s3 n3].
    simpl in *.

    eapply (Call_FStepS fenv env _ _ _ _ _ _ x _ _ _ _ H0 H5 IH) in H4.
    econstructor 1 with (x:=v3).
    assumption.
    econstructor 1 with (x:=(s3,n3)).
    simpl in *.
    assumption.
    assumption.
Defined.    

(*
Lemma ExpSoundness_Call : forall (n: nat)
    (IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
        ExpTyping ftenv tenv e t ->
        forall (fenv : funEnv) (env : valEnv),
        FEnvWT fenv ->
        FEnvTyping fenv ftenv ->
        EnvTyping env tenv ->
        forall (s : W) (n0 : nat), n0 <= n -> SoundExp fenv env e t s n0), 
 forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
      (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
      (p : PrmsTyping ftenv tenv (PS ls) pt),
    PrmsSoundness_def (S n) ftenv tenv (PS ls) pt p ->
    ExpSoundness_def (S n) ftenv tenv (Call x (PS ls)) t
    (Call_Typing ftenv tenv x ls pt t i p).
*)


Lemma ExpSoundness_Apply : forall (n: nat) 
(IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
        ExpTyping ftenv tenv e t ->
        forall (fenv : funEnv) (env : valEnv),
        FEnvWT fenv ->
        FEnvTyping fenv ftenv ->
        EnvTyping env tenv ->
        forall (s : W) (n0 : nat), n0 <= n -> SoundExp fenv env e t s n0),      
 forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (e : Exp) (ps : Prms) (pt : PTyp) (t : VTyp) (p : Pure e)
    (i : IdFTyping ftenv x (FT pt t)) (p0 : PrmsTyping ftenv tenv ps pt),
  PrmsSoundness_def (S n) ftenv tenv ps pt p0 ->
  forall e0 : ExpTyping ftenv tenv e Nat,
  ExpSoundness_def (S n) ftenv tenv e Nat e0 ->
  ExpSoundness_def (S n) ftenv tenv (Apply x ps e) t
    (Apply_Typing ftenv tenv x e ps pt t p i p0 e0).
Proof.
    unfold ExpSoundness_def, SoundExp, PrmsSoundness_def, SoundPrms.
    intros.
    specialize (X0 fenv env D X1 X2 s n0 H).
    destruct X0 as [v1 k1 X0].
    destruct X0 as [w X0].
    destruct w as [s1 n1].
    simpl in *.
    generalize X0.
    intro X3.
    eapply (Pure_sideffect _ _ _ _ _ _ _ _ p) in X0.
    destruct X0.
    inversion H0; subst.
    
    specialize (X fenv env D X1 X2 s1 n1 H).
    destruct X as [es X].
    destruct X as [vs k2 X].
    destruct X as [k3 X].
    destruct X as [w2 H4].
    destruct w2 as [s2 n2].
    simpl in *.
    inversion k2; subst.

    inversion i; subst.
    (* unfold FEnvTyping in X1. *)
    eapply ExtRelVal2 with (f:=funFTyp) (venv:=fenv) in H0.
    destruct H0 as [f H0 H3].

    assert (funArity f = length vs) as H5.
    {+ destruct pt.
       eapply PrmsArity_lemma in k3.
       destruct f.
       inversion H3; subst.
       unfold funArity.
       rewrite map_length in k3.
       rewrite map_length in k3.
       symmetry.
       exact k3.
    }

    inversion k1; subst.
    unfold valueVTyp in H6.
    destruct v1.
    simpl in *.
    inversion H6; subst.
    clear H1 H2.
    destruct v as [n0].
    unfold sVTyp in n0.
    unfold Nat in n0.
    simpl in n0.

    destruct n2.

    eapply (Apply_FStep0 fenv env s1 s2 n1 0 n0 x e _
                         (fun0Exp f) vs _ _ X3) in H4.   
   
    econstructor 1 with (x:=fun0Exp f).
    
    eapply FunTyping0_lemma.
    exact D.
    exact X1.
    exact H0.
    reflexivity.
    symmetry.
    eapply funFTyp_lemma.
    eassumption.
    
    econstructor 1 with (x:= (s2,0)).
    simpl.
    exact H4.
    eassumption.
    reflexivity.
    unfold cst.
    auto.
    auto.
    assumption.

(**)
    
    destruct n0.

    assert (min (S n2) 0 = 0) as k5.
    simpl.
    auto.
    eapply (Apply_FStep fenv env s1 s2 n1 (S n2) 0
                        (min (S n2) 0) x e _ vs f ps) in H4.
    rewrite k5 in *.
    simpl in *.
    clear k5.

    eapply (Call_FStep0 fenv env s2 0 x (fun0Exp f) vs f H0) in H5.

    econstructor 1 with (x:=fun0Exp f).
    eapply VTypingFun0_lemma.
    exact D.
    eassumption.
    eassumption.
    reflexivity.
    symmetry.
    eapply funFTyp_lemma.
    eassumption.

    econstructor 1 with (x:= (s2,0)).
    simpl in *.
    eapply EClosConcat.
    exact H4.
    exact H5.
    auto.
    auto.
    exact X3.
    auto.
    auto.
    assumption.
        
(**)
    
    specialize (IHn ftenv tenv (BindMS (mkVEnv (funValTC f) vs) (funSExp f)) t).
    
    assert (ExpTyping ftenv tenv
                      (BindMS (mkVEnv (funValTC f) vs) (funSExp f)) t) as X.
    econstructor.
    instantiate (1:=funValTC f).
    eapply mkVEnv_typing_lemma.
    eassumption.
    assumption.
    reflexivity.
    
    eapply ExpTWeaken with (ftenv1:=ftenv) (tenv1:=funValTC f).
    eapply  FunTypingS_lemma.
    exact D.
    assumption.
    eassumption.
    auto.
    auto.
    symmetry.
    eapply funFTyp_lemma.
    eassumption.
    instantiate (1:=nil).
    
    rewrite app_nil_r.
    auto.
    reflexivity.
    
    specialize (IHn X fenv env D X1 X2).
    specialize (IHn s2 (min n2 n0)).
    assert (S n2 <= n1) as H1.
    eapply PrmsDecrease in H4.
    assumption.
    assert (n2 <= n) as H6.
    omega.
    assert ((min n2 n0) <= n2) as H7.
    eapply min_idem1.
    assert ((min n2 n0) <= n) as H8.
    omega.
    
    specialize (IHn H8).

    destruct IHn as [v3 k4 IH].
    destruct IH as [w IH].
    destruct w as [s3 n3].
    simpl in *.

    eapply EClosWeaken with (fenv:=fenv) (env:=env) in X3.
    destruct ps.
    eapply (Apply_FStepS fenv env s1 s2 s3 n1 n2 n3 n0 _
                         x v3 vs e f es) in IH.
    econstructor 1 with (x:=v3).
    assumption.
    econstructor 1 with (x:=(s3,n3)).
    simpl.
    assumption.
    assumption.
    assumption.
    auto.
    assumption.
    assumption.
    instantiate (1:=nil).
    rewrite app_nil_r.
    auto.
    instantiate (1:=nil).
    rewrite app_nil_r.
    auto.
    assumption.
Defined.    

    
Lemma ExpSoundnessA :
   forall (n9: nat) (ftenv: funTC) (tenv: valTC)
          (e: Exp) (t: VTyp), 
          ExpTyping ftenv tenv e t ->
          forall (fenv: funEnv) (env: valEnv) (D: FEnvWT fenv),   
                 FEnvTyping fenv ftenv ->
                 EnvTyping env tenv ->
                 forall (s: W) (n: nat), n <= n9 ->
                   SoundExp fenv env e t s n.
Proof.
  intro n.
  induction n.
  eapply (TSoundness_ExpTyping_mut 0).
  - eapply (ExpSoundness_Val 0).
  - eapply (ExpSoundness_Var 0).
  - eapply (ExpSoundness_BindN 0).
  - eapply (ExpSoundness_BindS 0).
  - eapply (ExpSoundness_BindMS 0).
  - eapply (ExpSoundness_IfThenElse 0).
  - eapply ExpSoundness_Apply0. 
  - eapply ExpSoundness_Call0.
  - eapply (ExpSoundness_Modify 0).
  - eapply (ExpSoundness_PrmsNil 0).
  - eapply (ExpSoundness_PrmsCons 0).   
  - eapply (TSoundness_ExpTyping_mut (S n)).
    + eapply (ExpSoundness_Val (S n)).
    + eapply (ExpSoundness_Var (S n)).
    + eapply (ExpSoundness_BindN (S n)).
    + eapply (ExpSoundness_BindS (S n)).
    + eapply (ExpSoundness_BindMS (S n)).
    + eapply (ExpSoundness_IfThenElse (S n)).
    + eapply ExpSoundness_Apply.
      auto.
    + eapply ExpSoundness_Call.
      auto.
    + eapply (ExpSoundness_Modify (S n)).
    + eapply (ExpSoundness_PrmsNil (S n)).   
    + eapply (ExpSoundness_PrmsCons (S n)).
Defined.      


Lemma PrmsSoundness_Apply : forall (n: nat) 
    (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (e : Exp) (ps : Prms) (pt : PTyp) (t : VTyp) (p : Pure e)
    (i : IdFTyping ftenv x (FT pt t)) (p0 : PrmsTyping ftenv tenv ps pt),
  PrmsSoundness_def (S n) ftenv tenv ps pt p0 ->
  forall e0 : ExpTyping ftenv tenv e Nat,
  ExpSoundness_def (S n) ftenv tenv e Nat e0 ->
  ExpSoundness_def (S n) ftenv tenv (Apply x ps e) t
    (Apply_Typing ftenv tenv x e ps pt t p i p0 e0).
  unfold ExpSoundness_def.
  intros.
  eapply ExpSoundnessA with (ftenv:=ftenv) (tenv:=tenv).
  econstructor.
  assumption.
  eassumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  eassumption.
Defined.

Lemma PrmsSoundness_Call : forall (n: nat) 
    (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  PrmsSoundness_def (S n) ftenv tenv (PS ls) pt p ->
  ExpSoundness_def (S n) ftenv tenv (Call x (PS ls)) t
    (Call_Typing ftenv tenv x ls pt t i p).
  unfold ExpSoundness_def.
  intros.
  eapply ExpSoundnessA with (ftenv:=ftenv) (tenv:=tenv).
  econstructor.
  eassumption.
  assumption.
  assumption.
  assumption.
  assumption.
  eassumption.
Defined.


Lemma PrmsSoundnessA :
   forall (n9: nat) (ftenv: funTC) (tenv: valTC)
          (ps: Prms) (pt: PTyp), 
          PrmsTyping ftenv tenv ps pt ->
          forall (fenv: funEnv) (env: valEnv) (D: FEnvWT fenv),   
                 FEnvTyping fenv ftenv ->
                 EnvTyping env tenv ->
                 forall (s: W) (n: nat), n <= n9 ->
                   SoundPrms fenv env ps pt s n.
Proof.
  intro n.
  induction n.
  eapply (TSoundness_PrmsTyping_mut 0).
  - eapply (ExpSoundness_Val 0).
  - eapply (ExpSoundness_Var 0).
  - eapply (ExpSoundness_BindN 0).
  - eapply (ExpSoundness_BindS 0).
  - eapply (ExpSoundness_BindMS 0).
  - eapply (ExpSoundness_IfThenElse 0).
  - eapply ExpSoundness_Apply0. 
  - eapply ExpSoundness_Call0.
  - eapply (ExpSoundness_Modify 0).
  - eapply (ExpSoundness_PrmsNil 0).
  - eapply (ExpSoundness_PrmsCons 0).   
  - eapply (TSoundness_PrmsTyping_mut (S n)).
    + eapply (ExpSoundness_Val (S n)).
    + eapply (ExpSoundness_Var (S n)).
    + eapply (ExpSoundness_BindN (S n)).
    + eapply (ExpSoundness_BindS (S n)).
    + eapply (ExpSoundness_BindMS (S n)).
    + eapply (ExpSoundness_IfThenElse (S n)).
    + eapply PrmsSoundness_Apply.
    + eapply PrmsSoundness_Call.
    + eapply (ExpSoundness_Modify (S n)).
    + eapply (ExpSoundness_PrmsNil (S n)).   
    + eapply (ExpSoundness_PrmsCons (S n)). 
Defined.      


Lemma ExpSoundness :
   forall (ftenv: funTC) (tenv: valTC)
          (e: Exp) (t: VTyp), 
          ExpTyping ftenv tenv e t ->
          forall (fenv: funEnv) (env: valEnv) (D: FEnvWT fenv),   
                 FEnvTyping fenv ftenv ->
                 EnvTyping env tenv ->
                 forall (s: W) (n: nat), 
                   SoundExp fenv env e t s n.
Proof.
  intros.
  eapply (ExpSoundnessA n).
  eassumption.
  assumption.
  assumption.
  assumption.
  auto.
Defined.  

Lemma PrmsSoundness :
   forall (ftenv: funTC) (tenv: valTC)
          (ps: Prms) (pt: PTyp), 
          PrmsTyping ftenv tenv ps pt ->
          forall (fenv: funEnv) (env: valEnv) (D: FEnvWT fenv),   
                 FEnvTyping fenv ftenv ->
                 EnvTyping env tenv ->
                 forall (s: W) (n: nat),
                   SoundPrms fenv env ps pt s n.
Proof.
  intros.
  eapply (PrmsSoundnessA n).
  eassumption.
  assumption.
  assumption.
  assumption.
  auto.
Defined.  

Program Definition ExpEvalSOS (s: W) (n: nat) (fenv: funEnv)        
           (k1: FEnvWT fenv)
           (env: valEnv) (e: Exp) (t: VTyp) 
  (k2: ExpTyping (funEnv2funTC fenv) (valEnv2valTC env) e t) :
  SoundExp fenv env e t s n :=
  ExpSoundness (funEnv2funTC fenv) (valEnv2valTC env) e t k2
               fenv env k1 _ _ s n.
Next Obligation.
  constructor.
Defined.  
Next Obligation.
  constructor.    
Defined.

Program Definition PrmsEvalSOS (s: W) (n: nat) (fenv: funEnv)        
           (k1: FEnvWT fenv) 
           (env: valEnv) (ps: Prms) (pt: PTyp) 
  (k2: PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) ps pt) :
  SoundPrms fenv env ps pt s n :=
  PrmsSoundness (funEnv2funTC fenv) (valEnv2valTC env) ps pt k2
               fenv env k1 _ _ s n. 
Next Obligation.
  constructor.
Defined.
Next Obligation.
  constructor.    
Defined.
  
End TSoundness.

(*
Require Import Eqdep FunctionalExtensionality Coq.Program.Tactics.
Require Import Coq.Init.Specif.
Require Import Coq.Logic.JMeq.
*)
