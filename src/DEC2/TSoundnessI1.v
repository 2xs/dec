(*  DEC 2.0 language specification.
   Paolo Torrini  
   Universite' de Lille - CRIStAL-CNRS
*)

Require Import List.
Require Import Equality.
Require Import Eqdep.
Require Import PeanoNat.
Require Import Omega.

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

Import ListNotations.


Module TSoundness (IdT: ModTyp) <: ModTyp.

Module TransPrelimL := TransPrelim IdT.
Export TransPrelimL.

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
                prod (PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env)
                                 (PS es) pt)
                    (sigT (fun x: W * nat =>
                      PClosure fenv env (Conf Prms s n ps)
                                  (Conf Prms (fst x) (snd x) (PS es)))))).

(***********************************************************************)

Definition ExpSoundness_def (fenv: funEnv) (D: FEnvWT fenv) (n9: nat) :=
     fun (ftenv: funTC) (tenv: valTC)
         (e: Exp) (t: VTyp) 
         (k: ExpTyping ftenv tenv e t) =>    
     FEnvTyping fenv ftenv -> 
     forall  (env: valEnv),
     EnvTyping env tenv ->
     forall (n: nat), n <= n9 -> forall (s: W), SoundExp fenv env e t s n.

Definition PrmsSoundness_def (fenv: funEnv) (D: FEnvWT fenv) (n9: nat) :=
     fun (ftenv: funTC) (tenv: valTC)
         (ps: Prms) (pt: PTyp) 
         (k: PrmsTyping ftenv tenv ps pt) => 
     FEnvTyping fenv ftenv ->
     forall  (env: valEnv),
     EnvTyping env tenv ->
     forall (n: nat), n <= n9 -> forall (s: W), SoundPrms fenv env ps pt s n.  


Definition TSoundness_ExpTyping_mut
           (fenv: funEnv) (D: FEnvWT fenv) (n: nat) :=
  ExpTyping_mut (ExpSoundness_def fenv D n) (PrmsSoundness_def fenv D n). 

Definition TSoundness_PrmsTyping_mut
           (fenv: funEnv) (D: FEnvWT fenv) (n: nat) :=
  PrmsTyping_mut (ExpSoundness_def fenv D n) (PrmsSoundness_def fenv D n). 


(******************************************************************)

Lemma ExpSoundness_Val: forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv : valTC) (v : Value) 
    (t : VTyp) (v0 : VTyping v t),
    ExpSoundness_def fenv D n ftenv tenv (Val v) t
                     (Val_Typing ftenv tenv v t v0).
    unfold ExpSoundness_def, SoundExp.
    intros.
    constructor 1 with (x:=v).
    assumption.
    constructor 1 with (x:=(s,n0)).
    simpl.
    constructor.
Defined.

Lemma ExpSoundness_Var0 : forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (t : VTyp) (i : IdTyping tenv x t),
    ExpSoundness_def fenv D n ftenv tenv (Var x) t
                     (Var_Typing ftenv tenv x t i).
    unfold ExpSoundness_def, SoundExp.
    intros.
    inversion i; subst.
    inversion H0; subst.
    unfold EnvTyping in H0.    
    eapply ExtRelVal2 with (f:=valueVTyp) (venv:=env) in H3.
    destruct H3.
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


Lemma ExpSoundnessAux1_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id)
    (v : Value) 
    (t : VTyp) (i : IdTyping tenv x t) (mB: valueVTyp v = t)
    (fenv: funEnv) (env: valEnv) (mA: findE env x = Some v)
    (k1: FEnvWT fenv)                       
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)    
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
  SoundExp fenv env (Var x) t s0 n0.
  unfold SoundExp.
  intros.
  unfold IdTyping in i.
  unfold EnvrAssign in i.
  unfold EnvTyping in m2.
  unfold MatchEnvs in m2.
  rewrite m2 in i.
  clear m2.
  constructor 1 with (x:=v).
  unfold VTyping.
  exact mB.
  constructor 1 with (x:=(s0,n0)).
  simpl.
  eapply StepIsEClos.
  constructor.
  assumption.
Defined.

Lemma ExpSoundnessAux2_Var (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : Id)
    (v : Value) 
    (t : VTyp) (mB: valueVTyp v = t)
    (fenv: funEnv) (env: valEnv) (mA: findE env x = Some v)
    (k1: FEnvWT fenv)                       
    (m1: FEnvTyping fenv ftenv)
    (m2: EnvTyping env tenv)    
    (s0 : W) (n0 : nat) (m3: n0 <= n) :
  SoundExp fenv env (Var x) t s0 n0.
Proof.
  eapply (ExpSoundnessAux1_Var n ftenv tenv x v t
                                 (ExtRelTyp tenv x v t mB env m2 mA)
                                 mB fenv env mA k1 m1 m2 s0 n0 m3).
Defined.


Lemma ExpSoundnessA_Var : forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (t : VTyp) (i : IdTyping tenv x t),
    ExpSoundness_def fenv D n ftenv tenv (Var x) t
                     (Var_Typing ftenv tenv x t i).
  unfold ExpSoundness_def.
  intros.
  unfold EnvTyping in H0.
  eapply (ExpSoundnessAux2_Var n ftenv tenv x
       (*v*)(ExtRelVal2A_1 valueVTyp tenv env x t H0 i) t
       (*mB*)(ExtRelVal2A_4 valueVTyp tenv env x t H0 i)     
        fenv env                                          
       (*mA*)(ExtRelVal2A_2 valueVTyp tenv env x t H0 i) 
        D H H0 s n0 H1).
Defined.

Lemma ExpSoundness_Var : forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (t : VTyp) (i : IdTyping tenv x t),
    ExpSoundness_def fenv D n ftenv tenv (Var x) t
                     (Var_Typing ftenv tenv x t i).
  unfold ExpSoundness_def.
  intros.
  unfold EnvTyping in H0.
  inversion H0; subst.
  set (tenv:= map (thicken StaticSemL.Id valueVTyp) env).
  eapply (ExpSoundnessAux2_Var n ftenv tenv x
       (*v*)(ExtRelVal2B_1 env x t i) t
       (*mB*)(ExtRelVal2B_4 env x t i)     
        fenv env                                          
       (*mA*)(ExtRelVal2B_2 env x t i) 
        D H H0 s n0 H1).
Defined.


Lemma ExpSoundness_BindN : forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv : valTC) (e1 e2 : Exp) 
    (t1 t2 : VTyp) (e : ExpTyping ftenv tenv e1 t1),
  ExpSoundness_def fenv D n ftenv tenv e1 t1 e ->
  forall e0 : ExpTyping ftenv tenv e2 t2,
  ExpSoundness_def fenv D n ftenv tenv e2 t2 e0 ->
  ExpSoundness_def fenv D n ftenv tenv (BindN e1 e2) t2
    (BindN_Typing ftenv tenv e1 e2 t1 t2 e e0).
    unfold ExpSoundness_def, SoundExp.
    intros.
    specialize (X H env H0 n0 H1 s).
    destruct X as [v1 k1 X].
    destruct X as [w1 H4].
    destruct w1 as [s1 n1].
    assert (n1 <= n) as H2.
    eapply ExpDecrease in H4.
    simpl in H4.
    (* omega *)
    eapply le_trans with (m:=n0).
    exact H4.
    exact H1.
    specialize (X0 H env H0 n1 H2 s1).
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

Lemma ExpSoundness_BindS : forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv tenv' : valTC) (x : StaticSemL.Id)
    (e1 e2 : Exp) (t1 t2 : VTyp) (m : option VTyp) 
    (m0 : Maybe t1 m) (e : tenv' = (x, t1) :: tenv)
    (e0 : ExpTyping ftenv tenv e1 t1),
  ExpSoundness_def fenv D n ftenv tenv e1 t1 e0 ->
  forall e3 : ExpTyping ftenv tenv' e2 t2,
  ExpSoundness_def fenv D n ftenv tenv' e2 t2 e3 ->
  ExpSoundness_def fenv D n ftenv tenv (BindS x m e1 e2) t2
    (BindS_Typing ftenv tenv tenv' x e1 e2 t1 t2 m m0 e e0 e3).
    unfold ExpSoundness_def, SoundExp.
    intros.
    specialize (X H env H0 n0 H1 s).
    destruct X as [v1 k1 X]. 
    destruct X as [w1 H2].
    destruct w1 as [s1 n1].
    simpl in H2.
    set (X3:= updateEnvLemma valueVTyp env tenv x v1 t1 H0 k1).
    inversion e; subst.
    specialize (X0 H ((x,v1)::env) X3 n1). (* s1 *)
    assert (n1 <= n) as K2.
    eapply ExpDecrease in H2.
    (* omega *)
    eapply le_trans with (m:=n0).
    exact H2.
    exact H1.
    specialize (X0 K2 s1).
    destruct X0 as [v2 k3 X0].
    destruct X0 as [w2 H4].
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


Lemma ExpSoundness_BindMS : forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv tenv0 tenv1 : valTC) 
    (env0 : valEnv) (e : Exp) (t : VTyp) (e0 : EnvTyping env0 tenv0)
    (e1 : tenv1 = tenv0 ++ tenv) (e2 : ExpTyping ftenv tenv1 e t),
  ExpSoundness_def fenv D n ftenv tenv1 e t e2 ->
  ExpSoundness_def fenv D n ftenv tenv (BindMS env0 e) t
             (BindMS_Typing ftenv tenv tenv0 tenv1 env0 e t e0 e1 e2).
    unfold ExpSoundness_def, SoundExp.
    intros.
    inversion e1; subst.
    eapply (overrideEnvLemma valueVTyp env0 env tenv0 tenv e0) in H0.
    specialize (X H (env0 ++ env) H0 n0 H1 s).
    destruct X as [v1 k1 X].
    destruct X as [w1 H4].
    destruct w1 as [s1 n1].
    simpl in *.
    constructor 1 with (x:=v1).
    assumption.
    constructor 1 with (x:=(s1,n1)).
    simpl.
    eapply BindMS_FStep.
    eassumption. 
Defined.

Lemma ExpSoundness_IfThenElse : forall
    (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv : valTC) (e1 e2 e3 : Exp) 
    (t : VTyp) (e : ExpTyping ftenv tenv e1 Bool),
  ExpSoundness_def fenv D n ftenv tenv e1 Bool e ->
  forall e0 : ExpTyping ftenv tenv e2 t,
  ExpSoundness_def fenv D n ftenv tenv e2 t e0 ->
  forall e4 : ExpTyping ftenv tenv e3 t,
  ExpSoundness_def fenv D n ftenv tenv e3 t e4 ->
  ExpSoundness_def fenv D n ftenv tenv (IfThenElse e1 e2 e3) t
    (IfThenElse_Typing ftenv tenv e1 e2 e3 t e e0 e4).
    unfold ExpSoundness_def, SoundExp.
    intros.
    specialize (X H env H0 n0 H1 s).
    destruct X as [v1 k1 X].
    destruct X as [w1 H4].
    destruct w1 as [s1 n1].
    simpl in *.
    destruct v1.
    destruct v; unfold sVTyp in v.
    inversion k1; subst.
    simpl in *.
    inversion H2; subst.
    simpl in v.
    destruct v.
    + specialize (X0 H env H0 n1). (* s1 *)
      assert (n1 <= n) as K.
      eapply ExpDecrease in H4.
      (* omega. *)
      eapply le_trans.
      exact H4.
      exact H1.
      specialize (X0 K s1).
      destruct X0 as [v2 k3 X0].
      destruct X0 as [w2 H5].
      destruct w2 as [s2 n2].
      simpl in *.
      constructor 1 with (x:=v2).
      assumption.
      constructor 1 with (x:=(s2,n2)).
      simpl in *.
      eapply IfThenElse_FStep1.
      eassumption.
      assumption.
    + specialize (X1 H env H0 n1).
      assert (n1 <= n) as K.
      eapply ExpDecrease in H4.
      (* omega. *)
      eapply le_trans.
      exact H4.
      exact H1.
      specialize (X1 K s1).      
      destruct X1 as [v2 k3 X1].
      destruct X1 as [w2 H5].
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


Lemma ExpSoundness_Modify :
  forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
         (ftenv : funTC) (tenv : valTC) (t1 t2 : VTyp) 
    (XF : XFun t1 t2) (e : Exp) (e0 : ExpTyping ftenv tenv e t1),
  ExpSoundness_def fenv D n ftenv tenv e t1 e0 ->
  ExpSoundness_def fenv D n ftenv tenv (Modify t1 t2 XF e) t2
    (Modify_Typing ftenv tenv t1 t2 XF e e0).
    unfold ExpSoundness_def, SoundExp.
    intros.
    rename H into X0.
    rename H0 into X1.
    rename H1 into H.    
    specialize (X X0 env X1 n0 H s).
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

(**********************************************************************)

Lemma ExpSoundness_PrmsNil : forall 
    (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv : valTC),
    PrmsSoundness_def fenv D n 
                      ftenv tenv (PS []) (PT []) (PSNil_Typing ftenv tenv).
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
  forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
         (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp) 
    (es : list Exp) (ts : list VTyp) (e0 : ExpTyping ftenv tenv e t),
  ExpSoundness_def fenv D n ftenv tenv e t e0 ->
  forall p : PrmsTyping ftenv tenv (PS es) (PT ts),
  PrmsSoundness_def fenv D n ftenv tenv (PS es) (PT ts) p ->
  PrmsSoundness_def fenv D n ftenv tenv (PS (e :: es)) (PT (t :: ts))
                    (PSCons_Typing ftenv tenv e t es ts e0 p).
    unfold PrmsSoundness_def, SoundPrms.
    unfold ExpSoundness_def, SoundExp.
    intros.
    rename H into X1.
    rename H0 into X2.
    rename H1 into H.    
    specialize (X X1 env X2 n0 H s).
    destruct X as [v1 k1 X].
    destruct X as [w X].
    destruct w as [s1 n1].
    simpl in *.
    assert (n1 <= n0).
    eapply ExpDecrease in X.
    assumption.
    assert (n1 <= n).
    (* omega. *)
    eapply le_trans.
    exact H0.
    exact H.
    specialize (X0 X1 env X2 n1 H1 s1).
    destruct X0 as [es0 X0].
    destruct X0 as [vs k2 X0].
    destruct X0 as [k3 X0].
    destruct X0 as [w k4].
    destruct w as [s2 n2].
    econstructor 1 with (x:= (Val v1)::es0).
    econstructor 1 with (x:= v1::vs).
    unfold isValueList2T.
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


(******************************************************************)

Lemma ExpSoundness_Apply0 (fenv: funEnv) (D: FEnvWT fenv) :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (e : Exp) (ps : Prms) (pt : PTyp) (t : VTyp) (p : Pure e)
    (i : IdFTyping ftenv x (FT pt t)) (p0 : PrmsTyping ftenv tenv ps pt),
  PrmsSoundness_def fenv D 0 ftenv tenv ps pt p0 ->
  forall e0 : ExpTyping ftenv tenv e Nat,
  ExpSoundness_def fenv D 0 ftenv tenv e Nat e0 ->
  ExpSoundness_def fenv D 0 ftenv tenv (Apply x ps e) t
                   (Apply_Typing ftenv tenv x e ps pt t p i p0 e0).
    unfold ExpSoundness_def, SoundExp, PrmsSoundness_def, SoundPrms.
    intros.
    specialize (X0 H env H0 n H1 s).
    destruct X0 as [v1 k1 X0].
    destruct X0 as [w X0].
    destruct w as [s1 n1].
    simpl in *.
    generalize X0.
    intro X3.
    eapply (Pure_sideffect _ _ _ _ _ _ _ _ p) in X0.
    destruct X0.
    inversion H2; subst.
    
    specialize (X H env H0 n1 H1 s1).
    destruct X as [es X].
    destruct X as [vs k2 X].
    destruct X as [k3 X].
    destruct X as [w2 H6].
    destruct w2 as [s2 n2].
    simpl in *.
    inversion k2; subst.
    eapply VTyping_lemma in k1.
    destruct k1 as [n0 k1].
    cbv in n0.
    (* unfold sVTyp in n0; unfold Nat in n0; simpl in n0. *)
    inversion i; subst.
    unfold FEnvTyping in H.
    eapply ExtRelVal2 with (f:=funFTyp) (venv:=fenv) in H3.
    destruct H3 as [f H3 H5].
    remember (min n2 n0) as n3.

    assert (funArity f = length vs) as H7.
    {+ destruct pt.
       eapply PrmsArity_lemma in k3.
       destruct f.
       inversion H5; subst.
       unfold funArity.
       rewrite map_length in k3.
       rewrite map_length in k3.
       symmetry.
       exact k3.
    }
    
    eapply (Apply_FStep0 fenv env s1 s2 n1 n2 n0 x e
                         (cst Nat n0) _ vs f ps X3) in H6.
    instantiate (1:=fun0Exp f) in H6.
    
    econstructor 1 with (x:=fun0Exp f).

    eapply FunTyping0_lemma.
    reflexivity.
    unfold funFTyp in H5.
    unfold funVTyp.
    destruct f.
    inversion H5; subst.
    reflexivity.

    econstructor 1 with (x:= (s2,n2)).
    simpl.
    exact H6.
    assumption.
    reflexivity.
    reflexivity.
    assert (n1 = 0) as H8.
    omega.
    assert (n2 <= n1) as H9.
    eapply PrmsDecrease in H6.
    assumption.
    omega.
    assumption.
    assumption.
Defined.
    
Lemma ExpSoundness_Call0 (fenv: funEnv) (D: FEnvWT fenv) :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  PrmsSoundness_def fenv D 0 ftenv tenv (PS ls) pt p ->
  ExpSoundness_def fenv D 0 ftenv tenv (Call x (PS ls)) t
                   (Call_Typing ftenv tenv x ls pt t i p).
    unfold ExpSoundness_def, SoundExp, PrmsSoundness_def, SoundPrms.
    intros.
    rename H into X0.
    rename H0 into X1.
    rename H1 into H.
    specialize (X X0 env X1 n H s).
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
    
    eapply Call_FStep01 with (x:=x) (v:=fun0Exp f) in H4.
   
    econstructor 1 with (x:=fun0Exp f).

    eapply FunTyping0_lemma.
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


(********************************************************************)

Lemma ExpSoundness_CallX_aux4
  (fenv : funEnv)
  (n : nat)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (m : VTyping v (projT1 v))
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (vs : list Value)
  (n2 : nat)
  (s2 : W)
  (IHn : {v0 : Value & VTyping v0 (projT1 v) &
        {x : W * nat &
        EClosure fenv (mkVEnv tenv0 vs) (Conf Exp s2 n2 e)
          (Conf Exp (fst x) (snd x) (Val v0))}})
  (ls : list Exp)
  (p : PrmsTyping ftenv tenv (PS ls) (PT (map snd tenv0)))
  (env : valEnv)
  (n0 : nat)
  (s : W)
  (k3 : PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) 
         (PS (map Val vs)) (PT (map snd tenv0)))
  (k2 : isValueList2T (map Val vs) vs)
  (H4 : PClosure fenv env (Conf Prms s n0 (PS ls))
         (Conf Prms s2 (S n2) (PS (map Val vs))))
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (H1 : n0 <= S n)
  (H5 : funArity (FC tenv0 v e) = length vs)
  (H6 : EnvTyping (mkVEnv (funValTC (FC tenv0 v e)) vs) tenv0)
  (q2 : n2 <= n) :
  {v0 : Value & VTyping v0 (projT1 v) &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s n0 (Call x (PS ls)))
    (Conf Exp (fst x0) (snd x0) (Val v0))}}.    
(**)    
    destruct IHn as [v3 HH1 HH2].    

    econstructor 1 with (x:=v3).
    exact HH1.

    destruct HH2 as [w3 HH2].
    econstructor 1 with (x:=w3).
    destruct w3 as [s3 n3].

    eapply Call_FStepS with (v3:=v3) (s3:=s3) (n3:=n3).
    eassumption.
    eassumption.
    
    Focus 2.    
    eapply H4.

    eapply BindMS_FStep.
    eapply EClosWeakenA1 with (env':=env).
    exact HH2.
Defined.    


Lemma ExpSoundness_CallX_aux4_0
  (fenv : funEnv)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (m : VTyping v (projT1 v))
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (ls : list Exp)
  (p : PrmsTyping ftenv tenv (PS ls) (PT (map snd tenv0)))
  (env : valEnv)
  (n0 : nat)
  (s : W)
  (vs : list Value)
  (k3 : PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) 
         (PS (map Val vs)) (PT (map snd tenv0)))
  (k2 : isValueList2T (map Val vs) vs)
  (s2 : W)
  (H4 : PClosure fenv env (Conf Prms s n0 (PS ls))
         (Conf Prms s2 0 (PS (map Val vs))))
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (H5 : funArity (FC tenv0 v e) = length vs) :
  {v0 : Value & VTyping v0 (projT1 v) &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s n0 (Call x (PS ls)))
    (Conf Exp (fst x0) (snd x0) (Val v0))}}.  
    eapply Call_FStep01 with (x:=x) (v:=v) in H4.
   
    econstructor 1 with (x:=v).
    
    eapply FunTyping0_lemma with (f:= FC tenv0 v e).
    reflexivity.
    symmetry.
    eapply funFTyp_lemma.
    unfold funFTyp.
    reflexivity.
    
    econstructor 1 with (x:= (s2,0)).
    simpl.
    exact H4.
    eassumption.
    reflexivity.
    assumption. 
    reflexivity.
Defined.


Lemma ExpSoundness_CallX_aux3
  (fenv : funEnv)
  (n : nat)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (t : VTyp)
  (m : VTyping v t)
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (IHn : FEnvTyping fenv ftenv ->
        forall env : valEnv,
        EnvTyping env tenv0 ->
        forall n0 : nat,
        n0 <= n ->
        forall s : W,
        {v : Value & VTyping v t &
        {x : W * nat &
             EClosure fenv env (Conf Exp s n0 e)
                      (Conf Exp (fst x) (snd x) (Val v))}})
  (ls : list Exp)
  (pt : PTyp)
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (env : valEnv)
  (n0 : nat)
  (s : W)
  (vs : list Value)
  (k3 : PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) (PS (map Val vs)) pt)
  (k2 : isValueList2T (map Val vs) vs)
  (s2 : W)
  (n2 : nat)
  (H4 : PClosure fenv env (Conf Prms s n0 (PS ls))
          (Conf Prms s2 n2 (PS (map Val vs))))
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (H1 : n0 <= S n)
  (i3 : funFTyp (FC tenv0 v e) = FT pt t) : 
  {v0 : Value & VTyping v0 t &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s n0 (Call x (PS ls)))
    (Conf Exp (fst x0) (snd x0) (Val v0))}}.   
Proof. 
    simpl in i3.
    inversion i3; subst.
    clear i3.
    
    set (f:=FC tenv0 v e).
    set (t:= projT1 v).
    set (pt:=PT (map snd tenv0)).
    set (ft:=FT pt t).
    
    assert (funArity f = length vs) as H5.
    {+ eapply PrmsArity_lemma in k3.
       rewrite map_length in k3.
       rewrite map_length in k3.
       symmetry.
       exact k3.
    }

    destruct n2.
(* case 0 *)
    eapply (ExpSoundness_CallX_aux4_0 fenv ftenv tenv tenv0 x v e m
           i2 ls p env n0 s vs k3 k2 s2 H4 H H0 H5).  
(* case S *)
    assert (EnvTyping (mkVEnv (funValTC f) vs) tenv0) as H6.
    eapply mkVEnv_typing_lemma1.
    reflexivity.
    exact k3.

    assert (S n2 <= S n) as q02.
    eapply PrmsDecrease in H4.
    eapply le_trans.
    exact H4.
    exact H1.
    assert (n2 <= n) as q2.
    eapply (le_inject _ _ q02).

(**)
    subst t.
    subst f.

    specialize (IHn H (mkVEnv tenv0 vs)).

    specialize (IHn H6 n2).
         
    specialize (IHn q2 s2).
    eapply (ExpSoundness_CallX_aux4 fenv n ftenv tenv tenv0 x v e m
           i2 vs n2 s2 IHn ls p env n0 s k3 k2 H4 H H0 H1 H5 H6 q2).
Defined.


Lemma ExpSoundness_CallX_aux2
  (fenv : funEnv)
  (n : nat)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (t : VTyp)
  (m : VTyping v t)
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (IHn : FEnvTyping fenv ftenv ->
        forall env : valEnv,
        EnvTyping env tenv0 ->
        forall n0 : nat,
        n0 <= n ->
        forall s : W,
        {v : Value & VTyping v t &
        {x : W * nat &
             EClosure fenv env (Conf Exp s n0 e)
                      (Conf Exp (fst x) (snd x) (Val v))}})
  (ls : list Exp)
  (pt : PTyp)
  (i1 : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (env : valEnv)
  (n0 : nat)
  (s : W)
  (es : list Exp)
  (vs : list Value)
  (k2 : isValueList2T es vs)
  (k3 : PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) (PS es) pt)
  (s2 : W)
  (n2 : nat)
  (H4 : PClosure fenv env (Conf Prms s n0 (PS ls))
         (Conf Prms s2 n2 (PS es)))
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (H1 : n0 <= S n) : 
  {v0 : Value & VTyping v0 t &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s n0 (Call x (PS ls)))
    (Conf Exp (fst x0) (snd x0) (Val v0))}}.   
    simpl in *.
    
    set (f:=FC tenv0 v e).
    set (ft:=FT pt t).
    inversion k2; subst.
    unfold VTyping in m.

    generalize i1.
    intro i3.

    eapply (RelatedByEnv funFTyp fenv ftenv x f ft H i2) in i3.
    eapply (ExpSoundness_CallX_aux3 fenv n ftenv tenv tenv0
              x v e t m i2 IHn ls pt p env n0 s vs k3 k2 s2 n2 H4
           H H0 H1 i3).
Defined.


Lemma ExpSoundness_CallX_aux1 
  (fenv : funEnv)
  (n : nat)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (t : VTyp)
  (m : VTyping v t)
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (IHn : FEnvTyping fenv ftenv ->
        forall env : valEnv,
        EnvTyping env tenv0 ->
        forall n0 : nat,
        n0 <= n ->
        forall s : W,
        {v : Value & VTyping v t &
        {x : W * nat &
             EClosure fenv env (Conf Exp s n0 e)
                      (Conf Exp (fst x) (snd x) (Val v))}})
  (ls : list Exp)
  (pt : PTyp)
  (i1 : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (env : valEnv)
  (n0 : nat)
  (s : W)
  (X : {es : list Exp &
      {x : list Value & isValueList2T es x &
      PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) (PS es) pt *
      {x : W * nat &
      PClosure fenv env (Conf Prms s n0 (PS ls))
        (Conf Prms (fst x) (snd x) (PS es))}}})
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (H1 : n0 <= S n) :
  {v0 : Value & VTyping v0 t &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s n0 (Call x (PS ls)))
    (Conf Exp (fst x0) (snd x0) (Val v0))}}.    
    destruct X as [es X].
    destruct X as [vs k2 X].
    destruct X as [k3 X].
    destruct X as [w2 H4].
    destruct w2 as [s2 n2].
    eapply (ExpSoundness_CallX_aux2 fenv n ftenv tenv tenv0 x v e t m
                                    i2 IHn ls pt i1 p env n0 s es vs
                                    k2 k3 s2 n2 H4 H H0 H1). 
Defined.                                    


Lemma ExpSoundness_CallX : forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
    (v: Value) (e: Exp)
    (t : VTyp) (m: VTyping v t)
    (i2 : findE fenv x = Some (FC tenv0 v e))     
    (IHn : FEnvTyping fenv ftenv ->
        forall (env : valEnv),        
        EnvTyping env tenv0 ->
        forall (n0 : nat), n0 <= n -> forall (s : W),
            SoundExp fenv env e t s n0) 
    (ls : list Exp) (pt : PTyp) (i1 : IdFTyping ftenv x (FT pt t))
      (p : PrmsTyping ftenv tenv (PS ls) pt),
    PrmsSoundness_def fenv D (S n) ftenv tenv (PS ls) pt p ->
    ExpSoundness_def fenv D (S n) ftenv tenv (Call x (PS ls)) t
                           (Call_Typing ftenv tenv x ls pt t i1 p).
    unfold ExpSoundness_def, SoundExp, PrmsSoundness_def, SoundPrms.
    intros.
    specialize (X H env H0 n0 H1 s).
    eapply (ExpSoundness_CallX_aux1 fenv n ftenv tenv tenv0 x v e t m
                               i2 IHn ls pt i1 p env n0 s X H H0 H1).
Defined.

(**********************************************************************)

Lemma ExpSoundness_CallX0_aux2 (fenv : funEnv)
  (D : FEnvWT fenv)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (t : VTyp)
  (m : valueVTyp v = t)
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (ls : list Exp)
  (pt : PTyp)
  (i1 : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (env : valEnv)
  (s : W)
  (vs : list Value)
  (k3 : PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) (PS (map Val vs)) pt)
  (k2 : isValueList2T (map Val vs) vs)
  (s2 : W)
  (n2 : nat)
  (H4 : PClosure fenv env (Conf Prms s 0 (PS ls))
         (Conf Prms s2 n2 (PS (map Val vs))))
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (n : nat)
  (H1 : n <= 0)
  (i3 : funFTyp (FC tenv0 v e) = FT pt t) :
  {v0 : Value & VTyping v0 t &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s n (Call x (PS ls)))
    (Conf Exp (fst x0) (snd x0) (Val v0))}}.
    
    set (f := FC tenv0 v e).
    set (ft := FT pt t).

    simpl in i3.
    inversion i3; subst.
    clear i3.
    clear H5.
    
    set (t:= projT1 v).
    set (pt:=PT (map snd tenv0)).

    assert (funArity f = length vs) as H5.
    {+ eapply PrmsArity_lemma in k3.
       rewrite map_length in k3.
       rewrite map_length in k3.
       symmetry.
       exact k3.
    }

    assert (n2 <= 0) as qq1.
    eapply PrmsDecrease in H4.
    exact H4.

    assert (n2 = 0) as qq2.
    eapply (min_zero n2).
    exact qq1.

    inversion qq2; subst.
    subst t.

    assert (n = 0) as qq3.
    eapply (min_zero n).
    exact H1.

    inversion qq3; subst.
    
    eapply (ExpSoundness_CallX_aux4_0 fenv ftenv tenv tenv0 x v e eq_refl
           i2 ls p env 0 s vs k3 k2 s2 H4 H H0 H5).  
Defined.


Lemma ExpSoundness_CallX0_aux1 (fenv : funEnv)
  (D : FEnvWT fenv)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (t : VTyp)
  (m : VTyping v t)
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (ls : list Exp)
  (pt : PTyp)
  (i1 : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (env : valEnv)
  (s : W)
  (X : {es : list Exp &
      {x : list Value & isValueList2T es x &
      PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) (PS es) pt *
      {x : W * nat &
      PClosure fenv env (Conf Prms s 0 (PS ls))
        (Conf Prms (fst x) (snd x) (PS es))}}})
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (n : nat)
  (H1 : n <= 0)
  :
  {v0 : Value & VTyping v0 t &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s n (Call x (PS ls)))
    (Conf Exp (fst x0) (snd x0) (Val v0))}}.
    
    destruct X as [es X].
    destruct X as [vs k2 X].
    destruct X as [k3 X].
    destruct X as [w2 H4].
    destruct w2 as [s2 n2].
    
    simpl in *.
    
    set (f:=FC tenv0 v e).
    set (ft:=FT pt t).
    inversion k2; subst.
    unfold VTyping in m.

    generalize i1.
    intro i3.

    eapply (RelatedByEnv funFTyp fenv ftenv x f ft H i2) in i3.

    eapply (ExpSoundness_CallX0_aux2 fenv D ftenv tenv tenv0 x v e t m
           i2 ls pt i1 p env s vs k3 k2 s2 n2 H4 H H0 n H1 i3).
Defined.


Lemma ExpSoundness_CallX0 : forall (fenv: funEnv) (D: FEnvWT fenv) 
    (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
    (v: Value) (e: Exp)
    (t : VTyp) (m: VTyping v t)
    (i2 : findE fenv x = Some (FC tenv0 v e))     
    (ls : list Exp) (pt : PTyp) (i1 : IdFTyping ftenv x (FT pt t))
      (p : PrmsTyping ftenv tenv (PS ls) pt),
    PrmsSoundness_def fenv D 0 ftenv tenv (PS ls) pt p ->
    ExpSoundness_def fenv D 0 ftenv tenv (Call x (PS ls)) t
                           (Call_Typing ftenv tenv x ls pt t i1 p).
    unfold ExpSoundness_def, SoundExp, PrmsSoundness_def, SoundPrms.
    intros.

    assert (0 <= 0) as q0.
    auto.
    
    specialize (X H env H0 0 q0 s).

    eapply (ExpSoundness_CallX0_aux1 fenv D ftenv tenv tenv0
                                     x v e t m i2 ls pt i1 p env s
                                     X H H0 n H1).
Defined.

(*********************************************************************)

Lemma Convert_Soundness_Call (fenv: funEnv) (D: FEnvWT fenv) (n: nat) :
  (forall (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
    (v: Value) (e: Exp)
    (t : VTyp) (m: VTyping v t)
    (i2 : findE fenv x = Some (FC tenv0 v e))     
    (IHn : FEnvTyping fenv ftenv ->
        forall (env : valEnv),        
        EnvTyping env tenv0 ->
        forall (n0 : nat), n0 <= n -> forall (s : W),
            SoundExp fenv env e t s n0) 
    (ls : list Exp) (pt : PTyp) (i1 : IdFTyping ftenv x (FT pt t))
      (p : PrmsTyping ftenv tenv (PS ls) pt),
    PrmsSoundness_def fenv D (S n) ftenv tenv (PS ls) pt p ->
    ExpSoundness_def fenv D (S n) ftenv tenv (Call x (PS ls)) t
                     (Call_Typing ftenv tenv x ls pt t i1 p)) ->
   (forall (IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
        ExpTyping ftenv tenv e t ->
        FEnvTyping fenv ftenv ->
        forall (env : valEnv),        
        EnvTyping env tenv ->
        forall (n0 : nat), n0 <= n -> forall (s : W),
            SoundExp fenv env e t s n0), 
 forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
      (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
      (p : PrmsTyping ftenv tenv (PS ls) pt),
    PrmsSoundness_def fenv D (S n) ftenv tenv (PS ls) pt p ->
    ExpSoundness_def fenv D (S n) ftenv tenv (Call x (PS ls)) t
    (Call_Typing ftenv tenv x ls pt t i p)).
  intros.
  generalize i.
  intro i2.
  unfold IdFTyping in i.
  unfold EnvrAssign in i.

  unfold ExpSoundness_def.
  intros.
  
  eapply ExtRelVal2 with (f:=funFTyp) (venv:=fenv) in i.
  destruct i as [f m d].
  Focus 2.
  assumption.
  
  generalize D.
  intro D1.
  unfold FEnvWT in D1.
  specialize (D1 ftenv H x f m).
  unfold FunWT in D1.
   
  destruct f.
  simpl in d.
  inversion d; subst.
  set (t:= projT1 v).

  assert ((forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
        ExpTyping ftenv tenv e t ->
        FEnvTyping fenv ftenv ->
        forall env : valEnv,
        EnvTyping env tenv ->
        forall n0 : nat, n0 <= n -> forall s : W, SoundExp fenv env e t s n0)
          ->
        (FEnvTyping fenv ftenv ->
       forall env : valEnv,
       EnvTyping env tenv0 ->
       forall n0 : nat, n0 <= n -> forall s : W, SoundExp fenv env e t s n0))
  as IHc.

  intros.
  subst t.
  specialize (X1 ftenv tenv0 e (projT1 v) D1 H2 env0 H3 n1 H4 s0).
  exact X1.
  
  specialize (X ftenv tenv tenv0 x v e (projT1 v) eq_refl m (IHc IHn) 
                ls (PT (map snd tenv0)) i2 p X0). 

  eapply X.
  assumption.
  assumption.
  assumption.
Defined.  
    

Lemma Convert_Soundness_Call0 (fenv: funEnv) (D: FEnvWT fenv) :
 (forall (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
    (v: Value) (e: Exp)
    (t : VTyp) (m: VTyping v t)
    (i2 : findE fenv x = Some (FC tenv0 v e))     
    (ls : list Exp) (pt : PTyp) (i1 : IdFTyping ftenv x (FT pt t))
      (p : PrmsTyping ftenv tenv (PS ls) pt),
    PrmsSoundness_def fenv D 0 ftenv tenv (PS ls) pt p ->
    ExpSoundness_def fenv D 0 ftenv tenv (Call x (PS ls)) t
                     (Call_Typing ftenv tenv x ls pt t i1 p)) ->
    (forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  PrmsSoundness_def fenv D 0 ftenv tenv (PS ls) pt p ->
  ExpSoundness_def fenv D 0 ftenv tenv (Call x (PS ls)) t
                   (Call_Typing ftenv tenv x ls pt t i p)).
  intros.

  generalize i.
  intro i2.
  unfold IdFTyping in i.
  unfold EnvrAssign in i.

  unfold ExpSoundness_def.
  intros.
  
  eapply ExtRelVal2 with (f:=funFTyp) (venv:=fenv) in i.
  destruct i as [f m d].
  Focus 2.
  assumption.
  
  generalize D.
  intro D1.
  unfold FEnvWT in D1.
  specialize (D1 ftenv H x f m).
  unfold FunWT in D1.
   
  destruct f.
  simpl in d.
  inversion d; subst.
  set (t:= projT1 v).

  specialize (X ftenv tenv tenv0 x v e (projT1 v) eq_refl m  
                ls (PT (map snd tenv0)) i2 p X0). 

  eapply X.
  assumption.
  assumption.
  assumption.
Defined.  
    

(*************************************************************************)

Lemma ExpSoundness_Apply : forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
(IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
        ExpTyping ftenv tenv e t ->
        FEnvTyping fenv ftenv ->
        forall (env : valEnv),
        EnvTyping env tenv ->
        forall (n0 : nat), n0 <= n -> forall (s : W),
            SoundExp fenv env e t s n0),      
 forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (e : Exp) (ps : Prms) (pt : PTyp) (t : VTyp) (p : Pure e)
    (i : IdFTyping ftenv x (FT pt t)) (p0 : PrmsTyping ftenv tenv ps pt),
  PrmsSoundness_def fenv D (S n) ftenv tenv ps pt p0 ->
  forall e0 : ExpTyping ftenv tenv e Nat,
  ExpSoundness_def fenv D (S n) ftenv tenv e Nat e0 ->
  ExpSoundness_def fenv D (S n) ftenv tenv (Apply x ps e) t
    (Apply_Typing ftenv tenv x e ps pt t p i p0 e0).
Proof.
    unfold ExpSoundness_def, SoundExp, PrmsSoundness_def, SoundPrms.
    intros.
    rename H into X1.
    rename H0 into X2.
    rename H1 into H.  
    specialize (X0 X1 env X2 n0 H s).
    destruct X0 as [v1 k1 X0].
    destruct X0 as [w X0].
    destruct w as [s1 n1].
    simpl in *.
    generalize X0.
    intro X3.
    eapply (Pure_sideffect _ _ _ _ _ _ _ _ p) in X0.
    destruct X0.
    inversion H0; subst.
    
    specialize (X X1 env X2 n1 H s1).
    destruct X as [es X].
    destruct X as [vs k2 X].
    destruct X as [k3 X].
    destruct X as [w2 H4].
    destruct w2 as [s2 n2].
    simpl in *.
    inversion k2; subst.

    inversion i; subst.
    (* unfold FEnvTyping in X1. *)
    eapply ExtRelVal2 with (f:=funFTyp) (venv:=fenv) in H1.
    destruct H1 as [f H0 H3].

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
    eapply mkVEnv_typing_lemma1.
    eassumption.
    eassumption.
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
    
    specialize (IHn X X1 env X2).
    specialize (IHn (min n2 n0)).
    assert (S n2 <= n1) as H1.
    eapply PrmsDecrease in H4.
    assumption.
    assert (n2 <= n) as H6.
    omega.
    assert ((min n2 n0) <= n2) as H7.
    eapply min_idem1.
    assert ((min n2 n0) <= n) as H8.
    omega.
    
    specialize (IHn H8 s2).

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


(**********************************************************************)

Lemma ExpSoundness_ApplyX_aux4_0
  (fenv : funEnv)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (m : VTyping v (projT1 v))
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (e9 : Exp)
  (ls : list Exp)
  (p : PrmsTyping ftenv tenv (PS ls) (PT (map snd tenv0)))
  (env : valEnv)
  (s9 : W)
  (n9 : nat)
  (vs : list Value)
  (k3 : PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) 
         (PS (map Val vs)) (PT (map snd tenv0)))
  (k2 : isValueList2T (map Val vs) vs)
  (s2 : W)
  (n2 : nat)
  (H40 : PClosure fenv env (Conf Prms s9 n9 (PS ls))
          (Conf Prms s2 n2 (PS (map Val vs))))
  (m9 : ExpTyping ftenv tenv e9 Nat)
  (n10 : nat)
  
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (X3 : EClosure fenv env (Conf Exp s9 n9 e9)
         (Conf Exp s9 n9
            (Val
               (existT ValueI (VT nat (CInt I32 Unsigned))
                  (Cst (VT nat (CInt I32 Unsigned)) n10)))))
  (H50 : funArity (FC tenv0 v e) = length vs)
  (Heqn11 : 0 = Init.Nat.min n2 n10)
  :
  {v0 : Value & VTyping v0 (projT1 v) &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s9 n9 (Apply x (PS ls) e9))
    (Conf Exp (fst x0) (snd x0) (Val v0))}}.
   
    eapply Apply_FStep01 with (x:=x) (v:=v) (e:=e9) in H40.
    
    econstructor 1 with (x:=v).
    
    eapply FunTyping0_lemma with (f:= FC tenv0 v e).
    reflexivity.
    symmetry.
    eapply funFTyp_lemma.
    unfold funFTyp.
    reflexivity.
    
    econstructor 1 with (x:= (s2,0)).
    simpl.
    exact H40.
    eassumption.
    eassumption.
    reflexivity.
    reflexivity.
    assumption.
    assumption.
Defined.


Lemma ExpSoundness_ApplyX_aux4_1
  (fenv : funEnv)
  (n : nat)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (m : VTyping v (projT1 v))
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (vs : list Value)
  (n11 : nat)
  (s2 : W)
  (IHn : {v0 : Value & VTyping v0 (projT1 v) &
        {x : W * nat &
        EClosure fenv (mkVEnv tenv0 vs) (Conf Exp s2 n11 e)
          (Conf Exp (fst x) (snd x) (Val v0))}})
  (e9 : Exp)
  (ls : list Exp)  
  (p : PrmsTyping ftenv tenv (PS ls) (PT (map snd tenv0)))
  (env : valEnv)
  (s9 : W)
  (n9 : nat)
  (k3 : PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) 
         (PS (map Val vs)) (PT (map snd tenv0)))
  (k2 : isValueList2T (map Val vs) vs)
  (n2 : nat)
  (H40 : PClosure fenv env (Conf Prms s9 n9 (PS ls))
          (Conf Prms s2 n2 (PS (map Val vs))))
  (m9 : ExpTyping ftenv tenv e9 Nat)
  (n10 : nat)
  (k9 : VTyping
         (existT ValueI (VT nat (CInt I32 Unsigned))
            (Cst (VT nat (CInt I32 Unsigned)) n10)) Nat)
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (H1 : n9 <= S n)
  (X3 : EClosure fenv env (Conf Exp s9 n9 e9)
         (Conf Exp s9 n9
            (Val
               (existT ValueI (VT nat (CInt I32 Unsigned))
                  (Cst (VT nat (CInt I32 Unsigned)) n10)))))
  (H50 : funArity (FC tenv0 v e) = length vs)
  (Heqn11 : S n11 = Init.Nat.min n2 n10)
  (H6 : EnvTyping (mkVEnv (funValTC (FC tenv0 v e)) vs) tenv0)
  (q02a : n2 <= S n)
  (q02b : S n11 <= n2)
  (q02 : S n11 <= S n)
  (q2 : n11 <= n)
  :
  {v0 : Value & VTyping v0 (projT1 v) &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s9 n9 (Apply x (PS ls) e9))
    (Conf Exp (fst x0) (snd x0) (Val v0))}}.
  
    destruct IHn as [v3 HH1 HH2].    

    econstructor 1 with (x:=v3).
    exact HH1.

    destruct HH2 as [w3 HH2].
    econstructor 1 with (x:=w3).
    destruct w3 as [s3 n3].

    simpl.
    simpl in HH2.
    eapply EClosConcat.
    eapply Apply_FStep.
    exact X3.
    exact H40.
    reflexivity.
    exact Heqn11.
    eassumption.

    destruct n2.
    assert (False).
    intuition.
    inversion H2.    
    
    eapply Call_FStepS1 with (v3:=v3) (s3:=s3) (n3:=n3).
    eassumption.
    eassumption.
     
    Focus 2.
    assumption.

    eapply BindMS_FStep.
    eapply EClosWeakenA1 with (env':=env).
    exact HH2.
Defined.    


Lemma ExpSoundness_ApplyX_aux4
  (fenv : funEnv)
  (n : nat)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (m : VTyping v (projT1 v))
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (IHn : FEnvTyping fenv ftenv ->
        forall env : valEnv,
        EnvTyping env tenv0 ->
        forall n0 : nat,
        n0 <= n ->
        forall s : W,
        {v0 : Value & VTyping v0 (projT1 v) &
        {x : W * nat &
        EClosure fenv env (Conf Exp s n0 e)
          (Conf Exp (fst x) (snd x) (Val v0))}})
  (e9 : Exp)
  (ls : list Exp)
  (p : PrmsTyping ftenv tenv (PS ls) (PT (map snd tenv0)))
  (env : valEnv)
  (s9 : W)
  (n9 : nat)
  (vs : list Value)
  (k3 : PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) 
         (PS (map Val vs)) (PT (map snd tenv0)))
  (k2 : isValueList2T (map Val vs) vs)
  (s2 : W)
  (n2 : nat)
  (H40 : PClosure fenv env (Conf Prms s9 n9 (PS ls))
          (Conf Prms s2 n2 (PS (map Val vs))))
  (m9 : ExpTyping ftenv tenv e9 Nat)
  (n10 : nat)
  (k9 : VTyping
         (existT ValueI (VT nat (CInt I32 Unsigned))
            (Cst (VT nat (CInt I32 Unsigned)) n10)) Nat)
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (H1 : n9 <= S n)
  (X3 : EClosure fenv env (Conf Exp s9 n9 e9)
         (Conf Exp s9 n9
            (Val
               (existT ValueI (VT nat (CInt I32 Unsigned))
                  (Cst (VT nat (CInt I32 Unsigned)) n10)))))
  (H50 : funArity (FC tenv0 v e) = length vs)
  (n11 : nat)
  (Heqn11 : S n11 = Init.Nat.min n2 n10)
  :
  {v0 : Value & VTyping v0 (projT1 v) &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s9 n9 (Apply x (PS ls) e9))
    (Conf Exp (fst x0) (snd x0) (Val v0))}}.
  
  set (f := FC tenv0 v e).
  set (t := projT1 v).
  set (pt := PT (map snd tenv0)).
  set (ft := FT pt t).
   
    assert (EnvTyping (mkVEnv (funValTC f) vs) tenv0) as H6.
    eapply mkVEnv_typing_lemma1.
    reflexivity.
    exact k3.

    assert (n2 <= S n) as q02a.
    eapply PrmsDecrease in H40.    
    eapply le_trans.
    exact H40.
    exact H1.
    assert (S n11 <= n2) as q02b.
    rewrite Heqn11.
    intuition.
    assert (S n11 <= S n) as q02.
    eapply le_trans.
    exact q02b.
    exact q02a.
    
    assert (n11 <= n) as q2.
    eapply (le_inject _ _ q02).
    
(**)
    subst t.
    subst f.

    specialize (IHn H (mkVEnv tenv0 vs)).

    specialize (IHn H6 n11).
         
    specialize (IHn q2 s2).
    
    eapply (ExpSoundness_ApplyX_aux4_1 fenv n ftenv tenv tenv0 x v e m
                    i2 vs n11 s2 IHn e9 ls p env s9 n9 k3 k2 n2 H40
                    m9 n10 k9 H H0 H1 X3 H50 Heqn11 H6 q02a q02b q02 q2).
Defined.


Lemma ExpSoundness_ApplyX_aux3
  (fenv : funEnv)
  (n : nat)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (t : VTyp)
  (m : VTyping v t)
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (IHn : FEnvTyping fenv ftenv ->
        forall env : valEnv,
        EnvTyping env tenv0 ->
        forall n0 : nat,
        n0 <= n ->
        forall s : W,
        {v : Value & VTyping v t &
        {x : W * nat &
             EClosure fenv env (Conf Exp s n0 e)
                      (Conf Exp (fst x) (snd x) (Val v))}})
  (e9 : Exp)
  (ls : list Exp)
  (pt : PTyp)
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (env : valEnv)
  (s9: W)
  (n9 : nat)
  (vs : list Value)
  (k3 : PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) (PS (map Val vs)) pt)
  (k2 : isValueList2T (map Val vs) vs)
  (s2 : W)
  (n2 : nat)
  (H40 : PClosure fenv env (Conf Prms s9 n9 (PS ls))
          (Conf Prms s2 n2 (PS (map Val vs))))
  (m9 : ExpTyping ftenv tenv e9 Nat)
  (v9 : Value)
  (k9 : VTyping v9 Nat)
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (H1 : n9 <= S n)
  (X3 : EClosure fenv env (Conf Exp s9 n9 e9) (Conf Exp s9 n9 (Val v9)))
  (i3 : funFTyp (FC tenv0 v e) = FT pt t) :
  {v0 : Value & VTyping v0 t &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s9 n9 (Apply x (PS ls) e9))
    (Conf Exp (fst x0) (snd x0) (Val v0))}}.
    
    simpl in i3.
    inversion i3; subst.
    clear i3.

    set (f:=FC tenv0 v e). 
    set (t:= projT1 v).
    set (pt:=PT (map snd tenv0)). 
    set (ft:=FT pt t). 
    
    assert (funArity f = length vs) as H50.
    {+ eapply PrmsArity_lemma in k3.
       rewrite map_length in k3.
       rewrite map_length in k3.
       symmetry.
       exact k3.
    }

    destruct v9 as [t10 n10].
    inversion k9; subst.
    unfold Nat in H2.
    unfold valueVTyp in H2.
    simpl in H2.
    inversion H2; subst.
    destruct n10 as [n10].
    simpl in n10.

    remember (min n2 n10) as n11.
    clear H3.
    
    destruct n11.

(* case 0 *)

    eapply (ExpSoundness_ApplyX_aux4_0 fenv ftenv tenv tenv0 x v e m
              i2 e9 ls p env s9 n9 vs k3 k2 s2 n2 H40 m9 n10 H H0 X3
                                       H50 Heqn11). 
 
(* case S *)    

    eapply (ExpSoundness_ApplyX_aux4 fenv n ftenv tenv tenv0 x v e m
              i2 IHn e9 ls p env s9 n9 vs k3 k2 s2 n2 H40 m9 n10
                                    k9 H H0 H1 X3 H50 n11 Heqn11).
Defined.
    

Lemma ExpSoundness_ApplyX_aux2
  (fenv : funEnv)
  (n : nat)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (t : VTyp)
  (m : VTyping v t)
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (IHn : FEnvTyping fenv ftenv ->
        forall env : valEnv,
        EnvTyping env tenv0 ->
        forall n0 : nat,
        n0 <= n ->
        forall s : W,
        {v : Value & VTyping v t &
        {x : W * nat &
             EClosure fenv env (Conf Exp s n0 e)
                      (Conf Exp (fst x) (snd x) (Val v))}})
  (e9 : Exp)
  (ls : list Exp)
  (pt : PTyp)
  (p9: Pure e9)
  (i1 : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (env : valEnv)
  (s9: W)
  (n9 : nat)
  (es : list Exp)
  (vs : list Value)
  (k2 : isValueList2T es vs)
  (k3 : PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) (PS es) pt)
  (s2 : W)
  (n2 : nat)
  (H40 : PClosure fenv env (Conf Prms s9 n9 (PS ls))
          (Conf Prms (fst (s2, n2)) (snd (s2, n2)) (PS es)))
  (m9 : ExpTyping ftenv tenv e9 Nat)
  (v9 : Value)
  (k9 : VTyping v9 Nat)
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (H1 : n9 <= S n)
  (X3 : EClosure fenv env (Conf Exp s9 n9 e9) (Conf Exp s9 n9 (Val v9)))
  :
  {v0 : Value & VTyping v0 t &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s9 n9 (Apply x (PS ls) e9))
    (Conf Exp (fst x0) (snd x0) (Val v0))}}.

    simpl in *.
    
    set (f:=FC tenv0 v e).
    set (ft:=FT pt t).
    inversion k2; subst.
    unfold VTyping in m.

    generalize i1.
    intro i3.

    eapply (RelatedByEnv funFTyp fenv ftenv x f ft H i2) in i3.

    eapply (ExpSoundness_ApplyX_aux3 fenv n ftenv tenv tenv0 x v e t m
                     i2 IHn e9 ls pt p env s9 n9 vs k3 k2 s2 n2 H40
                                     m9 v9 k9 H H0 H1 X3 i3).
Defined.
 

Lemma ExpSoundness_ApplyX_aux1 
  (fenv : funEnv)
  (n : nat)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (t : VTyp)
  (m : VTyping v t)
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (IHn : FEnvTyping fenv ftenv ->
        forall env : valEnv,
        EnvTyping env tenv0 ->
        forall n0 : nat,
        n0 <= n ->
        forall s : W,
        {v : Value & VTyping v t &
        {x : W * nat &
             EClosure fenv env (Conf Exp s n0 e)
                      (Conf Exp (fst x) (snd x) (Val v))}})
  (e9 : Exp)
  (ls : list Exp)
  (pt : PTyp)
  (p9: Pure e9)
  (i1 : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (env : valEnv)
  (s9: W)
  (n9 : nat)
  (X : {es : list Exp &
      {x : list Value & isValueList2T es x &
      PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) (PS es) pt *
      {x0 : W * nat &
      PClosure fenv env (Conf Prms s9 n9 (PS ls))
               (Conf Prms (fst x0) (snd x0) (PS es))}}})
  (m9 : ExpTyping ftenv tenv e9 Nat)
  (v9 : Value)
  (k9 : VTyping v9 Nat)
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (H1 : n9 <= S n)
  (X3 : EClosure fenv env (Conf Exp s9 n9 e9) (Conf Exp s9 n9 (Val v9)))
  :
   {v0 : Value & VTyping v0 t &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s9 n9 (Apply x (PS ls) e9))
    (Conf Exp (fst x0) (snd x0) (Val v0))}}.  

    destruct X as [es X].
    destruct X as [vs k2 X].
    destruct X as [k3 X].
    destruct X as [w2 H40].
    destruct w2 as [s2 n2].

    eapply (ExpSoundness_ApplyX_aux2 fenv n ftenv tenv tenv0 x v e t m
                     i2 IHn e9 ls pt p9 i1 p env s9 n9 es vs k2 k3 s2 n2 H40
                                     m9 v9 k9 H H0 H1 X3).
Defined.
 

Lemma ExpSoundness_ApplyX_aux0 
  (fenv : funEnv)
  (n : nat)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (t : VTyp)
  (m : VTyping v t)
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (IHn : FEnvTyping fenv ftenv ->
        forall env : valEnv,
        EnvTyping env tenv0 ->
        forall n0 : nat,
        n0 <= n ->
        forall s : W,
        {v : Value & VTyping v t &
        {x : W * nat &
             EClosure fenv env (Conf Exp s n0 e)
                      (Conf Exp (fst x) (snd x) (Val v))}})
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
      n0 <= S n ->
      forall s : W,
      {es : list Exp &
      {x : list Value & isValueList2T es x &
      PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) (PS es) pt *
      {x : W * nat &
      PClosure fenv env (Conf Prms s n0 (PS ls))
        (Conf Prms (fst x) (snd x) (PS es))}}}) (**)
  (m9 : ExpTyping ftenv tenv e9 Nat) (**)
  (env : valEnv)
  (n0 : nat)
  (s : W)
  (X0 : {v : Value & VTyping v Nat &
       {x : W * nat &
            EClosure fenv env (Conf Exp s n0 e9)
                     (Conf Exp (fst x) (snd x) (Val v))}}) (**)
  (H : FEnvTyping fenv ftenv)
  (H0 : EnvTyping env tenv)
  (H1 : n0 <= S n) :
  {v0 : Value & VTyping v0 t &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s n0 (Apply x (PS ls) e9))
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
    
    specialize (X H env H0 n9 H1 s9).
    clear H4.

    eapply (ExpSoundness_ApplyX_aux1 fenv n ftenv tenv tenv0 x v e t m
                   i2 IHn e9 ls pt p9 i1 p env s9 n9 X m9 v9 k9 H H0 H1 X3).
Defined.
    

      
Lemma ExpSoundness_ApplyX : forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
    (v: Value) (e: Exp)
    (t : VTyp) (m: VTyping v t)
    (i2 : findE fenv x = Some (FC tenv0 v e))     
    (IHn : FEnvTyping fenv ftenv ->
        forall (env : valEnv),        
        EnvTyping env tenv0 ->
        forall (n0 : nat), n0 <= n -> forall (s : W),
            SoundExp fenv env e t s n0)      
    (e9 : Exp) (ls : list Exp) (pt : PTyp) (p9 : Pure e9)
    (i1 : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),  
  PrmsSoundness_def fenv D (S n) ftenv tenv (PS ls) pt p ->
  forall m9 : ExpTyping ftenv tenv e9 Nat,
  ExpSoundness_def fenv D (S n) ftenv tenv e9 Nat m9 ->
  ExpSoundness_def fenv D (S n) ftenv tenv (Apply x (PS ls) e9) t
                   (Apply_Typing ftenv tenv x e9 (PS ls) pt t p9 i1 p m9).
    unfold ExpSoundness_def, SoundExp, PrmsSoundness_def, SoundPrms.
    intros.
    specialize (X0 H env H0 n0 H1 s).

    eapply (ExpSoundness_ApplyX_aux0 fenv n ftenv tenv tenv0 x v e t m
                   i2 IHn e9 ls pt p9 i1 p X m9 env n0 s X0 H H0 H1).
Defined.


(**********************************************************************)

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
               (existT ValueI (VT nat (CInt I32 Unsigned))
                  (Cst (VT nat (CInt I32 Unsigned)) n10)))))
  (i3 : funFTyp (FC tenv0 v e) = FT pt t)
  (n : nat)
  (H1 : n <= 0)
  :
  {v0 : Value & VTyping v0 t &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s9 n (Apply x (PS ls) e9))
    (Conf Exp (fst x0) (snd x0) (Val v0))}}.

    set (v9 := Val
               (existT ValueI (VT nat (CInt I32 Unsigned))
                  (Cst (VT nat (CInt I32 Unsigned)) n10))).
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


(********************* main ***********************************************)

Lemma ExpSoundnessA :
  forall (fenv: funEnv) (D: FEnvWT fenv) (n9: nat) 
         (ftenv: funTC) (tenv: valTC)
          (e: Exp) (t: VTyp), 
          ExpTyping ftenv tenv e t ->  
          FEnvTyping fenv ftenv ->
          forall (env: valEnv),
                 EnvTyping env tenv ->
                 forall (n: nat), n <= n9 -> forall (s: W), 
                   SoundExp fenv env e t s n.
Proof.
  intros fenv D n.
  induction n.
  eapply (TSoundness_ExpTyping_mut fenv D 0).
  - eapply (ExpSoundness_Val fenv D 0).
  - eapply (ExpSoundness_Var fenv D 0).
  - eapply (ExpSoundness_BindN fenv D 0).
  - eapply (ExpSoundness_BindS fenv D 0).
  - eapply (ExpSoundness_BindMS fenv D 0).
  - eapply (ExpSoundness_IfThenElse fenv D 0).
  - eapply (ExpSoundness_Apply0 fenv D). 
  - eapply (Convert_Soundness_Call0 fenv D (ExpSoundness_CallX0 fenv D)).
  - eapply (ExpSoundness_Modify fenv D 0).
  - eapply (ExpSoundness_PrmsNil fenv D 0).
  - eapply (ExpSoundness_PrmsCons fenv D 0).   
  - eapply (TSoundness_ExpTyping_mut fenv D (S n)).
    + eapply (ExpSoundness_Val fenv D (S n)).
    + eapply (ExpSoundness_Var fenv D (S n)).
    + eapply (ExpSoundness_BindN fenv D (S n)).
    + eapply (ExpSoundness_BindS fenv D (S n)).
    + eapply (ExpSoundness_BindMS fenv D (S n)).
    + eapply (ExpSoundness_IfThenElse fenv D (S n)).
    + eapply (ExpSoundness_Apply fenv D).
      auto.
    + eapply (Convert_Soundness_Call fenv D n (ExpSoundness_CallX fenv D n)).
      auto.
    + eapply (ExpSoundness_Modify fenv D (S n)).
    + eapply (ExpSoundness_PrmsNil fenv D (S n)).   
    + eapply (ExpSoundness_PrmsCons fenv D (S n)).
Defined.      


Lemma PrmsSoundness_Apply : forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat) 
    (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (e : Exp) (ps : Prms) (pt : PTyp) (t : VTyp) (p : Pure e)
    (i : IdFTyping ftenv x (FT pt t)) (p0 : PrmsTyping ftenv tenv ps pt),
  PrmsSoundness_def fenv D (S n) ftenv tenv ps pt p0 ->
  forall e0 : ExpTyping ftenv tenv e Nat,
  ExpSoundness_def fenv D (S n) ftenv tenv e Nat e0 ->
  ExpSoundness_def fenv D (S n) ftenv tenv (Apply x ps e) t
    (Apply_Typing ftenv tenv x e ps pt t p i p0 e0).
  unfold ExpSoundness_def.
  intros.
  eapply ExpSoundnessA with (ftenv:=ftenv) (tenv:=tenv).
  exact D.
  econstructor.
  assumption.
  eassumption.
  assumption.
  assumption.
  assumption.
  assumption.
  eassumption.
Defined.

Lemma PrmsSoundness_Call : forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat) 
    (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  PrmsSoundness_def fenv D (S n) ftenv tenv (PS ls) pt p ->
  ExpSoundness_def fenv D (S n) ftenv tenv (Call x (PS ls)) t
    (Call_Typing ftenv tenv x ls pt t i p).
  unfold ExpSoundness_def.
  intros. 
  eapply ExpSoundnessA with (ftenv:=ftenv) (tenv:=tenv).
  exact D.
  econstructor.
  eassumption.
  assumption.
  assumption.
  assumption.
  eassumption.
Defined.


Lemma PrmsSoundnessA :
  forall (fenv: funEnv) (D: FEnvWT fenv) (n9: nat)
         (ftenv: funTC) (tenv: valTC)
          (ps: Prms) (pt: PTyp), 
          PrmsTyping ftenv tenv ps pt ->   
          FEnvTyping fenv ftenv ->
          forall (env: valEnv),
                 EnvTyping env tenv ->
                 forall (n: nat), n <= n9 -> forall (s: W),
                   SoundPrms fenv env ps pt s n.
Proof.
  intros fenv D n.
  induction n.
  eapply (TSoundness_PrmsTyping_mut fenv D 0).
  - eapply (ExpSoundness_Val fenv D 0).
  - eapply (ExpSoundness_Var fenv D 0).
  - eapply (ExpSoundness_BindN fenv D 0).
  - eapply (ExpSoundness_BindS fenv D 0).
  - eapply (ExpSoundness_BindMS fenv D 0).
  - eapply (ExpSoundness_IfThenElse fenv D 0).
  - eapply (ExpSoundness_Apply0 fenv D). 
  - eapply (Convert_Soundness_Call0 fenv D (ExpSoundness_CallX0 fenv D)).
  - eapply (ExpSoundness_Modify fenv D 0).
  - eapply (ExpSoundness_PrmsNil fenv D 0).
  - eapply (ExpSoundness_PrmsCons fenv D 0).   
  - eapply (TSoundness_PrmsTyping_mut fenv D (S n)).
    + eapply (ExpSoundness_Val fenv D (S n)).
    + eapply (ExpSoundness_Var fenv D (S n)).
    + eapply (ExpSoundness_BindN fenv D (S n)).
    + eapply (ExpSoundness_BindS fenv D (S n)).
    + eapply (ExpSoundness_BindMS fenv D (S n)).
    + eapply (ExpSoundness_IfThenElse fenv D (S n)).
    + eapply (PrmsSoundness_Apply fenv D).
    + eapply (PrmsSoundness_Call fenv D).
    + eapply (ExpSoundness_Modify fenv D (S n)).
    + eapply (ExpSoundness_PrmsNil fenv D (S n)).   
    + eapply (ExpSoundness_PrmsCons fenv D (S n)). 
Defined.      


Lemma ExpSoundness :
   forall (fenv: funEnv) (D: FEnvWT fenv) (ftenv: funTC) (tenv: valTC)
          (e: Exp) (t: VTyp), 
          ExpTyping ftenv tenv e t -> 
          FEnvTyping fenv ftenv ->
          forall (env: valEnv),
                 EnvTyping env tenv ->
                 forall (s: W) (n: nat), 
                   SoundExp fenv env e t s n.
Proof.
  intros.
  eapply (ExpSoundnessA fenv D n).
  eassumption.
  assumption.
  assumption.
  auto.
Defined.  

Lemma PrmsSoundness :
   forall (fenv: funEnv) (D: FEnvWT fenv) (ftenv: funTC) (tenv: valTC)
          (ps: Prms) (pt: PTyp), 
          PrmsTyping ftenv tenv ps pt ->  
          FEnvTyping fenv ftenv ->
          forall (env: valEnv),
                 EnvTyping env tenv ->
                 forall (s: W) (n: nat),
                   SoundPrms fenv env ps pt s n.
Proof.
  intros.
  eapply (PrmsSoundnessA fenv D n).
  eassumption.
  assumption.
  assumption.
  auto.
Defined.  

Program Definition ExpEvalSOS (s: W) (n: nat) (fenv: funEnv)        
           (k1: FEnvWT fenv)
           (env: valEnv) (e: Exp) (t: VTyp) 
  (k2: ExpTyping (funEnv2funTC fenv) (valEnv2valTC env) e t) :
  SoundExp fenv env e t s n :=
  ExpSoundness fenv k1 (funEnv2funTC fenv) (valEnv2valTC env) e t k2
               _ env _ s n.
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
  PrmsSoundness fenv k1 (funEnv2funTC fenv) (valEnv2valTC env) ps pt k2
                _ env _ s n. 
Next Obligation.
  constructor.
Defined.
Next Obligation.
  constructor.    
Defined.

Obligation Tactic := idtac. 

Program Fixpoint ExpSoundnessB 
        (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
        (ftenv: funTC) (tenv: valTC)
          (e: Exp) (t: VTyp) 
          (k: ExpTyping ftenv tenv e t) :  
            FEnvTyping fenv ftenv ->
            forall (env: valEnv),
                 EnvTyping env tenv ->
                 forall (n0: nat), n0 <= n -> forall (s: W),
                   SoundExp fenv env e t s n0 := _
with PrmsSoundnessB  
       (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
       (ftenv: funTC) (tenv: valTC)
          (ps: Prms) (pt: PTyp) 
          (k: PrmsTyping ftenv tenv ps pt) :  
            FEnvTyping fenv ftenv ->
            forall (env: valEnv),
                 EnvTyping env tenv ->
                 forall (n0: nat), n0 <= n -> forall (s: W), 
                   SoundPrms fenv env ps pt s n0 := _.

Next Obligation.
  intros fenv D n.
  induction n.
  eapply (TSoundness_ExpTyping_mut fenv D 0).
  - eapply (ExpSoundness_Val fenv D 0).
  - eapply (ExpSoundness_Var fenv D 0).
  - eapply (ExpSoundness_BindN fenv D 0).
  - eapply (ExpSoundness_BindS fenv D 0).
  - eapply (ExpSoundness_BindMS fenv D 0).
  - eapply (ExpSoundness_IfThenElse fenv D 0).
  - eapply (ExpSoundness_Apply0 fenv D). 
  - eapply (Convert_Soundness_Call0 fenv D (ExpSoundness_CallX0 fenv D)).
  - eapply (ExpSoundness_Modify fenv D 0).
  - eapply (ExpSoundness_PrmsNil fenv D 0).
  - eapply (ExpSoundness_PrmsCons fenv D 0).
  - eapply (TSoundness_ExpTyping_mut fenv D (S n)).
    + eapply (ExpSoundness_Val fenv D (S n)).
    + eapply (ExpSoundness_Var fenv D (S n)).
    + eapply (ExpSoundness_BindN fenv D (S n)).
    + eapply (ExpSoundness_BindS fenv D (S n)).
    + eapply (ExpSoundness_BindMS fenv D (S n)).
    + eapply (ExpSoundness_IfThenElse fenv D (S n)).
    + eapply (ExpSoundness_Apply fenv D).
      auto.
    + eapply (Convert_Soundness_Call fenv D n (ExpSoundness_CallX fenv D n)).
      auto.
    + eapply (ExpSoundness_Modify fenv D (S n)).
    + eapply (ExpSoundness_PrmsNil fenv D (S n)).   
    + eapply (ExpSoundness_PrmsCons fenv D (S n)).
Defined.      

Next Obligation.
  intros fenv D n.
  induction n.
  eapply (TSoundness_PrmsTyping_mut fenv D 0).
  - eapply (ExpSoundness_Val fenv D 0).
  - eapply (ExpSoundness_Var fenv D 0).
  - eapply (ExpSoundness_BindN fenv D 0).
  - eapply (ExpSoundness_BindS fenv D 0).
  - eapply (ExpSoundness_BindMS fenv D 0).
  - eapply (ExpSoundness_IfThenElse fenv D 0).
  - eapply (ExpSoundness_Apply0 fenv D). 
  - eapply (Convert_Soundness_Call0 fenv D (ExpSoundness_CallX0 fenv D)).
  - eapply (ExpSoundness_Modify fenv D 0).
  - eapply (ExpSoundness_PrmsNil fenv D 0).
  - eapply (ExpSoundness_PrmsCons fenv D 0).   
  - eapply (TSoundness_PrmsTyping_mut fenv D (S n)).
    + eapply (ExpSoundness_Val fenv D (S n)).
    + eapply (ExpSoundness_Var fenv D (S n)).
    + eapply (ExpSoundness_BindN fenv D (S n)).
    + eapply (ExpSoundness_BindS fenv D (S n)).
    + eapply (ExpSoundness_BindMS fenv D (S n)).
    + eapply (ExpSoundness_IfThenElse fenv D (S n)).
    + eapply (PrmsSoundness_Apply fenv D).
    + eapply (PrmsSoundness_Call fenv D).
    + eapply (ExpSoundness_Modify fenv D (S n)).
    + eapply (ExpSoundness_PrmsNil fenv D (S n)).   
    + eapply (ExpSoundness_PrmsCons fenv D (S n)). 
Defined.      
  

(**********************************************************************)
(**********************************************************************)

(* not used *)

Lemma ExpSoundness_Call_old : forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
        ExpTyping ftenv tenv e t ->
        FEnvTyping fenv ftenv ->
        forall (env : valEnv),        
        EnvTyping env tenv ->
        forall (n0 : nat), n0 <= n -> forall (s : W),
            SoundExp fenv env e t s n0), 
 forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
      (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
      (p : PrmsTyping ftenv tenv (PS ls) pt),
    PrmsSoundness_def fenv D (S n) ftenv tenv (PS ls) pt p ->
    ExpSoundness_def fenv D (S n) ftenv tenv (Call x (PS ls)) t
    (Call_Typing ftenv tenv x ls pt t i p).
    unfold ExpSoundness_def, SoundExp, PrmsSoundness_def, SoundPrms.
    intros.
    rename H into X0.
    rename H0 into X1.
    rename H1 into H.    
    specialize (X X0 env X1 n0 H s).
    destruct X as [es X].
    destruct X as [vs k2 X].
    destruct X as [k3 X].
    destruct X as [w2 H4].
    destruct w2 as [s2 n2].
    simpl in *.
    inversion k2; subst.

    inversion i; subst.
    unfold FEnvTyping in X0.
    eapply ExtRelVal2 with (f:=funFTyp) (venv:=fenv) in H1.
    destruct H1 as [f H0 H3].

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
    eapply mkVEnv_typing_lemma1.
    eassumption.
    eassumption.
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
    
    specialize (IHn X X0 env X1 n2). (* s2 *)
    assert (S n2 <= n0) as H1.
    eapply PrmsDecrease in H4.
    assumption.
    assert (n2 <= n) as H6.
    omega.
    specialize (IHn H6 s2).

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


Lemma ExpSoundness_Call_X_old : forall
  (fenv : funEnv) (k:  FEnvWT fenv) (n : nat)
  (IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
        ExpTyping ftenv tenv e t ->
        FEnvTyping fenv ftenv ->
        forall (env : valEnv),
        EnvTyping env tenv ->
        forall (n0 : nat),
        n0 <= n -> forall (s : W),
        {v : Value & VTyping v t &
        {x : W * nat &
    EClosure fenv env (Conf Exp s n0 e) (Conf Exp (fst x) (snd x) (Val v))}})
  (ftenv : funTC)
  (tenv : valTC)
  (x : Id)
  (ls : list Exp)
  (pt : PTyp)
  (t : VTyp)
  (i : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (X : FEnvTyping fenv ftenv ->
      forall (env : valEnv),
      EnvTyping env tenv ->
      forall (n0 : nat),  
      n0 <= S n -> forall (s : W),
      {es : list Exp &
      {x : list Value & isValueList2T es x &
      PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) (PS es) pt *
      {x : W * nat &
      PClosure fenv env (Conf Prms s n0 (PS ls))
        (Conf Prms (fst x) (snd x) (PS es))}}})
  (env : valEnv)
  (X0 : FEnvTyping fenv ftenv)
  (X1 : EnvTyping env tenv)
  (s : W)
  (n0 : nat)
  (H : n0 <= n),
  {v : Value & VTyping v t &
  {x0 : W * nat &
  EClosure fenv env (Conf Exp s (S n0) (Call x (PS ls)))
    (Conf Exp (fst x0) (snd x0) (Val v))}}.
  intros.
  eapply ExpSoundness_Call_old.
  exact IHn.
  exact i.
  eassumption.
  assumption.
  assumption.
  omega.
  Unshelve.
  assumption.
  assumption.
Defined.  


      
Lemma ExpSoundness_ApplyXXX : forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
    (v: Value) (e: Exp)
    (t : VTyp) (m: VTyping v t)
    (i2 : findE fenv x = Some (FC tenv0 v e))     
    (IHn : FEnvTyping fenv ftenv ->
        forall (env : valEnv),        
        EnvTyping env tenv0 ->
        forall (n0 : nat), n0 <= n -> forall (s : W),
            SoundExp fenv env e t s n0)      
    (e9 : Exp) (ls : list Exp) (pt : PTyp) (p9 : Pure e9)
    (i1 : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),  
  PrmsSoundness_def fenv D (S n) ftenv tenv (PS ls) pt p ->
  forall m9 : ExpTyping ftenv tenv e9 Nat,
  ExpSoundness_def fenv D (S n) ftenv tenv e9 Nat m9 ->
  ExpSoundness_def fenv D (S n) ftenv tenv (Apply x (PS ls) e9) t
                   (Apply_Typing ftenv tenv x e9 (PS ls) pt t p9 i1 p m9).
    unfold ExpSoundness_def, SoundExp, PrmsSoundness_def, SoundPrms.
    intros.
    specialize (X0 H env H0 n0 H1 s).
    destruct X0 as [v9 k9 X0].
    destruct X0 as [w X0].
    destruct w as [s9 n9].
    simpl in *.
    generalize X0.
    intro X3.
    eapply (Pure_sideffect _ _ _ _ _ _ _ _ p9) in X0.
    destruct X0 as [H2 H3].
    inversion H2; subst.

    specialize (X H env H0 n9 H1 s9).
    destruct X as [es X].
    destruct X as [vs k2 X].
    destruct X as [k3 X].
    destruct X as [w2 H40].
    destruct w2 as [s2 n2].

    simpl in *.
    
    set (f:=FC tenv0 v e).
    set (ft:=FT pt t).
    inversion k2; subst.
    unfold VTyping in m.

    generalize i1.
    intro i3.

    eapply (RelatedByEnv funFTyp fenv ftenv x f ft H i2) in i3.

    simpl in i3.
    inversion i3; subst.
    clear i3.

    set (t:= projT1 v).
    
    assert (funArity f = length vs) as H50.
    {+ eapply PrmsArity_lemma in k3.
       rewrite map_length in k3.
       rewrite map_length in k3.
       symmetry.
       exact k3.
    }

    destruct v9 as [t10 n10].
    inversion k9; subst.
    unfold Nat in H2.
    unfold valueVTyp in H2.
    simpl in H2.
    inversion H2; subst.
    destruct n10 as [n10].
    simpl in n10.

    remember (min n2 n10) as n11.
    clear H3.
    
    destruct n11.

    eapply Apply_FStep01 with (x:=x) (v:=v) (e:=e9) in H40.
    
    econstructor 1 with (x:=v).
    
    eapply FunTyping0_lemma with (f:= FC tenv0 v e).
    reflexivity.
    symmetry.
    eapply funFTyp_lemma.
    unfold funFTyp.
    reflexivity.
    
    econstructor 1 with (x:= (s2,0)).
    simpl.
    exact H40.
    eassumption.
    eassumption.
    reflexivity.
    reflexivity.
    assumption.
    assumption.
    
    assert (EnvTyping (mkVEnv (funValTC f) vs) tenv0) as H6.
    eapply mkVEnv_typing_lemma1.
    reflexivity.
    exact k3.

    assert (n2 <= S n) as q02a.
    eapply PrmsDecrease in H40.    
    eapply le_trans.
    exact H40.
    exact H1.
    assert (S n11 <= n2) as q02b.
    rewrite Heqn11.
    intuition.
    assert (S n11 <= S n) as q02.
    eapply le_trans.
    exact q02b.
    exact q02a.
    
    assert (n11 <= n) as q2.
    eapply (le_inject _ _ q02).
    
(**)
    subst t.
    subst f.

    specialize (IHn H (mkVEnv tenv0 vs)).

    specialize (IHn H6 n11).
         
    specialize (IHn q2 s2).

    destruct IHn as [v3 HH1 HH2].    

    econstructor 1 with (x:=v3).
    exact HH1.

    destruct HH2 as [w3 HH2].
    econstructor 1 with (x:=w3).
    destruct w3 as [s3 n3].

    simpl.
    simpl in HH2.
    eapply EClosConcat.
    eapply Apply_FStep.
    exact X3.
    exact H40.
    reflexivity.
    exact Heqn11.
    eassumption.

    destruct n2.
    assert (False).
    intuition.
    inversion H2.    
    
    eapply Call_FStepS1 with (v3:=v3) (s3:=s3) (n3:=n3).
    eassumption.
    eassumption.
     
    Focus 2.
    assumption.

    eapply BindMS_FStep.
    eapply EClosWeakenA1 with (env':=env).
    exact HH2.
Defined.    


End TSoundness.

