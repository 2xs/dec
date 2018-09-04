(*  DEC 2.0 language specification.
   Paolo Torrini, 
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
Require Import WeakenI1.
Require Import UniqueTypI1.

Import ListNotations.


(** * DEC 2.0 language specification *)

(** Derived dynamic rules *)

Module DerivDyn (IdT: ModTyp) <: ModTyp.

Module UniqueTypL := UniqueTyp IdT.
Export UniqueTypL.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.


(*********************************************************************)

(** big-step lifting of congruence rules *)

Lemma BindN_extended_congruence : 
   forall (fenv: funEnv) (env: valEnv)  
                          (s1 s2: W) (n1 n2: nat) (p1 p2 p3: Exp),
     EClosure fenv env (Conf Exp s1 n1 p1) (Conf Exp s2 n2 p2) ->
     EClosure fenv env (Conf Exp s1 n1 (BindN p1 p3))
                            (Conf Exp s2 n2 (BindN p2 p3)).
Proof.
  intros.
  dependent induction X.
  constructor.
  destruct p5.
  specialize (IHX state s2).
  specialize (IHX fuel n2).
  specialize (IHX qq).
  specialize (IHX p2).
  econstructor.
  - instantiate (1:= Conf Exp state fuel (BindN qq p3)).
    eapply BindN_Cg_EStep.
    assumption.
  - apply IHX.
    reflexivity.
    reflexivity.
Defined.    


Lemma BindMS_extended_congruence :
        forall (fenv: funEnv) (env envL env': valEnv)
                (s1 s2: W) (n1 n2: nat) (e1 e2: Exp),
          env' = envL ++ env -> 
          EClosure fenv env' (Conf Exp s1 n1 e1) (Conf Exp s2 n2 e2) ->
          EClosure fenv env (Conf Exp s1 n1 (BindMS envL e1))
                   (Conf Exp s2 n2 (BindMS envL e2)).
Proof.
  intros.
  dependent induction X.
  constructor.
  destruct p2.
  econstructor.
  - instantiate (1 := Conf Exp state fuel (BindMS envL qq)).  
    econstructor.
    reflexivity.
    assumption.
  - eapply IHX.
    reflexivity.
    reflexivity.
    reflexivity.
Defined.


Lemma BindS_extended_congruence :
   forall (fenv: funEnv) (env: valEnv)
      (s1 s2: W) (n1 n2: nat) (x: Id) (mt: option VTyp) (p1 p2 p3: Exp),
           EClosure fenv env (Conf Exp s1 n1 p1) (Conf Exp s2 n2 p2) ->
           EClosure fenv env (Conf Exp s1 n1 (BindS x mt p1 p3))
                             (Conf Exp s2 n2 (BindS x mt p2 p3)).
Proof.
  intros.
  dependent induction X.
  constructor.
  destruct p5.
  econstructor.
  - econstructor.
    eassumption.
  - eapply IHX.
    reflexivity.
    reflexivity.
Defined.


Lemma Apply1_extended_congruence :
     forall (fenv: funEnv) (env: valEnv)
                           (s s': W) (n n': nat) 
                           (x: Id) (ps ps': Prms) (v: Value),
     PClosure fenv env (Conf Prms s n ps) (Conf Prms s' n' ps') ->
     EClosure fenv env (Conf Exp s n (Apply x ps (Val v)))
                            (Conf Exp s' n' (Apply x ps' (Val v))).
Proof.
  intros.
  dependent induction X.
  constructor.
  destruct p2.
  econstructor.
  - instantiate (1 := Conf Exp state fuel (Apply x qq (Val v))).
    econstructor.
    assumption.
  - specialize (IHX state s' fuel n' qq ps').
    eapply IHX. 
    reflexivity.
    reflexivity.
Defined.


Lemma Apply2_extended_congruence 
      (fenv: funEnv) (env: valEnv) (s s': W) (n n': nat)
      (x: Id) (ps: Prms) (e e': Exp) : 
     EClosure fenv env (Conf Exp s n e) (Conf Exp s' n' e') ->
     EClosure fenv env (Conf Exp s n (Apply x ps e))
                            (Conf Exp s' n' (Apply x ps e')).
Proof.
  intros.
  dependent induction X.
  constructor.
  destruct p2.
  econstructor.
  - instantiate (1:= Conf Exp state fuel (Apply x ps qq)). 
    econstructor.
    eassumption.
  - eapply IHX.
    reflexivity.
    reflexivity.
Defined.  


Lemma IfThenElse_extended_congruence :
     forall (fenv: funEnv) (env: valEnv)
                           (s s': W) (n n': nat) 
                           (e e' e1 e2: Exp),
     EClosure fenv env (Conf Exp s n e) (Conf Exp s' n' e') ->
     EClosure fenv env (Conf Exp s n
                                 (IfThenElse e e1 e2))
                            (Conf Exp s' n'
                                 (IfThenElse e' e1 e2)).
Proof.
  intros. 
  dependent induction X.
  constructor.
  intros.
  destruct p2.
  specialize (IHX state s' fuel n' qq e' eq_refl eq_refl). 
  econstructor.
  - econstructor.
    eassumption.
  - assumption.
Defined.  


Lemma Call_extended_congruence :
     forall (fenv: funEnv) (env: valEnv)
                           (s s': W) (n n': nat) 
                           (x: Id) (ps ps': Prms),
     PClosure fenv env (Conf Prms s n ps) (Conf Prms s' n' ps') ->
     EClosure fenv env (Conf Exp s n (Call x ps))
                            (Conf Exp s' n' (Call x ps')).
Proof.
  intros.
  dependent induction X.
  constructor.
  destruct p2.
  econstructor.
  - instantiate (1 := Conf Exp state fuel (Call x qq)).
    econstructor.
    assumption.
  - specialize (IHX state s' fuel n' qq ps').
    eapply IHX. 
    reflexivity.
    reflexivity.
Defined.


Lemma Modify_extended_congruence :
     forall (fenv: funEnv) (env: valEnv)
            (s s': W) (n n': nat) (t1 t2: VTyp)
            (xf: XFun t1 t2) (e e': Exp),
     EClosure fenv env (Conf Exp s n e) (Conf Exp s' n' e') ->
     EClosure fenv env (Conf Exp s n
                                 (Modify t1 t2 xf e))
                       (Conf Exp s' n'
                                 (Modify t1 t2 xf e')).
Proof.
  intros. 
  dependent induction X.
  constructor.
  destruct p2.
  specialize (IHX state s' fuel n' xf qq e' eq_refl eq_refl). 
  econstructor.
  - econstructor.
    eassumption.
  - assumption.
Defined.  


Lemma Prms_extended_congruence1 :
    forall (fenv: funEnv) (env: valEnv)
                   (s s': W) (n n': nat)
                   (es es': list Exp) (v: Value),
         PClosure fenv env (Conf Prms s n (PS es))
                                   (Conf Prms s' n' (PS es')) ->
         PClosure fenv env (Conf Prms s n (PS (Val v :: es)))
                                   (Conf Prms s' n' (PS (Val v :: es'))).  
Proof.
  intros.
  revert v.
  dependent induction X.
  - intros.
    constructor.
  - intros.
    destruct p2.
    destruct qq. 
    specialize (IHX state s' fuel n' es0 es').
    specialize (IHX eq_refl eq_refl v).
    econstructor.
    econstructor.
    eassumption.
    assumption.
Defined.
  

Lemma Prms_extended_congruence2 :
    forall (fenv: funEnv) (env: valEnv)
           (s s': W) (n n': nat) (es: list Exp) (e e': Exp),
         EClosure fenv env (Conf Exp s n e)
                                (Conf Exp s' n' e') ->
         PClosure fenv env (Conf Prms s n (PS (e::es)))
                           (Conf Prms s' n' (PS (e'::es))).  
  intros.
  revert es.
  dependent induction X.
  - constructor.
  - intros.
    destruct p2.
    specialize (IHX state s' fuel n' qq e').
    specialize (IHX eq_refl eq_refl es).
    econstructor.
    econstructor.
    eassumption.
    assumption.
Defined.  
  

Lemma Prms_extended_congruence3 :
       forall (fenv: funEnv) (env: valEnv)
                   (s s': W) (n n': nat) 
                   (es evs: list Exp) (vs: list Value),
         isValueList2T evs vs ->                             
         PClosure fenv env (Conf Prms s n (PS es))
                                   (Conf Prms s' n' (PS evs)) ->
         PClosure fenv env (Conf Prms s n (PS es))
                                   (Conf Prms s' n' (PS (map Val vs))).  
Proof.
  intros.
  inversion X; subst.
  assumption.
Defined.  


Lemma Prms_extended_congruence4 :
    forall (fenv: funEnv) (env: valEnv)
           (s s' s'': W) (n n' n'': nat)
           (es es': list Exp) (e: Exp) (v: Value),
         EClosure fenv env (Conf Exp s n e)
                                (Conf Exp s' n' (Val v)) ->
         PClosure fenv env (Conf Prms s' n' (PS es))
                                   (Conf Prms s'' n'' (PS es')) ->  
         PClosure fenv env (Conf Prms s n (PS (e::es)))
                                   (Conf Prms s'' n'' (PS (Val v::es'))).  
  intros.
  revert es es' X0.
  revert s'' n''.
  dependent induction X.
  - intros.
    eapply PConcat.
    econstructor.
    eapply Prms_extended_congruence1.
    assumption.
  - intros.
    destruct p2.
    specialize (IHX state s' fuel n' qq v).
    specialize (IHX eq_refl eq_refl s'' n'' es es' X0).
    econstructor.
    econstructor.
    eassumption.
    assumption.
Defined.  

(****************************************************************************)

Lemma BindN_FStep :   
   forall (fenv: funEnv) (env: valEnv)
          (s0 s1 s2: W) (n0 n1 n2: nat)
          (e1 e2: Exp) (v1 v2: Value),
    EClosure fenv env (Conf Exp s0 n0 e1) (Conf Exp s1 n1 (Val v1)) ->
    EClosure fenv env (Conf Exp s1 n1 e2) (Conf Exp s2 n2 (Val v2)) ->
    EClosure fenv env (Conf Exp s0 n0 (BindN e1 e2))
                      (Conf Exp s2 n2 (Val v2)).
  intros.
  eapply (EClosConcat fenv env).
  instantiate (1:=Conf Exp s1 n1 (BindN (Val v1) e2)).
  eapply BindN_extended_congruence.
  assumption.
  econstructor.
  econstructor.
  assumption.
Defined.

Lemma BindS_FStep :   
   forall (fenv: funEnv) (env: valEnv)
          (s0 s1 s2: W) (n0 n1 n2: nat)
          (e1 e2: Exp) (x: Id) (m: option VTyp) (v1 v2: Value),
    EClosure fenv env (Conf Exp s0 n0 e1) (Conf Exp s1 n1 (Val v1)) ->
    EClosure fenv ((x,v1)::env) (Conf Exp s1 n1 e2) (Conf Exp s2 n2 (Val v2)) ->
    EClosure fenv env (Conf Exp s0 n0 (BindS x m e1 e2))
                      (Conf Exp s2 n2 (Val v2)).
  intros.
  eapply (EClosConcat fenv env).
  instantiate (1:=Conf Exp s1 n1 (BindS x m (Val v1) e2)).
  eapply BindS_extended_congruence.
  assumption.
  econstructor.
  econstructor.
  eapply (EClosConcat fenv env).
  instantiate (1:=Conf Exp s2 n2 (BindMS (singleE x v1) (Val v2))).
  eapply BindMS_extended_congruence.
  reflexivity.
  unfold singleE.
  simpl.
  assumption.
  econstructor.
  econstructor.
  econstructor.
Defined.

Lemma BindMS_FStep :   
   forall (fenv: funEnv) (env env0: valEnv)
          (s0 s1: W) (n0 n1: nat)
          (e: Exp) (v: Value),
    EClosure fenv (env0 ++ env) (Conf Exp s0 n0 e) (Conf Exp s1 n1 (Val v)) ->
    EClosure fenv env (Conf Exp s0 n0 (BindMS env0 e))
                      (Conf Exp s1 n1 (Val v)).
  intros.
  eapply (EClosConcat fenv env).
  instantiate (1:=Conf Exp s1 n1 (BindMS env0 (Val v))).
  eapply BindMS_extended_congruence.
  reflexivity.
  assumption.
  econstructor.
  econstructor.
  constructor.
Defined.  

Lemma IfThenElse_FStep1 :   
   forall (fenv: funEnv) (env: valEnv)
          (s0 s1 s2: W) (n0 n1 n2: nat)
          (e1 e2 e3: Exp) (v: Value),
  EClosure fenv env (Conf Exp s0 n0 e1)
         (Conf Exp s1 n1 (Val (existT ValueI Bool (Cst Bool true)))) ->    
  EClosure fenv env (Conf Exp s1 n1 e2) (Conf Exp s2 n2 (Val v)) ->
  EClosure fenv env (Conf Exp s0 n0 (IfThenElse e1 e2 e3))
    (Conf Exp s2 n2 (Val v)).
  intros.
  eapply (EClosConcat fenv env).
  instantiate (1:=Conf Exp s1 n1 (IfThenElse (Val (cst Bool true)) e2 e3)).
  eapply IfThenElse_extended_congruence.
  assumption.
  econstructor.
  econstructor.
  assumption.
Defined.  

Lemma IfThenElse_FStep2 :   
   forall (fenv: funEnv) (env: valEnv)
          (s0 s1 s2: W) (n0 n1 n2: nat)
          (e1 e2 e3: Exp) (v: Value),
  EClosure fenv env (Conf Exp s0 n0 e1)
         (Conf Exp s1 n1 (Val (existT ValueI Bool (Cst Bool false)))) ->    
  EClosure fenv env (Conf Exp s1 n1 e3) (Conf Exp s2 n2 (Val v)) ->
  EClosure fenv env (Conf Exp s0 n0 (IfThenElse e1 e2 e3))
    (Conf Exp s2 n2 (Val v)).
  intros.
  eapply (EClosConcat fenv env).
  instantiate (1:=Conf Exp s1 n1 (IfThenElse (Val (cst Bool false)) e2 e3)).
  eapply IfThenElse_extended_congruence.
  assumption.
  econstructor.
  econstructor.
  assumption.
Defined.  

Lemma Apply_FStep :   
   forall (fenv: funEnv) (env: valEnv)
          (s0 s1: W) (n0 n1 n2 n3: nat) (x: Id)
          (e: Exp) (v: Value) (vs: list Value) (f: Fun) (ps: Prms),
     EClosure fenv env (Conf Exp s0 n0 e) (Conf Exp s0 n0 (Val v)) ->
     PClosure fenv env (Conf Prms s0 n0 ps)
              (Conf Prms s1 n1 (PS (map Val vs))) ->
     v = cst Nat n2 ->
     n3 = min n1 n2 ->
     findE fenv x = Some f ->
     EClosure fenv env (Conf Exp s0 n0 (Apply x ps e))
              (Conf Exp s1 n3 (Call x (PS (map Val vs)))).
  intros.
  eapply (EClosConcat fenv env).
  instantiate (1:=Conf Exp s0 n0 (Apply x ps (Val v))).
  eapply Apply2_extended_congruence.
  eapply EClosWeaken.
  eassumption.
  instantiate (1:=nil).
  rewrite app_nil_r.
  auto.
  instantiate (1:=nil).
  rewrite app_nil_r.
  auto.
  eapply (EClosConcat fenv env).
  instantiate (1:= Conf Exp s1 n1 (Apply x (PS (map Val vs)) (Val v))).
  eapply Apply1_extended_congruence.
  assumption.
  eapply StepIsEClos.
  econstructor.
  exact f.
  exact H.
  unfold isValueListT.
  eapply forallValues.
  assumption.
Defined.  

Lemma Call_FStep0 :   
   forall (fenv: funEnv) (env: valEnv)
          (s: W) (n: nat) (x: Id)
          (v: Value) (vs: list Value) (f: Fun),
     findE fenv x = Some f ->
     v = fun0Exp f ->
     funArity f = length vs ->
     n = 0 ->
     EClosure fenv env (Conf Exp s n (Call x (PS (map Val vs))))
                       (Conf Exp s n (Val v)).
  intros.
  eapply StepIsEClos.
  rewrite H2.
  econstructor.
  eassumption.
  econstructor.
  assumption.
  reflexivity.
  assumption.
Defined.  

Lemma Call_FStep01 :   
   forall (fenv: funEnv) (env: valEnv)
          (s0 s1: W) (n0 n1: nat) (x: Id)
          (v: Value) (vs: list Value) (f: Fun) (ps: Prms),
     PClosure fenv env (Conf Prms s0 n0 ps)
              (Conf Prms s1 n1 (PS (map Val vs))) ->
     findE fenv x = Some f ->
     v = fun0Exp f ->
     funArity f = length vs ->
     n1 = 0 ->
     EClosure fenv env (Conf Exp s0 n0 (Call x ps))
                       (Conf Exp s1 n1 (Val v)).
  intros.  
  eapply (EClosConcat fenv env).
  eapply Call_extended_congruence.
  eassumption.
  eapply Call_FStep0.
  eassumption.
  assumption.
  assumption.
  assumption.
Defined.


Lemma Call_FStepS :   
   forall (fenv: funEnv) (env: valEnv)
          (s0 s2 s3: W) (n0 n2 n3: nat) (x: Id)
          (v3: Value) (vs: list Value) (f: Fun) (ls: list Exp),
    findE fenv x = Some f ->
     funArity f = length vs -> 
    EClosure fenv env
         (Conf Exp s2 n2 (BindMS (mkVEnv (funValTC f) vs) (funSExp f)))
         (Conf Exp s3 n3 (Val v3)) ->
    PClosure fenv env (Conf Prms s0 n0 (PS ls))
         (Conf Prms s2 (S n2) (PS (map Val vs))) ->  
    EClosure fenv env (Conf Exp s0 n0 (Call x (PS ls)))
                           (Conf Exp s3 n3 (Val v3)).
Proof.
  intros.
  eapply Call_extended_congruence with (x:=x) in X0.
  eapply EClosConcat.
  exact X0.
  econstructor.
  instantiate (1:= Conf Exp s2 n2
                        (BindMS (mkVEnv (funValTC f) vs) (funSExp f))).
  econstructor.
  econstructor.
  eassumption.
  assumption.
  auto.
  auto.
  assumption.
Defined.  



Lemma Call_FStepS1 :   
   forall (fenv: funEnv) (env: valEnv)
          (s0 s3: W) (n0 n3: nat) (x: Id)
          (v3: Value) (vs: list Value) (f: Fun) (ls: list Exp),
    findE fenv x = Some f ->
     funArity f = length vs -> 
    EClosure fenv env
         (Conf Exp s0 n0 (BindMS (mkVEnv (funValTC f) vs) (funSExp f)))
         (Conf Exp s3 n3 (Val v3)) ->
    isValueList2T ls vs -> 
    EClosure fenv env (Conf Exp s0 (S n0) (Call x (PS ls)))
                           (Conf Exp s3 n3 (Val v3)).
Proof.
  intros.
  econstructor.
  eapply Call_EStepS.
  exact X0.
  exact H.
  exact H0.
  reflexivity.
  reflexivity.
  exact X.
Defined.  


Lemma Apply_FStepS :   
   forall (fenv: funEnv) (env: valEnv)
          (s0 s2 s3: W) (n0 n2 n3 n5 n6: nat) (x: Id)
          (v3: Value) (vs: list Value) (e: Exp) (f: Fun) (ls: list Exp),
    findE fenv x = Some f ->
    funArity f = length vs ->
    n6 = min n2 n5 ->
    EClosure fenv env (Conf Exp s0 n0 e)
             (Conf Exp s0 n0 (Val (cst Nat (S n5)))) -> 
    EClosure fenv env
             (Conf Exp s2 n6
                   (BindMS (mkVEnv (funValTC f) vs) (funSExp f)))
         (Conf Exp s3 n3 (Val v3)) ->
    PClosure fenv env (Conf Prms s0 n0 (PS ls))
         (Conf Prms s2 (S n2) (PS (map Val vs))) ->  
    EClosure fenv env (Conf Exp s0 n0 (Apply x (PS ls) e))
                           (Conf Exp s3 n3 (Val v3)).
Proof.
  intros.
  eapply Apply2_extended_congruence with (x:=x) (e:=e) (ps:=PS ls) in X.
  eapply EClosConcat.
  exact X.
  eapply Apply1_extended_congruence
            with (x:=x) (ps:=PS ls) (v:=cst Nat (S n5)) in X1.
  eapply EClosConcat.
  exact X1.
  econstructor.
  instantiate (1:= Conf Exp s2 (S n6)
                        (Call x (PS (map Val vs)))).
  econstructor.
  exact f.
  reflexivity.
  eapply forallValues.
  simpl.
  inversion H1; subst.
  auto.
  econstructor.
  instantiate (1:=(Conf Exp s2 n6
                        (BindMS (mkVEnv (funValTC f) vs) (funSExp f)))).
  econstructor.
  econstructor.
  eassumption.
  assumption.
  reflexivity.
  reflexivity.
  assumption.
Defined.  


Lemma Apply_FStep0 :   
   forall (fenv: funEnv) (env: valEnv)
          (s0 s1: W) (n0 n1 n2: nat) (x: Id)
          (e: Exp) (v0 v: Value) (vs: list Value) (f: Fun) (ps: Prms),
     EClosure fenv env (Conf Exp s0 n0 e) (Conf Exp s0 n0 (Val v0)) ->
     PClosure fenv env (Conf Prms s0 n0 ps)
              (Conf Prms s1 n1 (PS (map Val vs))) ->
     findE fenv x = Some f ->
     v = fun0Exp f ->
     v0 = cst Nat n2 ->
     n1 = 0 -> 
     funArity f = length vs ->
     EClosure fenv env (Conf Exp s0 n0 (Apply x ps e))
                       (Conf Exp s1 n1 (Val v)).
  intros.
  eapply (EClosConcat fenv env).
  instantiate (1:=Conf Exp s1 0 (Call x (PS (map Val vs)))).
  eapply Apply_FStep.
  eassumption.
  eassumption.
  eassumption.
  rewrite H2.
  simpl.
  reflexivity.
  eassumption.
  rewrite H2.
  eapply Call_FStep0.
  eassumption.
  assumption.
  assumption.
  reflexivity.
Defined.


Lemma Apply_FStep01 :   
   forall (fenv: funEnv) (env: valEnv)
          (s0 s1: W) (n0 n1 n2: nat) (x: Id)
          (e: Exp) (v0 v: Value) (vs: list Value) (f: Fun) (ps: Prms),
     EClosure fenv env (Conf Exp s0 n0 e) (Conf Exp s0 n0 (Val v0)) ->
     PClosure fenv env (Conf Prms s0 n0 ps)
              (Conf Prms s1 n1 (PS (map Val vs))) ->
     findE fenv x = Some f ->
     v = fun0Exp f ->
     v0 = cst Nat n2 ->
     0 = min n1 n2 -> 
     funArity f = length vs ->
     EClosure fenv env (Conf Exp s0 n0 (Apply x ps e))
                       (Conf Exp s1 0 (Val v)).
  intros.
  eapply (EClosConcat fenv env).
  instantiate (1:=Conf Exp s1 (min n1 n2) (Call x (PS (map Val vs)))).
  eapply Apply_FStep.
  eassumption.
  eassumption.
  eassumption.
  reflexivity.
  eassumption.
  rewrite <- H2. 
  eapply Call_FStep0.
  eassumption.
  assumption.
  assumption.
  reflexivity.
Defined.



Lemma Modify_FStep :   
   forall (n: nat) (fenv: funEnv) (env: valEnv)
          (s0 s1 s2: W) (n0 n1: nat) (t1 t2: VTyp)
          (xf: XFun t1 t2)
          (e: Exp) (v1: sVTyp t1) (v2: Value),
     EClosure fenv env (Conf Exp s0 n0 e) (Conf Exp s1 n1 (Val (cst t1 v1))) ->
     v2 = (cst t2 (x_eval t1 t2 xf v1 s1)) ->
     s2 = x_exec t1 t2 xf v1 s1 -> 
     EClosure fenv env (Conf Exp s0 n0 (Modify t1 t2 xf e))
                       (Conf Exp s2 n1 (Val v2)).
  intros.
  eapply (EClosConcat fenv env).
  instantiate (1:=Conf Exp s1 n1 (Modify t1 t2 xf (Val (cst t1 v1)))).
  eapply Modify_extended_congruence.
  eassumption.
  eapply StepIsEClos.
  inversion H; subst.
  econstructor.
Defined.  
  

(****************************************************************************)

Lemma Pure_step_inv1 :
     forall (fenv: funEnv) (env: valEnv)
                           (s s': W) (n n': nat) 
                           (e e': Exp),
     Pure e ->   
     EStep fenv env (Conf Exp s n e) (Conf Exp s' n' e') ->
     Pure e'.
Proof.
  intros.
  revert X0.
  revert s s' n n' e'.
  induction X.
  intros.
  inversion X0.
  intros.
  inversion X0; subst.
  constructor.
Defined.
  
Lemma Pure_inv1 :
     forall (fenv: funEnv) (env: valEnv)
                           (s s': W) (n n': nat) 
                           (e e': Exp),
     Pure e ->   
     EClosure fenv env (Conf Exp s n e) (Conf Exp s' n' e') ->
     Pure e'.
Proof.
  intros.
  dependent induction X0.
  assumption.
  destruct p2.
  specialize (IHX0 e' qq).
  eapply IHX0.
  eapply Pure_step_inv1 with (e':=qq) (e:=e).
  assumption.
  eassumption.
  reflexivity.
  reflexivity.
Defined.  

Lemma Pure_step_sideffect :
     forall (fenv: funEnv) (env: valEnv)
                           (s s': W) (n n': nat) 
                           (e e': Exp),
     Pure e ->   
     EStep fenv env (Conf Exp s n e) (Conf Exp s' n' e') ->
     s = s' /\ n = n'.
Proof.
  intros.
  inversion X; subst.
  inversion X0.
  inversion X0; subst.
  auto.
Defined.

Lemma Pure_sideffect :
     forall (fenv: funEnv) (env: valEnv)
                           (s s': W) (n n': nat) 
                           (e e': Exp),
     Pure e ->   
     EClosure fenv env (Conf Exp s n e) (Conf Exp s' n' e') ->
     s = s' /\ n = n'.
Proof.
  intros.
  dependent induction X0.
  auto.
  destruct p2.
  generalize e0.
  intro k.
  eapply Pure_step_sideffect in k.
  destruct k.
  inversion H; subst.
  specialize (IHX0 e' qq).
  eapply Pure_step_inv1 in e0.
  specialize (IHX0 e0).
  specialize (IHX0 n' fuel s' state).
  specialize (IHX0 eq_refl eq_refl).
  assumption.
  assumption.
  assumption.
Defined.  
  

(******************************************************************)

(** lemmas about parameters *)

Lemma PrmsStep_aux0 :
    forall (fenv: funEnv) (env: valEnv)
           (s s': W) (n n': nat) (es es': list Exp),
         PStep fenv env (Conf Prms s n (PS es))
                     (Conf Prms s' n' (PS es')) ->
         length es = length es'.  
Proof.
  intros.
  dependent induction X.
  specialize (IHX s s' n n' es0 es'0 eq_refl eq_refl).
  simpl.
  auto.
  auto.
Defined.  
 
Lemma PrmsClos_aux0 :
    forall (fenv: funEnv) (env: valEnv)
            (s s': W) (n n': nat) (es es': list Exp),
         PClosure fenv env (Conf Prms s n (PS es))
                     (Conf Prms s' n' (PS es')) ->
         length es = length es'.  
Proof.
  intros.
  dependent induction X.
  auto.
  destruct p2.
  destruct qq.
  eapply PrmsStep_aux0 in p.
  specialize (IHX state s' fuel n' es0 es' eq_refl eq_refl).
  rewrite <- p in IHX.
  auto.
Defined.  


Lemma PrmsClos_aux1 (fenv: funEnv) (env: valEnv)
                     (e: Exp) (v: Value) (es es': list Exp) (w: W * nat)
      : {w' : W * nat &
      PClosure fenv env (Conf Prms (fst w) (snd w) (PS (e :: es)))
                  (Conf Prms (fst w') (snd w') (PS (Val v :: es')))} ->
      {w' : W * nat &
         prod (EClosure fenv env (Conf Exp (fst w) (snd w) e)
               (Conf Exp (fst w') (snd w') (Val v)))
            {w'' : W * nat &
                  PClosure fenv env (Conf Prms (fst w') (snd w') (PS es))
                                (Conf Prms (fst w'') (snd w'') (PS es'))} }.         
Proof.
  intros.
  destruct X as [w2 X].
  dependent induction X.
  - econstructor.
    split.
    econstructor.
    econstructor.
    econstructor.
  - destruct p2.
    destruct qq.
    destruct es0 as [| e1 es1].
    inversion p.
    specialize (IHX e1 v es1 es' (state,fuel) w2 eq_refl eq_refl).
    destruct IHX.
    destruct p0.
    destruct s.
    inversion e0; subst.
    inversion p; subst.
    econstructor.
    split.
    econstructor.
    econstructor.
    econstructor.
    exact X0.
    exact p0.
    econstructor.
    split.
    eapply StepIsEClos.
    exact X0.
    econstructor.
    exact p0.
    (**)
    inversion e0; subst.
    inversion X0.
    inversion p; subst.
    inversion X0.
    econstructor.
    split.
    econstructor.
    exact X4.
    exact e0.
    econstructor.
    exact p0.
Defined.    


Lemma PrmsClos_aux2 (fenv: funEnv) (env: valEnv)
      (e: Exp) (v: Value) (es es': list Exp)
      (w0 w1: W) (n0 n1: nat) : 
      PClosure fenv env (Conf Prms w0 n0 (PS (Val v :: es)))
                  (Conf Prms w1 n1 (PS (Val v :: es'))) ->
      PClosure fenv env (Conf Prms w0 n0 (PS es))
                  (Conf Prms w1 n1 (PS es')).         
Proof.
  intros.
  dependent induction X.
  - constructor.
  - destruct p2.
    destruct qq.
    destruct es0.
    inversion p.
    inversion p; subst.
    specialize (IHX v es0 es' state w1 fuel n1 eq_refl eq_refl).
    econstructor.
    exact X0.
    exact IHX.
    inversion X0.
Defined.    
    

Lemma PrmsClos_aux3 (fenv: funEnv) (env: valEnv)
      (e: Exp) (v: Value) (es es': list Exp)
      (w0 w1: W) (n0 n1: nat) :
      PClosure fenv env (Conf Prms w0 n0 (PS (e :: es)))
                  (Conf Prms w1 n1 (PS (Val v :: es'))) ->
      {s : W * nat &
        prod (EClosure fenv env (Conf Exp w0 n0 e)
               (Conf Exp (fst s) (snd s) (Val v)))
             (PClosure fenv env (Conf Prms (fst s) (snd s) (PS es))
                                (Conf Prms w1 n1 (PS es'))) }.         
Proof.
  intros.
  dependent induction X.
  - econstructor 1 with (x:=(w1,n1)).
    split.
    simpl.
    econstructor.
    simpl.
    econstructor.
  - destruct p2.
    destruct qq.
    destruct es0 as [| e1 es1].
    inversion p.
    inversion p; subst.
    
    specialize (IHX (Val v0) v es1 es' state w1 fuel n1 eq_refl eq_refl).
    destruct IHX.
    destruct p0.
    destruct x.
    
    constructor 1 with (x:=(w0,n0)).
    simpl in *.
    inversion e; subst.
    split.
    constructor.
    econstructor.
    exact X0.
    exact p0.

    inversion X1.
    
    specialize (IHX e1 v es1 es' state w1 fuel n1 eq_refl eq_refl).
    destruct IHX.
    destruct p0.
    destruct x.

    constructor 1 with (x:=(w,n)).
    simpl in *.
    split.
    econstructor.
    exact X0.
    exact e0.
    exact p0.
Defined.
    
    
Lemma prmsAux1
      (ftenv: funTC) (tenv: valTC) (ps: Prms) (pt: PTyp) :  
  forall (fenv: funEnv) (env: valEnv),                      
    FEnvTyping fenv ftenv ->
    EnvTyping env tenv ->
    forall w: W * nat, 
    (sigT (fun (w': W * nat) => 
           sigT (fun (es: list Exp) => 
           prod (isValueListT es) 
           (prod (PClosure fenv env (Conf Prms (fst w) (snd w) ps)
                                    (Conf Prms (fst w') (snd w') (PS es))) 
                 (PrmsTyping ftenv tenv (PS es) pt))))) ->       
    (sigT (fun (w': W * nat) =>
           sigT (fun (vs: list Value) => 
           prod (PClosure fenv env (Conf Prms (fst w) (snd w) ps)
                            (Conf Prms (fst w') (snd w') (PS (map Val vs)))) 
                (PrmsTyping ftenv tenv (PS (map Val vs)) pt)))).
Proof.
  intros.
  destruct X as [n1 X].
  destruct X as [es X].
  destruct X as [X1 X2].
  destruct X2 as [X2 X3].
  exists n1.
  eapply isValueList22_T in X1.
  inversion X1.
  destruct X1 as [vs].
  constructor 1 with (x:=vs).
  split.
  - eapply PConcat.
    eassumption.
    inversion i; subst.
    constructor.
  - destruct pt.
    inversion i; subst.
    exact X3.
Defined.    
   

Lemma NoPrmsStep (fenv: funEnv) (env: valEnv)
                  (w0 w1: W * nat) (es1 es2: list Exp):
  PStep fenv env (Conf Prms (fst w0) (snd w0) (PS es1))
                      (Conf Prms (fst w1) (snd w1) (PS es2)) ->
   isValueListT es1 -> False.
Proof.
  intros.
  revert X0.
  dependent induction X.
  intros.
  inversion X0; subst.
  eapply IHX.
  reflexivity.
  reflexivity.
  auto.
  intro.
  inversion X0; subst.
  inversion X; subst.
  inversion e0.
Defined.


Lemma NoNilPrmsClos1 (fenv: funEnv) (env: valEnv)
                  (s0 s1: W) (n0 n1: nat) (e: Exp) (es: list Exp):
  PClosure fenv env (Conf Prms s0 n0 (PS (e::es)))
                      (Conf Prms s1 n1 (PS nil)) -> False.
  intros.
  dependent induction X.
  destruct p2.
  destruct qq.
  destruct es0.
  inversion p.
  specialize (IHX state s1 fuel n1 e0 es0 eq_refl eq_refl).
  exact IHX.
Defined.  

Lemma NoNilPrmsClos2 (fenv: funEnv) (env: valEnv)
                  (s0 s1: W) (n0 n1: nat) (e: Exp) (es: list Exp):
  PClosure fenv env (Conf Prms s0 n0 (PS nil))
                      (Conf Prms s1 n1 (PS (e::es))) -> False.
  intros.
  dependent induction X.
  destruct p2.
  destruct qq.
  destruct es0.
  specialize (IHX state s1 fuel n1 e es eq_refl eq_refl).
  exact IHX.
  inversion p.
Defined.  



(************* from TSoundness ***************************************)
(********************************************************************)

Program Definition ExtRelTyp (tenv : valTC) (x : Id)
      (v : Value) (t : VTyp) (mB: valueVTyp v = t)
       (env: valEnv) (m2: EnvTyping env tenv) (mA: findE env x = Some v) :
   findE tenv x = Some t.  
  unfold EnvTyping in m2.
  unfold MatchEnvs in m2.
  rewrite m2.
  unfold thicken.
  rewrite <- mB.
  revert m2.
  revert tenv.
  induction env.
  inversion mA.
  intros tenv m2.
  destruct a.
  simpl in *.
  destruct (IdT.IdEqDec x i).
  injection mA; intro.
  rewrite H.
  reflexivity.
  specialize (IHenv mA (map (thicken StaticSemL.Id valueVTyp) env) eq_refl).
  exact IHenv.
Defined. 



Program Definition ExtRelVal2A {K V1 V2: Type} {h: DEq K} (f: V1 -> V2)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2): 
    MatchEnvs K f venv tenv ->
    findE tenv x = Some t ->
    sigT2 (fun v: V1 => findE venv x = Some v) (fun v: V1 => f v = t). 
Proof.
  unfold MatchEnvs.
  unfold thicken.
  intros.
  rewrite H in H0.
  clear H.
  clear tenv.
  induction venv.
  simpl in *.
  discriminate H0.
  destruct a.
  simpl in *.
  destruct (dEq x k).
  injection H0; intro.
  clear H0.
  constructor 1 with (x:=v).
  reflexivity.
  rewrite H in *.
  reflexivity.
  eapply IHvenv.
  intuition n.
Defined.  


Definition ExtRelVal2A_1 {K V1 V2: Type} {h: DEq K} (f: V1 -> V2)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2) 
    (k1: MatchEnvs K f venv tenv)
    (k2: findE tenv x = Some t) : V1 :=
   proj1_of_sigT2 (ExtRelVal2A f tenv venv x t k1 k2).

Definition ExtRelVal2A_2 {K V1 V2: Type} {h: DEq K} (f: V1 -> V2)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2) 
    (k1: MatchEnvs K f venv tenv)
    (k2: findE tenv x = Some t) :
  findE venv x = Some (ExtRelVal2A_1 f tenv venv x t k1 k2) :=
  projT2 (fst_sigT_of_sigT2 (ExtRelVal2A f tenv venv x t k1 k2)).

Definition ExtRelVal2A_3 {K V1 V2: Type} {h: DEq K} (f: V1 -> V2)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2) 
    (k1: MatchEnvs K f venv tenv)
    (k2: findE tenv x = Some t) : sigT (fun v: V1 => f v = t) :=
  snd_sigT_of_sigT2 (ExtRelVal2A f tenv venv x t k1 k2). 

Definition ExtRelVal2A_4 {K V1 V2: Type} {h: DEq K} (f: V1 -> V2)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2) 
    (k1: MatchEnvs K f venv tenv)
    (k2: findE tenv x = Some t) :
  f (ExtRelVal2A_1 f tenv venv x t k1 k2) = t :=
  projT2 (snd_sigT_of_sigT2 (ExtRelVal2A f tenv venv x t k1 k2)). 


Lemma TransformA_Var (P : valEnv -> Exp -> VTyp -> Type)
      (Q : VTyp -> Type)
      (F1 : forall (env: valEnv) (x: Id) (t: VTyp), P env (Var x) t -> Type)
      (F2: forall t: VTyp, Q t -> Type)
  : (forall (tenv : valTC) (x : Id)
    (v : Value) 
    (t : VTyp) (i : findE tenv x = Some t) (mB: valueVTyp v = t)
    (env: valEnv) (mA: findE env x = Some v)
    (m2: EnvTyping env tenv), 
    (P env (Var x) t * Q t) ->
     sigT (fun I: (P env (Var x) t * Q t) => 
             F1 env x t (fst I) = F2 t (snd I))) -> 
    forall (tenv : valTC) (x : Id) (t: VTyp)
    (i : findE tenv x = Some t) 
    (env: valEnv) 
    (m2: EnvTyping env tenv), 
    (P env (Var x) t * Q t) ->
     sigT (fun I: (P env (Var x) t * Q t) => 
             F1 env x t (fst I) = F2 t (snd I)).
Proof.
  intros.
  specialize (X tenv x (ExtRelVal2A_1 valueVTyp tenv env x t m2 i) t i
         (ExtRelVal2A_4 valueVTyp tenv env x t m2 i)     
         env                                          
         (ExtRelVal2A_2 valueVTyp tenv env x t m2 i) 
         m2 X0).       
  exact X.   
Defined.


(*****************************************************************)


Program Definition ExtRelVal2B 
       (env: valEnv) (x: Id) (t: VTyp): 
    findE (valEnv2valTC env) x = Some t ->
    sigT2 (fun v: Value => findE env x = Some v)
          (fun v: Value => projT1 v = t). 
Proof.
  induction env.
  simpl in *.
  intros.
  discriminate H.
  destruct a.
  simpl in *.
  destruct (IdT.IdEqDec x i).
  intro.
  injection H; intro.
  constructor 1 with (x:=v).
  reflexivity.
  exact H0.
  intro.
  eapply IHenv.
  exact H.
Defined.  

Lemma ExtRelVal2B_ok (env: valEnv)
    (x: Id) (t: VTyp) (v: Value) 
    (k1: findE (valEnv2valTC env) x = Some t)
    (k2: findE env x = Some v) :
  v = proj1_of_sigT2 (ExtRelVal2B env x t k1).
  induction env.
  inversion k1.
  destruct a.
  simpl in k1, k2.
  simpl.
  unfold ExtRelVal2B.
  unfold proj1_of_sigT2.
  unfold sigT_of_sigT2.
  simpl.
  destruct (IdT.IdEqDec x i).
  inversion k2; subst.
  reflexivity.
  specialize (IHenv k1 k2).
  rewrite IHenv.
  reflexivity.
Defined.

Lemma ExtRelVal2B_Typ_ok (env: valEnv)
    (x: Id) (t: VTyp) (v: Value) 
    (k1: findE (valEnv2valTC env) x = Some t)
    (k2: findE env x = Some v) :
  (sVTyp (projT1 v)) =
      sVTyp (projT1
       (proj1_of_sigT2
          (ExtRelVal2B env x t k1))).
  rewrite (ExtRelVal2B_ok env x t v k1 k2).
  reflexivity.
Defined.  

Lemma ExtRelVal2B_TypS_ok (env: valEnv)
    (x: Id) (t: VTyp) (v: Value) 
    (k1: findE (valEnv2valTC env) x = Some t)
    (k2: findE env x = Some v) :
    sVTyp (projT1
       (proj1_of_sigT2
          (ExtRelVal2B env x t k1))) =
    (sVTyp (projT1 v)).
  rewrite (ExtRelVal2B_ok env x t v k1 k2).
  reflexivity.
Defined.  



Definition ExtRelVal2B_1
           (env: valEnv) (x: Id) (t: VTyp)
           (k: findE (valEnv2valTC env) x = Some t) : Value :=
 proj1_of_sigT2 (ExtRelVal2B env x t k).
  
Definition ExtRelVal2B_2
           (env: valEnv) (x: Id) (t: VTyp)
           (k: findE (valEnv2valTC env) x = Some t) :
  findE env x = Some (ExtRelVal2B_1 env x t k) :=
 projT2 (fst_sigT_of_sigT2 (ExtRelVal2B env x t k)).


Definition ExtRelVal2B_3 (env: valEnv) (x: Id) (t: VTyp)
           (k: findE (valEnv2valTC env) x = Some t) :
    sigT (fun v: Value => valueVTyp v = t) :=
 snd_sigT_of_sigT2 (ExtRelVal2B env x t k).


Definition ExtRelVal2B_4
           (env: valEnv) (x: Id) (t: VTyp)
           (k: findE (valEnv2valTC env) x = Some t) :
  valueVTyp (ExtRelVal2B_1 env x t k) = t :=
 projT2 (snd_sigT_of_sigT2 (ExtRelVal2B env x t k)).


End DerivDyn.


