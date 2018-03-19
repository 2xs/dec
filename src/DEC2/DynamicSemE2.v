(*  DEC 2.0 language specification.
   Paolo Torrini, 
   Universite' Lille-1 - CRIStAL-CNRS
*)

Require Import List.
Require Import Equality.

Require Import ModTypE1. 
Require Import TypSpecE1. 
Require Import LangSpecE1. 
Require Import StaticSemE2.

Import ListNotations.


(** * DEC 2.0 language specification *)

(** Dynamic small-step semantics *)

Module DynamicSem (IdT: ModTyp) <: ModTyp.

Module StaticSemL := StaticSem IdT.
Export StaticSemL.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.


(*********************************************************************)

(** * Dynamic semantics *)

(** Configurations *)

Inductive AConfig (T: Type) : Type := Conf (state: W) (fuel: nat) (qq: T).

Definition confState {T: Type} (a: AConfig T) : W :=
  match a with | Conf _ s _ _ => s end.

Definition confFuel {T: Type} (a: AConfig T) : nat :=
  match a with | Conf _ _ n _ => n end.

Definition confProg {T: Type} (a: AConfig T) : T :=
  match a with | Conf _ _ _ x => x end.


Fixpoint sValueList (ls: list Value) : tlist2type (map valueSTyp ls) :=
  match ls with
    | nil => tt
    | v:: vs => (sValue v, sValueList vs)
  end.                
   
Lemma sValueListRel 
         (ftenv: funTC) (tenv: valTC) (vs: list Value) (pt: PTyp) :
  PrmsTyping ftenv tenv (PS (map Val vs)) pt -> sPTyp pt.  
  revert pt.
  unfold sPTyp.
  induction vs.
  intros.
  inversion X; subst.
  simpl.
  exact tt.
  intros.
  inversion X; subst.
  inversion X0; subst.
  specialize (IHvs (PT ts) X1).
  simpl in *.
  split.
  destruct a.
  simpl.
  destruct v.
  inversion X2; subst.
  simpl in *.
  exact v.
  exact IHvs.
Defined.  
  

(** Program term computation *)    

Inductive EStep : (** - Expressions *)
            funEnv -> valEnv -> AConfig Exp -> AConfig Exp -> Type :=
(** - variable lifting *)
| Var_EStep : forall (fenv: funEnv) (env: valEnv)
                     (s: W) (n: nat) (x: Id) (v: Value),
    findE env x = Some v ->
    EStep fenv env (Conf Exp s n (Var x))
                        (Conf Exp s n (Val v))
(** - sequencing *)
| BindN_EStep : forall (fenv: funEnv) (env: valEnv)
                       (s: W) (n: nat) (v: Value) (e: Exp),
    EStep fenv env (Conf Exp s n (BindN (Val v) e)) (Conf Exp s n e)
| BindN_Cg_EStep : forall (fenv: funEnv) (env: valEnv) 
                          (s s': W) (n n': nat) (e1 e1' e2: Exp),
    EStep fenv env (Conf Exp s n e1) (Conf Exp s' n' e1') ->
    EStep fenv env (Conf Exp s n (BindN e1 e2))
                   (Conf Exp s' n' (BindN e1' e2))
(** - let-style binding *)
| BindS_EStep : forall (fenv: funEnv) (env: valEnv) 
                       (s: W) (n: nat) (x: Id) (v: Value) (e: Exp)
                       (mt: option VTyp),          
    EStep fenv env (Conf Exp s n (BindS x mt (Val v) e))
                   (Conf Exp s n (BindMS (singleE x v) e))
| BindS_Cg_EStep : forall (fenv: funEnv) (env: valEnv) 
                          (s s': W) (n n': nat) (x: Id) (e1 e1' e2: Exp)
                          (m: option VTyp),
    EStep fenv env (Conf Exp s n e1) (Conf Exp s' n' e1') ->
    EStep fenv env (Conf Exp s n (BindS x m e1 e2))     
                   (Conf Exp s' n' (BindS x m e1' e2))
(** - local environments *)
| BindMS_EStep : forall (fenv: funEnv) (env env': valEnv)    
                        (s: W) (n: nat) (v: Value),
    EStep fenv env (Conf Exp s n (BindMS env' (Val v)))
                   (Conf Exp s n (Val v))
| BindMS_Cg_EStep : forall (fenv: funEnv) (env envL env': valEnv) 
                           (s s': W) (n n': nat) (e e': Exp), 
    env' = envL ++ env ->
    EStep fenv env' (Conf Exp s n e) (Conf Exp s' n' e') ->
    EStep fenv env (Conf Exp s n (BindMS envL e))
                   (Conf Exp s' n' (BindMS envL e'))
(** - conditional *)
| IfThenElse_EStep1 : forall (fenv: funEnv) (env: valEnv)
                             (s: W) (n: nat) (e1 e2: Exp),
    EStep fenv env (Conf Exp s n
                   (IfThenElse (Val (cst Bool true)) e1 e2))
                        (Conf Exp s n e1)                   
| IfThenElse_EStep2 : forall (fenv: funEnv) (env: valEnv)
                             (s: W) (n: nat) (e1 e2: Exp),
     EStep fenv env (Conf Exp s n
                (IfThenElse (Val (cst Bool false)) e1 e2))
                         (Conf Exp s n e2)
| IfThenElse_Cg_EStep :  forall (fenv: funEnv) (env: valEnv)
                                (s s': W) (n n': nat)
                                (e e' e1 e2: Exp),
     EStep fenv env (Conf Exp s n e) (Conf Exp s' n' e') ->   
     EStep fenv env (Conf Exp s n (IfThenElse e e1 e2))
                    (Conf Exp s' n' (IfThenElse e' e1 e2))
(* function application - note: no side-effects in the 
   fuel congruence rule *)           
| Apply_Cg1_EStep : forall (fenv: funEnv) (env: valEnv)
                           (s s': W) (n n': nat) (x: Id) (ps: Prms) 
                           (e e': Exp),
     EStep fenv env (Conf Exp s n e) (Conf Exp s' n' e') -> 
     EStep fenv env (Conf Exp s n (Apply x ps e))
                    (Conf Exp s' n' (Apply x ps e'))
| Apply_Cg2_EStep : forall (fenv: funEnv) (env: valEnv)
                           (s s': W) (n n': nat) (x: Id) (ps ps': Prms) 
                           (v: Value),
     PStep fenv env (Conf Prms s n ps) (Conf Prms s' n' ps') ->
     EStep fenv env (Conf Exp s n (Apply x ps (Val v)))
                    (Conf Exp s' n' (Apply x ps' (Val v)))
| Apply_EStep : forall (fenv: funEnv) (env: valEnv)
                       (s: W)  (n0 n1 n: nat) (x: Id)  
                       (es: list Exp) (v: Value)
                       (f: Fun),    
     v = cst Nat n1 ->
     isValueListT es ->
     n = min n0 n1 -> 
     EStep fenv env (Conf Exp s n0 (Apply x (PS es) (Val v)))
                    (Conf Exp s n (Call x (PS es)))
(*                    (Conf Exp s n (BindMS env' (Call x (PS es)))) *)
(* function call *)
| Call_Cg_EStep : forall (fenv: funEnv) (env: valEnv)
                         (s s': W) (n n': nat) (x: Id) (ps ps': Prms),
     PStep fenv env (Conf Prms s n ps) (Conf Prms s' n' ps') ->
     EStep fenv env (Conf Exp s n (Call x ps))
                    (Conf Exp s' n' (Call x ps'))
| Call_EStep0 : forall (fenv: funEnv) (env env': valEnv)
                       (s: W) (x: Id) 
                       (es: list Exp) 
                       (vs: list Value) 
                       (f: Fun) (v: Value),
     findE fenv x = Some f ->      
     isValueList2T es vs ->              
     funArity f = length vs ->
     env' = mkVEnv (funValTC f) vs ->
     v = fun0Exp f -> 
     EStep fenv env (Conf Exp s 0 (Call x (PS es)))
                    (Conf Exp s 0 (Val v))
| Call_EStepS : forall (fenv: funEnv) (env env': valEnv)
                       (s: W) (n: nat) (x: Id) 
                       (es: list Exp) 
                       (vs: list Value) 
                       (f: Fun) (e: Exp),            
     isValueList2T es vs ->              
     findE fenv x = Some f ->
     funArity f = length vs ->
     env' = mkVEnv (funValTC f) vs ->
     e = funSExp f -> 
     EStep fenv env (Conf Exp s (S n) (Call x (PS es)))
                         (Conf Exp s n (BindMS env' e))
(** - modify *)
| Modify_EStep : forall (fenv: funEnv) (env: valEnv) (s: W) (n: nat)
                        (t1 t2: VTyp) 
                        (XF: XFun t1 t2)
                        (w: sVTyp t1),
      EStep fenv env
         (Conf Exp s n (Modify t1 t2 XF (Val (cst t1 w))))
         (Conf Exp (x_exec t1 t2 XF w s) n 
                   (Val (cst t2 (x_eval t1 t2 XF w s))))      
| Modify_Cg_EStep : forall (fenv: funEnv) (env: valEnv) (s s': W) (n n': nat)
                           (t1 t2: VTyp) 
                           (XF: XFun t1 t2) (e e': Exp),
    EStep fenv env (Conf Exp s n e) (Conf Exp s' n' e') ->
    EStep fenv env (Conf Exp s n (Modify t1 t2 XF e))
                        (Conf Exp s' n' (Modify t1 t2 XF e'))
with PStep : (** - Parameters *)
       funEnv -> valEnv -> AConfig Prms -> AConfig Prms -> Type :=
| Prms_Cg_Step : forall (fenv: funEnv) (env: valEnv)
                        (s s': W) (n n': nat)
                        (es es': list Exp) (v: Value),
         PStep fenv env (Conf Prms s n (PS es))
                        (Conf Prms s' n' (PS es')) ->
         PStep fenv env (Conf Prms s n (PS (Val v :: es)))
                        (Conf Prms s' n' (PS (Val v :: es')))
| Prms_Step1 : forall (fenv: funEnv) (env: valEnv)
                      (s s': W) (n n': nat) (es: list Exp) (e e': Exp),
         EStep fenv env (Conf Exp s n e) (Conf Exp s' n' e') ->   
         PStep fenv env (Conf Prms s n (PS (e::es)))
                        (Conf Prms s' n' (PS (e'::es))).


Scheme EStep_mut := Induction for EStep Sort Type
with PStep_mut := Induction for PStep Sort Type.


(*****************************************************************)    

(** reflexive-transitive closures *)

Inductive EClosure :
     funEnv -> valEnv -> AConfig Exp -> AConfig Exp -> Type :=
  | EC_Base : forall (fenv: funEnv) (env: valEnv) (p: AConfig Exp), 
              EClosure fenv env p p 
  | EC_Step : forall (fenv: funEnv) (env: valEnv) (p1 p2 p3: AConfig Exp),
           EStep fenv env p1 p2 ->
           EClosure fenv env p2 p3 -> EClosure fenv env p1 p3.


Inductive PClosure :
     funEnv -> valEnv -> AConfig Prms -> AConfig Prms -> Type :=
  | PrmsC_Base : forall (fenv: funEnv) (env: valEnv) (p: AConfig Prms), 
              PClosure fenv env p p 
  | PrmsC_Step : forall (fenv: funEnv) (env: valEnv)
                        (p1 p2 p3: AConfig Prms),
                   PStep fenv env p1 p2 ->
                   PClosure fenv env p2 p3 ->
                   PClosure fenv env p1 p3.

(******************************************************************)

(** a small step is a big step *)

Lemma StepIsEClos :
         forall (fenv: funEnv) (env: valEnv) (p1 p2: AConfig Exp),
               EStep fenv env p1 p2 -> EClosure fenv env p1 p2.
Proof.
intros.
eapply EC_Step.
eassumption.
constructor.
Defined.


Lemma StepIsPClos :
     forall (fenv: funEnv) (env: valEnv) (p1 p2: AConfig Prms),
       PStep fenv env p1 p2 -> PClosure fenv env p1 p2.
Proof.
  intros.
  eapply PrmsC_Step.
  eassumption.
  constructor.
Defined.


(**************************************************************)

(** appending two big steps gives one big step *)

Lemma EClosConcat :
    forall (fenv: funEnv) (env: valEnv) 
           (p1 p2 p3: AConfig Exp),
   EClosure fenv env p1 p2 -> EClosure fenv env p2 p3 ->
                                   EClosure fenv env p1 p3.
Proof.
  intros.
  induction X.
  assumption.
  apply IHX in X0.
  econstructor.
  eassumption.
  assumption.
Defined.

Lemma PConcat :
  forall (fenv: funEnv) (env: valEnv) 
         (p1 p2 p3: AConfig Prms),
   PClosure fenv env p1 p2 -> PClosure fenv env p2 p3 ->
                              PClosure fenv env p1 p3.
Proof.
  intros.
  induction X.
  assumption.
  apply IHX in X0.
  econstructor.
  eassumption.
  assumption.
Defined.


End DynamicSem.


(****************************************************************)
(*
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
  inversion H; subst.
  inversion H; subst.
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
          (e: Exp) (v: Value) (vs: list Value) (ps: Prms),
     EClosure [] env (Conf Exp s0 n0 e) (Conf Exp s0 n0 (Val v)) ->
     PClosure fenv env (Conf Prms s0 n0 ps)
              (Conf Prms s1 n1 (PS (map Val vs))) ->
     v = cst Nat n2 ->
     n3 = min n1 n2 -> 
     EClosure fenv env (Conf Exp s0 n0 (Apply x ps e))
              (Conf Exp s1 n3 (Call x (PS (map Val vs)))).
  intros.
  eapply (EClosConcat fenv env).
  instantiate (1:=Conf Exp s0 n0 (Apply x ps (Val v))).
  eapply Apply2_extended_congruence.
  eapply EClosWeaken.
  assumption.
  



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
  

End DynamicSem.
*)

(*
Require Import Eqdep FunctionalExtensionality Coq.Program.Tactics.
Require Import Coq.Init.Specif.
Require Import Coq.Logic.JMeq.
*)

(*
Definition callFun (fenv: funEnv) (cenv: tfcEnv) (x: Id) : option Fun :=
  match findE cenv x with
  | None => None
  | Some c =>
    match findE fenv (fst (fst c)) with
    | None => None
    | Some f => Some f
    end
  end.

Definition callNamedFun (fenv: funEnv) (cenv: tfcEnv) (x: Id) :
                                 option (Id * Fun) :=
  match findE cenv x with
  | None => None
  | Some c =>
    match findE fenv (fst (fst c)) with
    | None => None
    | Some f => Some (fst (fst c), f)
    end
  end.
*)


  





