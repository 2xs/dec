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
  inversion H2; subst.
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


