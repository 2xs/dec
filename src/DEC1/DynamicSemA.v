
Require Export Basics.
Require Export EnvLibA.
Require Export RelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Import IdModTypeA.
Require Import StaticSemA.
Require Import TRInductA.

Import ListNotations.

Module Dynamic (IdT: IdModType) <: IdModType.

Module TRInductI := TRInduct IdT.
Export TRInductI.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.


(* Configurations *)

Inductive AConfig (T: Type) : Type :=
          Conf (state: W) (qq: T).


(* Dynamic semantics *)

Inductive QVStep :
   valEnv -> AConfig QValue -> AConfig QValue -> Type :=
   OK_QVStep : forall (env: valEnv) (n: W) (x: Id) (v: Value),
          findET env x v ->  
          QVStep env (Conf QValue n (Var x))
                       (Conf QValue n (QV v)).

Inductive QFStep :
   funEnv -> AConfig QFun -> AConfig QFun -> Type :=
   OK_QFStep : forall (env: funEnv) (n: W) (x: Id) (v: Fun),
          findET env x v ->  
          QFStep env (Conf QFun n (FVar x))
                       (Conf QFun n (QF v)).

    
Inductive EStep : funEnv -> valEnv ->
                                 AConfig Exp -> AConfig Exp -> Type :=
(* modify *)
| Modify_EStep : forall (fenv: funEnv) (env: valEnv) (n: W)
                        (T1 T2: Type) (VT1: ValTyp T1) (VT2: ValTyp T2)
                        (XF: XFun T1 T2) (w: T1),
    EStep fenv env
       (Conf Exp n (Modify T1 T2 VT1 VT2 XF (QV (cst T1 w))))
       (Conf Exp (b_exec T1 T2 XF n w)
                   (Val (cst T2 (b_eval T1 T2 XF n w))))
| Modify_Cg_EStep : forall (fenv: funEnv) (env: valEnv) (n n': W)
                        (T1 T2: Type) (VT1: ValTyp T1) (VT2: ValTyp T2)
                        (XF: XFun T1 T2) (q q': QValue),
    QVStep env (Conf QValue n q) (Conf QValue n' q') ->
    EStep fenv env (Conf Exp n (Modify T1 T2 VT1 VT2 XF q))
                        (Conf Exp n' (Modify T1 T2 VT1 VT2 XF q'))

(* return *)
| Return_EStep : forall (G: Tag)
                        (fenv: funEnv) (env: valEnv) (n: W) (v: Value),
    EStep fenv env (Conf Exp n (Return G (QV v)))
                        (Conf Exp n (Val v))
| Return_Cg_EStep : forall (G: Tag)
                           (fenv: funEnv) (env: valEnv) 
                           (n n': W) (q q': QValue),
    QVStep env (Conf QValue n q) (Conf QValue n' q') ->
    EStep fenv env (Conf Exp n (Return G q)) (Conf Exp n' (Return G q'))
(* bindN *)
| BindN_EStep : forall (fenv: funEnv) (env: valEnv)
                       (n: W) (v: Value) (e: Exp),
    EStep fenv env (Conf Exp n (BindN (Val v) e)) (Conf Exp n e)
| BindN_Cg_EStep : forall (fenv: funEnv) (env: valEnv) 
                          (n n': W) (e1 e1' e2: Exp),
    EStep fenv env (Conf Exp n e1) (Conf Exp n' e1') ->
    EStep fenv env (Conf Exp n (BindN e1 e2))
                        (Conf Exp n' (BindN e1' e2))
(* bindS *)
| BindS_EStep : forall (fenv: funEnv) (env: valEnv) 
                       (n: W) (x: Id) (v: Value) (e: Exp),          
    EStep fenv env (Conf Exp n (BindS x (Val v) e))
                        (Conf Exp n (BindMS emptyE (singleE x v) e))
| BindS_Cg_EStep : forall (fenv: funEnv) (env: valEnv) 
                          (n n': W) (x: Id) (e1 e1' e2: Exp),
    EStep fenv env (Conf Exp n e1) (Conf Exp n' e1') ->
    EStep fenv env (Conf Exp n (BindS x e1 e2))     
                        (Conf Exp n' (BindS x e1' e2))
(* bindMS *)
| BindMS_EStep : forall (fenv fenv': funEnv) (env env': valEnv)    
                        (n: W) (v: Value),
    EStep fenv env (Conf Exp n (BindMS fenv' env' (Val v)))
                     (Conf Exp n (Val v))
| BindMS_Cg_EStep : forall (fenv fenvL fenv': funEnv)
                           (env envL env': valEnv) 
                           (n n': W) (e e': Exp),
    fenv' = fenvL ++ fenv -> 
    env' = envL ++ env ->
    EStep fenv' env' (Conf Exp n e) (Conf Exp n' e') ->
    EStep fenv env (Conf Exp n (BindMS fenvL envL e))
                   (Conf Exp n' (BindMS fenvL envL e'))
(* apply *)
| Apply_EStep0 : forall (fenv fenv': funEnv) (env env': valEnv)
                        (n: W) (e0 e1: Exp)
                        (es: list Exp) (vs: list Value)
                        (x: Id) 
                        (pt: valTC),
     isValueList2T es vs ->              
     length pt = length vs ->
     env' = mkVEnv pt vs ->
     EStep fenv env (Conf Exp n
              (Apply (QF (FC fenv' pt e0 e1 x 0)) (PS es)))
                     (Conf Exp n (BindMS fenv' env' e0))
| Apply_EStep1 : forall (fenv fenv': funEnv) (env env': valEnv)
                        (n: W) (e0 e1: Exp)
                        (es: list Exp) (vs: list Value)
                        (x: Id) (i: nat)
                        (pt: valTC),
     isValueList2T es vs ->              
     length pt = length vs ->
     env' = mkVEnv pt vs ->
     EStep fenv env
           (Conf Exp n (Apply (QF (FC fenv' pt e0 e1 x (S i))) (PS es)))
           (Conf Exp n
                 (BindMS ((x,(FC fenv' pt e0 e1 x i))::fenv') env' e1))
                   | Apply_Cg1_EStep : forall (fenv: funEnv) (env: valEnv)
                           (n n': W) 
                           (f: Fun) (ps ps': Prms),
     PrmsStep fenv env (Conf Prms n ps) (Conf Prms n' ps') ->
     EStep fenv env (Conf Exp n (Apply (QF f) ps))
                         (Conf Exp n' (Apply (QF f) ps'))
| Apply_Cg2_EStep : forall (fenv: funEnv) (env: valEnv)
                           (n n': W) 
                           (qf qf': QFun) (ps: Prms),
     QFStep fenv (Conf QFun n qf) (Conf QFun n' qf') ->
     EStep fenv env (Conf Exp n (Apply qf ps))
                         (Conf Exp n' (Apply qf' ps))
(* ifthenelse *)
| IfThenElse_EStep1 :  forall (fenv: funEnv) (env: valEnv)
                              (n: W) (e1 e2: Exp),
     EStep fenv env (Conf Exp n (IfThenElse (Val (cst bool true)) e1 e2))
                         (Conf Exp n e1)                   
| IfThenElse_EStep2 :  forall (fenv: funEnv) (env: valEnv)
                              (n: W) (e1 e2: Exp),
     EStep fenv env (Conf Exp n
                (IfThenElse (Val (cst bool false)) e1 e2))
                         (Conf Exp n e2)
| IfThenElse_Cg_EStep :  forall (fenv: funEnv) (env: valEnv)
                                (n n': W) (e e' e1 e2: Exp),
     EStep fenv env (Conf Exp n e) (Conf Exp n' e') ->                       
     EStep fenv env (Conf Exp n (IfThenElse e e1 e2))
                         (Conf Exp n' (IfThenElse e' e1 e2))
with PrmsStep :
       funEnv -> valEnv -> AConfig Prms -> AConfig Prms -> Type :=
| Prms_Cg_Step : forall (fenv: funEnv) (env: valEnv)
                   (n n': W) 
                   (es es': list Exp) (v: Value),
         PrmsStep fenv env (Conf Prms n (PS es))
                                (Conf Prms n' (PS es')) ->
         PrmsStep fenv env (Conf Prms n (PS (Val v :: es)))
                                (Conf Prms n' (PS (Val v :: es')))
| Prms_Step1 : forall (fenv: funEnv) (env: valEnv)
                   (n n': W) (es: list Exp) (e e': Exp),
         EStep fenv env (Conf Exp n e) (Conf Exp n' e') ->   
         PrmsStep fenv env (Conf Prms n (PS (e::es)))
                                (Conf Prms n' (PS (e'::es))).

 

Scheme EStep_mut := Induction for EStep Sort Type
with PrmsStep_mut := Induction for PrmsStep Sort Type.


(********************************************************************)

Inductive PStep :
          funEnv -> AConfig Prog -> AConfig Prog -> Type := 
| Prog_PStep : forall (fenv: funEnv) (env: valEnv)   
                      (n n': W) (e e': Exp),
                 EStep fenv env (Conf Exp n e) (Conf Exp n' e') ->
                 env = emptyE -> 
                 PStep fenv (Conf Prog n (prog e))
                                 (Conf Prog n' (prog e'))
| Define_PStep : forall (fenv: funEnv) (env: valEnv)   
                        (n: W) (x: Id) (f: Fun) (v: Value),
      PStep fenv (Conf Prog n (define x f (prog (Val v))))
                      (Conf Prog n (prog (Val v)))
| Define_Cg_PStep : forall (fenv fenv': funEnv)     
                           (n n': W) 
                           (x: Id) (f: Fun) (p p': Prog),
      fenv' = (x, f) :: fenv ->                 
      PStep fenv' (Conf Prog n p) (Conf Prog n' p') ->
      PStep fenv (Conf Prog n (define x f p))
                      (Conf Prog n' (define x f p')).
    
(*****************************************************************)    

(** reflexive-transitive closures *)

Inductive EClosure :
     funEnv -> valEnv -> AConfig Exp -> AConfig Exp -> Type :=
  | EC_Base : forall (fenv: funEnv) (env: valEnv) (p: AConfig Exp), 
              EClosure fenv env p p 
  | EC_Step : forall (fenv: funEnv) (env: valEnv) (p1 p2 p3: AConfig Exp),
           EStep fenv env p1 p2 ->
           EClosure fenv env p2 p3 -> EClosure fenv env p1 p3.


Inductive PrmsClosure :
     funEnv -> valEnv -> AConfig Prms -> AConfig Prms -> Type :=
  | PrmsC_Base : forall (fenv: funEnv) (env: valEnv) (p: AConfig Prms), 
              PrmsClosure fenv env p p 
  | PrmsC_Step : forall (fenv: funEnv) (env: valEnv)
                        (p1 p2 p3: AConfig Prms),
                   PrmsStep fenv env p1 p2 ->
                   PrmsClosure fenv env p2 p3 ->
                   PrmsClosure fenv env p1 p3.

Inductive QFClosure :
     funEnv -> AConfig QFun -> AConfig QFun -> Type :=
  | QF_Base : forall (fenv: funEnv) (p: AConfig QFun), 
              QFClosure fenv p p 
  | QF_Step : forall (fenv: funEnv) (p1 p2: AConfig QFun),
                QFStep fenv p1 p2 -> 
                QFClosure fenv p1 p2.


Inductive RTClosure :
     funEnv -> AConfig Prog -> AConfig Prog -> Type :=
  | RTC_Base : forall (env: funEnv) (p: AConfig Prog), 
              RTClosure env p p 
  | RTC_Step : forall (env: funEnv) (p1 p2 p3: AConfig Prog),
           PStep env p1 p2 -> RTClosure env p2 p3 ->
           RTClosure env p1 p3.


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


Lemma StepIsPrmsClos :
     forall (fenv: funEnv) (env: valEnv) (p1 p2: AConfig Prms),
       PrmsStep fenv env p1 p2 -> PrmsClosure fenv env p1 p2.
Proof.
  intros.
  eapply PrmsC_Step.
  eassumption.
  constructor.
Defined.


Lemma StepIsRTClos :
         forall (fenv: funEnv) (p1 p2: AConfig Prog),
              PStep fenv p1 p2 -> RTClosure fenv p1 p2.
Proof.
  intros.
  eapply RTC_Step.
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

Lemma PrmsConcat :
  forall (fenv: funEnv) (env: valEnv) 
         (p1 p2 p3: AConfig Prms),
   PrmsClosure fenv env p1 p2 -> PrmsClosure fenv env p2 p3 ->
                                      PrmsClosure fenv env p1 p3.
Proof.
  intros.
  induction X.
  assumption.
  apply IHX in X0.
  econstructor.
  eassumption.
  assumption.
Defined.

Lemma RTClosConcat :
        forall (env: funEnv) (p1 p2 p3: AConfig Prog),
             RTClosure env p1 p2 -> RTClosure env p2 p3 ->
             RTClosure env p1 p3.
Proof.
  intros.
  induction X.
  assumption.
  apply IHX in X0.
  econstructor.
  eassumption.
  assumption.
Defined.

(****************************************************************)

(** big-step lifting of congruence rules *)

Lemma BindN_extended_congruence : 
   forall (fenv: funEnv) (env: valEnv)  
                          (n1 n2: W) (p1 p2 p3: Exp),
     EClosure fenv env (Conf Exp n1 p1) (Conf Exp n2 p2) ->
     EClosure fenv env (Conf Exp n1 (BindN p1 p3))
                            (Conf Exp n2 (BindN p2 p3)).
Proof.
  intros.
  dependent induction X.
  constructor.
  destruct p5.
  specialize (IHX state).
  specialize (IHX n2).
  specialize (IHX qq).
  specialize (IHX p2).
  econstructor.
  - instantiate (1:= Conf Exp state (BindN qq p3)).
    eapply BindN_Cg_EStep.
    assumption.
  - apply IHX.
    reflexivity.
    reflexivity.
Defined.    


Lemma BindMS_extended_congruence :
        forall (fenv fenvL fenv': funEnv) (env envL env': valEnv)
               (n1 n2: W) (e1 e2: Exp),
          fenv' = fenvL ++ fenv ->
          env' = envL ++ env -> 
          EClosure fenv' env' (Conf Exp n1 e1) (Conf Exp n2 e2) ->
          EClosure fenv env (Conf Exp n1 (BindMS fenvL envL e1))
                                 (Conf Exp n2 (BindMS fenvL envL e2)).
Proof.
  intros.
  dependent induction X.
  constructor.
  destruct p2.
  econstructor.
  - instantiate (1 := Conf Exp state (BindMS fenvL envL qq)).  
    econstructor.
    reflexivity.
    reflexivity.
    assumption.
  - eapply IHX.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
Defined.


Lemma BindS_extended_congruence :
   forall (fenv: funEnv) (env: valEnv)
      (n1 n2: W) (x: Id) (p1 p2 p3: Exp),
           EClosure fenv env (Conf Exp n1 p1) (Conf Exp n2 p2) ->
           EClosure fenv env (Conf Exp n1 (BindS x p1 p3))
                             (Conf Exp n2 (BindS x p2 p3)).
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
                           (n n': W) 
                           (f: Fun) (ps ps': Prms),
     PrmsClosure fenv env (Conf Prms n ps) (Conf Prms n' ps') ->
     EClosure fenv env (Conf Exp n (Apply (QF f) ps))
                            (Conf Exp n' (Apply (QF f) ps')).
Proof.
  intros.
  dependent induction X.
  constructor.
  destruct p2.
  econstructor.
  - econstructor.
    eassumption.
  - specialize (IHX state n' qq ps').
    eapply IHX. 
    reflexivity.
    reflexivity.
Defined.


Lemma Apply2_extended_congruence 
      (fenv: funEnv) (env: valEnv) (n n': W) (h h': QFun) (ps: Prms) : 
     QFClosure fenv (Conf QFun n h) (Conf QFun n' h') ->
     EClosure fenv env (Conf Exp n (Apply h ps))
                            (Conf Exp n' (Apply h' ps)).
Proof.
  intros.
  dependent induction X.
  constructor.
  econstructor.
  - econstructor.
    eassumption.
  - constructor.
Defined.  


Lemma IfThenElse_extended_congruence :
     forall (fenv: funEnv) (env: valEnv)
                           (n n': W) 
                           (e e' e1 e2: Exp),
     EClosure fenv env (Conf Exp n e) (Conf Exp n' e') ->
     EClosure fenv env (Conf Exp n
                                 (IfThenElse e e1 e2))
                            (Conf Exp n'
                                 (IfThenElse e' e1 e2)).
Proof.
  intros. 
  dependent induction X.
  constructor.
  intros.
  destruct p2.
  specialize (IHX state n' qq e' eq_refl eq_refl). 
  econstructor.
  - econstructor.
    eassumption.
  - assumption.
Defined.  


Lemma Pars_extended_congruence1 :
    forall (fenv: funEnv) (env: valEnv)
                   (n n': W) 
                   (es es': list Exp) (v: Value),
         PrmsClosure fenv env (Conf Prms n (PS es))
                                   (Conf Prms n' (PS es')) ->
         PrmsClosure fenv env (Conf Prms n (PS (Val v :: es)))
                                   (Conf Prms n' (PS (Val v :: es'))).  
Proof.
  intros.
  revert v.
  dependent induction X.
  - intros.
    constructor.
  - intros.
    destruct p2.
    destruct qq. 
    specialize (IHX state n' es0 es').
    specialize (IHX eq_refl eq_refl v).
    econstructor.
    econstructor.
    eassumption.
    assumption.
Defined.
  

Lemma Pars_extended_congruence2 :
    forall (fenv: funEnv) (env: valEnv)
           (n n': W) (es: list Exp) (e e': Exp),
         EClosure fenv env (Conf Exp n e)
                                (Conf Exp n' e') ->
         PrmsClosure fenv env (Conf Prms n (PS (e::es)))
                                   (Conf Prms n' (PS (e'::es))).  
  intros.
  revert es.
  dependent induction X.
  - constructor.
  - intros.
    destruct p2.
    specialize (IHX state n' qq e').
    specialize (IHX eq_refl eq_refl es).
    econstructor.
    econstructor.
    eassumption.
    assumption.
Defined.  
  

Lemma Pars_extended_congruence3 :
       forall (fenv: funEnv) (env: valEnv)
                   (n n': W) 
                   (es evs: list Exp) (vs: list Value),
         isValueList2T evs vs ->                             
         PrmsClosure fenv env (Conf Prms n (PS es))
                                   (Conf Prms n' (PS evs)) ->
         PrmsClosure fenv env (Conf Prms n (PS es))
                                   (Conf Prms n' (PS (map Val vs))).  
Proof.
  intros.
  inversion H; subst.
  inversion H; subst.
  assumption.
Defined.  


Lemma Pars_extended_congruence4 :
    forall (fenv: funEnv) (env: valEnv)
           (n n' n'': W) (es es': list Exp) (e: Exp) (v: Value),
         EClosure fenv env (Conf Exp n e)
                                (Conf Exp n' (Val v)) ->
         PrmsClosure fenv env (Conf Prms n' (PS es))
                                   (Conf Prms n'' (PS es')) ->  
         PrmsClosure fenv env (Conf Prms n (PS (e::es)))
                                   (Conf Prms n'' (PS (Val v::es'))).  
  intros.
  revert es es' X0.
  revert n''.
  dependent induction X.
  - intros.
    eapply PrmsConcat.
    econstructor.
    eapply Pars_extended_congruence1.
    assumption.
  - intros.
    destruct p2.
    specialize (IHX state n' qq v).
    specialize (IHX eq_refl eq_refl n'' es es' X0).
    econstructor.
    econstructor.
    eassumption.
    assumption.
Defined.  


Lemma Define_extended_congruence :
  forall (env1 env2: funEnv)
         (n1 n2: W) (x: Id) (f: Fun) (p1 p2: Prog),
             env2 = (x, f) :: env1 ->
             RTClosure env2 (Conf Prog n1 p1) (Conf Prog n2 p2) ->
             RTClosure env1 (Conf Prog n1 (define x f p1))
                                 (Conf Prog n2 (define x f p2)).
Proof.
  intros.
  dependent induction X.
  - constructor.
  - destruct p4.
    econstructor.
    + instantiate (1 := Conf Prog state (define x f qq)).  
      econstructor.
      reflexivity.
      assumption.
    + eapply IHX.
      reflexivity.
      reflexivity.
      reflexivity.
Defined.


(******************************************************************)

(** lemmas about parameters *)

Lemma PrmsStep_aux0 :
    forall (fenv: funEnv) (env: valEnv)
           (n n': W) (es es': list Exp),
         PrmsStep fenv env (Conf Prms n (PS es))
                     (Conf Prms n' (PS es')) ->
         length es = length es'.  
Proof.
  intros.
  dependent induction X.
  specialize (IHX n n' es0 es'0 eq_refl eq_refl).
  simpl.
  auto.
  auto.
Defined.  
 
Lemma PrmsClos_aux0 :
    forall (fenv: funEnv) (env: valEnv)
           (n n': W) (es es': list Exp),
         PrmsClosure fenv env (Conf Prms n (PS es))
                     (Conf Prms n' (PS es')) ->
         length es = length es'.  
Proof.
  intros.
  dependent induction X.
  auto.
  destruct p2.
  destruct qq.
  eapply PrmsStep_aux0 in p.
  specialize (IHX state n' es0 es' eq_refl eq_refl).
  rewrite <- p in IHX.
  auto.
Defined.  


Lemma PrmsClos_aux1 (fenv: funEnv) (env: valEnv)
                     (e: Exp) (v: Value) (es es': list Exp) (n: W)
      : {n' : W &
      PrmsClosure fenv env (Conf Prms n (PS (e :: es)))
                  (Conf Prms n' (PS (Val v :: es')))} ->
{n' : W &
      prod (EClosure fenv env (Conf Exp n e)
               (Conf Exp n' (Val v)))
            {n'' : W &
                  PrmsClosure fenv env (Conf Prms n' (PS es))
                                       (Conf Prms n'' (PS es'))} }.         
Proof.
  intros.
  destruct X as [n2 X].
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
    specialize (IHX e1 v es1 es' state n2 eq_refl eq_refl).
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



Lemma prmsAux1
      (ftenv: funTC) (tenv: valTC) (ps: Prms) (pt: PTyp) :  
  forall (fenv: funEnv) (env: valEnv),                      
    MatchEnvsT FunTyping fenv ftenv ->
    MatchEnvsT ValueTyping env tenv ->
    forall n: W, 
    (sigT (fun (n': W) => 
           sigT (fun (es: list Exp) => 
           prod (isValueListT es) 
           (prod (PrmsClosure fenv env (Conf Prms n ps)
                                            (Conf Prms n' (PS es))) 
                 (PrmsTyping ftenv tenv fenv (PS es) pt))))) ->       
    (sigT (fun (n': W) =>
           sigT (fun (vs: list Value) => 
           prod (PrmsClosure fenv env (Conf Prms n ps)
                                           (Conf Prms n' (PS (map Val vs)))) 
                (PrmsTyping emptyE emptyE emptyE (PS (map Val vs)) pt)))).
Proof.
  intros.
  destruct X1 as [n1 X1].
  destruct X1 as [es X1].
  destruct X1 as [X1 X2].
  destruct X2 as [X2 X3].
  exists n1.
  eapply isValueList22_T in X1.
  inversion X1.
  destruct X1 as [vs].
  constructor 1 with (x:=vs).
  split.
  - eapply PrmsConcat.
    eassumption.
    inversion i; subst.
    constructor.
  - destruct pt.
    inversion i; subst. 
    constructor.
    eapply matchListsAux1A.
    eassumption.
    inversion X3; subst.
    eassumption.
Defined.


Lemma NoPrmsStep (fenv: funEnv) (env: valEnv)
                  (n0 n1: W) (es1 es2: list Exp):
  PrmsStep fenv env (Conf Prms n0 (PS es1))
                      (Conf Prms n1 (PS es2)) ->
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


End Dynamic.

