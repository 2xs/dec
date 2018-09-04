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

Import ListNotations.

(** * DEC 2.0 language specification *)

(** Static semantics *)

Module StaticSem (IdT: ModTyp) <: ModTyp.

Module LangSpecL := LangSpec IdT.
Export LangSpecL.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.


(************************************************************************)

(** * Static semantics *)

(** Value and function typing *)

Definition VTyping (v: Value) (t: VTyp) : Prop :=
  valueVTyp v = t.                       

Definition sVTyping (T: Type) (v: T) (t: VTyp) : Prop :=
    sVTyp t = T. 

Definition FTyping (f: Fun) (ft: FTyp) : Prop :=
   funFTyp f = ft.


Lemma VTyping2sVTyp_lemma (v: Value) (t: VTyp) :
         VTyping v t -> sVTyp t.
  intros.
  destruct v.
  destruct v.
  unfold VTyping in H.
  rewrite <- H.
  simpl.
  exact v.
Defined.  

Definition VTyping2sVTyp {v: Value} {t: VTyp} : VTyping v t -> sVTyp t :=
 let (x, v0) as s return (VTyping s t -> sVTyp t) := v in
  match v0 as v1 return (VTyping (existT ValueI x v1) t -> sVTyp t) with
  | Cst _ v1 =>
      fun X1 : VTyping (existT ValueI x (Cst x v1)) t =>
      eq_rect (valueVTyp (existT ValueI x (Cst x v1)))
        (fun t0 : VTyp => sVTyp t0) v1 t X1
  end.

Definition VTyping_lemma {v: Value} {t: VTyp} : VTyping v t ->
                sigT (fun x : sVTyp t => v = cst t x). 
  intros.
  destruct v.
  destruct v.
  unfold VTyping in H.
  simpl in H.
  rewrite <- H.
  constructor 1 with (x:=v).
  auto.
Defined.  

  
(** Typing of identifiers *)

Definition IdTyping : valTC -> Id -> VTyp -> Prop := EnvrAssign. 

Definition IdFTyping : funTC -> Id -> FTyp -> Prop := EnvrAssign. 

Definition IdEnvTyping : valEnv -> Id -> VTyp -> Prop :=
  EnvrDAssign valueVTyp.

Definition IdFEnvTyping : funEnv -> Id -> FTyp -> Prop :=
  EnvrDAssign funFTyp.



(** Environment manipulation *)

(* value environments *)

Definition IdValue2IdVTyp (p: Id * Value) : Id * VTyp :=
    thicken Id valueVTyp p.
(*  (fst p, valueVTyp (snd p)). *)

Definition valEnv2valTC (env: valEnv) : valTC :=
    map (thicken Id valueVTyp) env.
(*  map IdValue2IdVTyp env. *)

Definition EnvTyping (env: valEnv) (tenv: valTC) : Prop :=
    MatchEnvs Id valueVTyp env tenv.
(*  tenv = valEnv2valTC env. *)

Definition VIdVTyp (env: valEnv) (x: Id) : option VTyp :=
  option_map valueVTyp (findE env x). 

(** function environments *)

Definition IdFun2IdFTyp (p: Id * Fun) : Id * FTyp :=
    thicken Id funFTyp p.
(*  (fst p, funFTyp (snd p)). *)

Definition funEnv2funTC (env: funEnv) : funTC :=
    map (thicken Id funFTyp) env.
(*  map IdFun2IdFTyp env. *)

Definition FEnvTyping (env: funEnv) (tenv: funTC) : Prop :=
    MatchEnvs Id funFTyp env tenv.
(*  tenv = funEnv2funTC env. *)

Definition FIdFTyp (env: funEnv) (x: Id) : option FTyp :=
  option_map funFTyp (findE env x). 


Inductive Maybe : VTyp -> option VTyp -> Type :=
| Maybe_Some : forall t: VTyp, Maybe t (Some t)
| Maybe_None : forall t: VTyp, Maybe t None.                                     

Inductive Pure : Exp -> Type :=
| Pure_Val : forall v: Value, Pure (Val v)
| Pure_Var : forall x: Id, Pure (Var x).


Inductive ExpTyping : (** Expressions *)
       funTC -> valTC -> Exp -> VTyp -> Type :=
(** - lifting of values *)                        
  | Val_Typing : forall (ftenv: funTC) (tenv: valTC)
                        (v: Value) (t: VTyp), 
                       VTyping v t -> 
                       ExpTyping ftenv tenv (Val v) t
(** - tagged lifting of quasi-values *)                               
  | Var_Typing : forall (ftenv: funTC) (tenv: valTC)
                        (x: Id) (t: VTyp),
                       IdTyping tenv x t ->  
                       ExpTyping ftenv tenv (Var x) t
(** - sequencing *)                                 
  | BindN_Typing : forall (ftenv: funTC) (tenv: valTC) 
                          (e1 e2: Exp) (t1 t2: VTyp), 
                       ExpTyping ftenv tenv e1 t1 ->
                       ExpTyping ftenv tenv e2 t2 ->
                       ExpTyping ftenv tenv (BindN e1 e2) t2
(** - let-style binding of identifiers *)
  | BindS_Typing : forall (ftenv: funTC) (tenv tenv': valTC)
                            (x: Id) (e1 e2: Exp) (t1 t2: VTyp)
                            (m: option VTyp),
                       Maybe t1 m -> 
                       tenv' = (x, t1) :: tenv ->   
                       ExpTyping ftenv tenv e1 t1 ->
                       ExpTyping ftenv tenv' e2 t2 ->
                       ExpTyping ftenv tenv
                                 (BindS x m e1 e2) t2
(** - binding by local environments *)                                 
  | BindMS_Typing : forall (ftenv: funTC)
                           (tenv tenv0 tenv1: valTC)
                           (env0: valEnv) 
                           (e: Exp) (t: VTyp),
                       EnvTyping env0 tenv0 -> 
                       tenv1 = tenv0 ++ tenv ->                       
                       ExpTyping ftenv tenv1 e t ->
                       ExpTyping ftenv tenv (BindMS env0 e) t
(** - conditional expression *)                                 
  | IfThenElse_Typing : forall (ftenv: funTC) (tenv: valTC)
                               (e1 e2 e3: Exp) (t: VTyp),
             ExpTyping ftenv tenv e1 Bool ->
             ExpTyping ftenv tenv e2 t ->
             ExpTyping ftenv tenv e3 t ->
             ExpTyping ftenv tenv (IfThenElse e1 e2 e3) t
(** - function application *)                                 
  | Apply_Typing : forall (ftenv: funTC) (tenv: valTC)  
                          (x: Id) (e: Exp)
                          (ps: Prms) (pt: PTyp) (t: VTyp),
              Pure e -> 
              IdFTyping ftenv x (FT pt t) -> 
              PrmsTyping ftenv tenv ps pt ->
              ExpTyping ftenv tenv e Nat ->  
              ExpTyping ftenv tenv (Apply x ps e) t
(** - function call *)
  | Call_Typing : forall (ftenv: funTC) (tenv: valTC)  
                         (x: Id) 
                         (ls: list Exp) (pt: PTyp) (t: VTyp),
              IdFTyping ftenv x (FT pt t) -> 
              PrmsTyping ftenv tenv (PS ls) pt ->
              ExpTyping ftenv tenv (Call x (PS ls)) t
(** - call to a generic effect (external function) *)       
  | Modify_Typing : forall (ftenv: funTC) (tenv: valTC) 
                           (t1 t2: VTyp) 
                           (XF: XFun t1 t2) (e: Exp),
              ExpTyping ftenv tenv e t1 ->  
              ExpTyping ftenv tenv (Modify t1 t2 XF e) t2
with PrmsTyping : (** - Parameters *)
         funTC -> valTC -> Prms -> PTyp -> Type :=
| PSNil_Typing: forall (ftenv: funTC) (tenv: valTC),  
      PrmsTyping ftenv tenv (PS nil) (PT nil)
| PSCons_Typing: forall (ftenv: funTC) (tenv: valTC)
                    (e: Exp) (t: VTyp)    
                    (es: list Exp) (ts: list VTyp),
    ExpTyping ftenv tenv e t ->
    PrmsTyping ftenv tenv (PS es) (PT ts) ->    
    PrmsTyping ftenv tenv (PS (e::es)) (PT (t::ts)).


Scheme ExpTyping_mut := Induction for ExpTyping Sort Type
with PrmsTyping_mut := Induction for PrmsTyping Sort Type.




(** function is well typed wrt to environment *)

Definition FunWT (ftenv: funTC) (f: Fun) : Type :=
    match f with 
      | FC tenv v e => ExpTyping ftenv tenv e (projT1 v)
    end.                            


(** the function environment is well typed *)
Definition FEnvWT (fenv: funEnv) : Type :=
  forall (ftenv: funTC),
   FEnvTyping fenv ftenv ->
   forall (x: Id) (f: Fun),
    findE fenv x = Some f ->
    FunWT ftenv f.
    

Definition ExpWTyping (fenv: funEnv) (env: valEnv)
           (e: Exp) (t: VTyp) : Type :=
  (forall (ftenv: funTC) (tenv: valTC),
    EnvTyping env tenv ->
    FEnvTyping fenv ftenv ->
    FEnvWT fenv -> 
    ExpTyping ftenv tenv e t).


Definition PrmsWTyping (fenv: funEnv) (env: valEnv)
           (ps: Prms) (pt: PTyp) : Type :=
  (forall (ftenv: funTC) (tenv: valTC),
    EnvTyping env tenv ->
    FEnvTyping fenv ftenv ->
    FEnvWT fenv -> 
    PrmsTyping ftenv tenv ps pt).


(********************************************************************)

(** function is well typed *)

Definition FunWT1 (f: Fun) : Type :=
    match f with 
      | FC tenv v e => VTyping v (projT1 v)
    end.                            

Lemma FunWT1_prop (f: Fun) :
  FunWT1 f.
  unfold FunWT1.
  destruct f.
  destruct v.
  constructor.
Defined.  


(********************************************************************)

(** Value lists in Prop *)

Inductive isValue (e: Exp) : Prop :=
  IsValue : forall (v: Value), e = Val v -> isValue e.

Definition isValueList (ls : list Exp) : Prop :=
Forall isValue ls.

Inductive isValueList2  
  (els : list Exp) (vls : list Value) : Prop :=
IsValueList2 :  els = map Val vls -> isValueList2 els vls.

(** Value lists in Type *)

Definition isValueT (e: Exp) : Type :=
  sigT (fun (v: Value) => e = Val v).

Definition isValueListT (ls : list Exp) : Type :=
ForallT isValueT ls.

Definition isValueList2T  
  (els : list Exp) (vls : list Value) : Type :=
  els = map Val vls.

(***************************************************************)

(** lemmas about value lists *)

Lemma forallValues (vs: list Value) : ForallT isValueT (map Val vs).
  induction vs.
  simpl.
  constructor.
  simpl.
  constructor.
  econstructor.
  reflexivity.
  assumption.
Defined.  

Lemma isValueList2IsValueT (els : list Exp) (vls : list Value) :
  isValueList2T els vls -> isValueListT els.
Proof.
  unfold isValueListT, isValueList2T.
  intros.
  inversion H; subst.
  induction vls.
  simpl.
  constructor.
  constructor.
  econstructor.
  reflexivity.
  eapply IHvls.
  reflexivity.
Defined.  

Lemma isValueList22_T (ls : list Exp) : isValueListT ls ->
             sigT (fun vs => isValueList2T ls vs). 
Proof.
  induction ls.
  intros.
  exists nil.  
  constructor.
  simpl.
  intros.
  assert (isValueListT ls).
  inversion X; subst.
  assumption.
  inversion X; subst.
  inversion X1; subst. 
  eapply IHls in X0.
  destruct X0 as [vs1 X0].
  constructor 1 with (x := x::vs1).
  inversion X0; subst.
  reflexivity.
Defined.  

Lemma sameLengthVV (es : list Exp) (vs : list Value) : 
  isValueList2 es vs -> length es = length vs.
Proof.
intros.  
inversion H; subst.
clear H.
induction vs.
auto.
simpl.
rewrite IHvs.
reflexivity.
Defined.

Lemma sameLengthVV_T (es : list Exp) (vs : list Value) : 
  isValueList2T es vs -> length es = length vs.
Proof.
  unfold isValueList2T.
intros.  
inversion H; subst.
induction vs.
auto.
simpl.
rewrite IHvs.
reflexivity.
reflexivity.
Defined.


Lemma mapEq (ls1 ls2: list Value) :
   map Val ls1 = map Val ls2 -> ls1 = ls2. 
Proof.
  revert ls2.
  induction ls1.
  induction ls2.
  auto.
  intros.
  simpl in H.
  inversion H.
  intros.
  destruct ls2.
  simpl in H.
  inversion H.
  simpl in H.
  inversion H; subst.
  assert (ls1 = ls2).
  eapply IHls1.
  assumption.
  rewrite H0.
  auto.
Defined.  


Lemma vlaMapEq (vs1 vs2: list Value) : map Val vs1 = map Val vs2 -> vs1 = vs2.
Proof.
  intros.
  revert H.
  revert vs2.
  induction vs1.
  intro vs2.
  destruct vs2.
  auto.
  intros.
  simpl in H.
  inversion H.
  intros.
  destruct vs2.
  simpl in H.
  inversion H.
  simpl in H.
  inversion H; subst.
  eapply IHvs1 in H2.
  rewrite H2.
  auto.
Defined.

(** lemmas about parameters *)

Lemma PrmsArity_lemma (ftenv: funTC) (tenv: valTC)
                       (es: list Exp) (ts: list VTyp) : 
      PrmsTyping ftenv tenv (PS es) (PT ts) ->
      length es = length ts.
Proof.
  intros.
  dependent induction X.
  reflexivity. 
  simpl.
  auto.
Defined.  
  
Lemma FunArity_lemma (ft: FTyp) (f: Fun) :
  funFTyp f = ft -> 
  length (funValTC f) = length (ptypLS (ftypPT ft)).
Proof.
  unfold funFTyp, funValTC, ptypLS, ftypPT.
  destruct f.
  destruct ft.
  intros.
  inversion H; subst.
  rewrite map_length.
  auto.
Defined.  
  

(* lemmas about function typing *)

Lemma FEnvWT_nil_lemma : FEnvWT nil.
  unfold FEnvWT.
  intros.
  inversion H0.
Defined.  

Lemma funFTyp_lemma (f: Fun) (pt: PTyp) (t: VTyp) :
      funFTyp f = FT pt t ->
      funVTyp f = t.
      destruct f.
      unfold funFTyp.
      unfold funVTyp.
      intros.
      inversion H; subst.
      auto.
Defined.


Lemma FunTyping0_lemma (f: Fun) (v: Value) (t: VTyp) :
    v = fun0Exp f ->
    t = funVTyp f -> 
    VTyping v t.
  intros.
  destruct f.
  inversion H0; subst.
  simpl.
  reflexivity.
Defined.
  

Lemma FunTypingS_lemma (ftenv: funTC) (fenv: funEnv) (tenv: valTC)
      (x: Id) (f: Fun) (e: Exp) (t: VTyp) :
    FEnvWT fenv ->
    FEnvTyping fenv ftenv ->
    findE fenv x = Some f ->
    tenv = funValTC f ->
    e = funSExp f ->
    t = funVTyp f -> 
    ExpTyping ftenv tenv e t.
  intros.
  specialize (X ftenv H x f H0).
  destruct f.
  simpl in H3.
  destruct v.
  simpl in H3.
  inversion H3; subst.
  simpl in *.
  assumption.
Defined.  


Lemma VTypingFun0_lemma (ftenv: funTC) (fenv: funEnv)
      (x: Id) (f: Fun) (v: Value) (t: VTyp) :
    FEnvWT fenv ->
    FEnvTyping fenv ftenv ->
    findE fenv x = Some f ->
    v = fun0Exp f ->
    t = funVTyp f -> 
    VTyping (fun0Exp f) t.
  intros.
  destruct f.
  simpl.
  destruct v.
  destruct v0.
  simpl in H1.
  inversion H1; subst.
  unfold VTyping.
  unfold valueVTyp.
  simpl.
  reflexivity.
Defined.  


Lemma mkVEnv_typing_lemma (f: Fun) (pt: PTyp) (t: VTyp) (vs: list Value) :
  funFTyp f = FT pt t ->
  PrmsTyping emptyE emptyE (PS (map Val vs)) pt ->
  EnvTyping (mkVEnv (funValTC f) vs) (funValTC f).
  destruct f.
  unfold mkVEnv.
  unfold funValTC.
  unfold funFTyp.
  intros.
  inversion H; subst; clear H.
  
  revert X.
  revert tenv.
  dependent induction vs.
  intros.
  assert (tenv = nil).
  destruct tenv.
  auto.
  simpl in X.
  inversion X.
  rewrite H.
  simpl.
  constructor.

  intros.
  destruct tenv.
  simpl in *.
  inversion X.
  simpl in *.
  inversion X; subst.
  specialize (IHvs tenv X1).
  unfold EnvTyping.
  unfold MatchEnvs.
  simpl.
  destruct p.
  simpl in *.
  inversion X0; subst.
  inversion H2; subst.
  simpl in *.
  inversion IHvs.
  rewrite H at 1.
  auto.
Defined.


Lemma mkVEnv_typing_lemma1 (ftenv: funTC) (tenv: valTC)
      (f: Fun) (pt: PTyp) (t: VTyp) (vs: list Value) :
  funFTyp f = FT pt t ->
  PrmsTyping ftenv tenv (PS (map Val vs)) pt ->
  EnvTyping (mkVEnv (funValTC f) vs) (funValTC f).
  destruct f.
  unfold mkVEnv.
  unfold funValTC.
  unfold funFTyp.
  intros.
  inversion H; subst; clear H.

  dependent induction X.
  symmetry in x0.
  eapply map_eq_nil in x0.
  inversion x0; subst.
  clear H.
  symmetry in x.
  eapply map_eq_nil in x.
  inversion x; subst.
  clear H.
  simpl.
  constructor.
  destruct vs.
  simpl in x0.
  inversion x0.
  destruct tenv0.
  simpl in x.
  inversion x.
  simpl in *.
  specialize (IHX tenv0 vs).
  inversion x0; subst.
  inversion x; subst.
  specialize (IHX eq_refl eq_refl).
  destruct p.
  simpl in *.
  unfold EnvTyping.
  unfold MatchEnvs.
  simpl.
  unfold thicken.
  simpl.
  inversion e1; subst.
  inversion H2; subst.
  inversion IHX; subst.
  unfold thicken.
  rewrite H at 1.
  reflexivity.
Defined.  


Lemma mkVEnv_typing_lemma2 (ftenv: funTC) (tenv tenv0: valTC)
      (vs: list Value) :
  PrmsTyping ftenv tenv (PS (map Val vs)) (PT (map snd tenv0)) ->
  EnvTyping (mkVEnv tenv0 vs) tenv0.
  unfold mkVEnv.
  intros.
(*  
  unfold EnvTyping.
  unfold MatchEnvs.
*)
  dependent induction X.
  symmetry in x0.
  eapply map_eq_nil in x0.
  inversion x0; subst.
  clear H.
  symmetry in x.
  eapply map_eq_nil in x.
  inversion x; subst.
  clear H.
  simpl.
  constructor.
  destruct vs.
  simpl in x0.
  inversion x0.
  destruct tenv0.
  simpl in x.
  inversion x.
  simpl in *.
  specialize (IHX tenv0 vs).
  inversion x0; subst.
  inversion x; subst.
  specialize (IHX eq_refl eq_refl).
  destruct p.
  simpl in *.
  unfold EnvTyping.
  unfold MatchEnvs.
  simpl.
  unfold thicken.
  simpl.
  inversion e0; subst.
  inversion H2; subst.
  inversion IHX; subst.
  unfold thicken.
  rewrite H at 1.
  reflexivity.
Defined.  


(*******************************************************************)


Lemma mkVEnv_lemma1 (ftenv: funTC) (tenv: valTC)
          (f: Fun) (vs: list Value) :
  PrmsTyping ftenv tenv (PS (map Val vs))
             (PT (map snd (funValTC f))) ->  
  EnvTyping (mkVEnv (funValTC f) vs) (funValTC f).
  destruct f.
  simpl.
  intros.
  dependent induction X.
  symmetry in x0.
  eapply map_eq_nil in x0.
  symmetry in x.
  eapply map_eq_nil in x.
  inversion x0; subst.
  unfold mkVEnv.
  simpl.
  reflexivity.
  destruct vs.
  simpl in x0.
  inversion x0.
  destruct tenv0.
  simpl in x.
  inversion x.
  simpl in x0, x.
  inversion x0; subst.
  inversion x; subst.
  specialize (IHX tenv0 vs eq_refl eq_refl).
  unfold mkVEnv.
  simpl.
  unfold EnvTyping.
  unfold MatchEnvs.
  simpl.
  destruct p.
  simpl.
  inversion e1; subst.
  unfold VTyping in H2.
  simpl in H2.
  unfold thicken.
  simpl.
  rewrite H2.
  f_equal.
  exact IHX.
Defined.  

Lemma mkVEnv_lemma2a (ftenv: funTC) (tenv tenv0: valTC) (vs: list Value) :
  PrmsTyping ftenv tenv (PS (map Val vs)) (PT (map snd tenv0)) ->
  valEnv2valTC (mkVEnv tenv0 vs) = tenv0.
  intros.
  unfold valEnv2valTC.
  unfold mkVEnv.
  dependent induction X.
  symmetry in x0.
  eapply map_eq_nil in x0.
  symmetry in x.
  eapply map_eq_nil in x.
  inversion x0; subst.
  simpl.
  reflexivity.
  destruct vs.
  simpl in x0.
  inversion x0.
  destruct tenv0.
  simpl in x.
  inversion x.
  simpl in x0, x.
  inversion x0; subst.
  inversion x; subst.
  specialize (IHX tenv0 vs eq_refl eq_refl).
  destruct p.
  simpl.
  inversion e0; subst.
  unfold VTyping in H2.
  simpl in H2.
  unfold thicken.
  simpl.
  rewrite H2.
  f_equal.
  exact IHX.
Defined.  


Lemma mkVEnv_lemma2 (ftenv: funTC) (tenv tenv0: valTC)
              (vs: list Value) :
  PrmsTyping ftenv tenv (PS (map Val vs))
             (PT (map snd tenv0)) ->  
  EnvTyping (mkVEnv tenv0 vs) tenv0.
  simpl.
  intros.
  dependent induction X.
  symmetry in x0.
  eapply map_eq_nil in x0.
  symmetry in x.
  eapply map_eq_nil in x.
  inversion x0; subst.
  unfold mkVEnv.
  simpl.
  reflexivity.
  destruct vs.
  simpl in x0.
  inversion x0.
  destruct tenv0.
  simpl in x.
  inversion x.
  simpl in x0, x.
  inversion x0; subst.
  inversion x; subst.
  specialize (IHX tenv0 vs eq_refl eq_refl).
  unfold mkVEnv.
  simpl.
  unfold EnvTyping.
  unfold MatchEnvs.
  simpl.
  destruct p.
  simpl.
  inversion e0; subst.
  unfold VTyping in H2.
  simpl in H2.
  unfold thicken.
  simpl.
  rewrite H2.
  f_equal.
  exact IHX.
Defined.  

Lemma prms_helper1 (ftenv: funTC) (tenv tenv0: valTC) (vs: list Value) :
    PrmsTyping ftenv tenv (PS (map Val vs)) (PT (map snd tenv0)) -> 
    ( valEnv2valTC (interleave (map fst tenv0) vs) = tenv0 ).
    intros.
    dependent induction X.
    symmetry in x0.
    eapply map_eq_nil in x0.
    inversion x0; subst.
    symmetry in x.
    eapply map_eq_nil in x.
    inversion x; subst.
    simpl.
    reflexivity.
    destruct vs.
    simpl in x0.
    inversion x0.
    destruct tenv0.
    simpl in x.
    inversion x.
    simpl in x0, x.
    inversion x0; subst.
    inversion x; subst.
    clear x x0.
    simpl in *.
    destruct p.
    unfold thicken.
    simpl.
    simpl in e0.
    destruct v.
    destruct v.
    destruct v0.
    simpl in *.
    inversion e0; subst.
    inversion H2; subst.
    unfold valueVTyp in H.
    simpl in H.
    inversion H; subst.
    f_equal.
    eapply IHX.
    reflexivity.
    reflexivity.
Defined.    
     

(********************************************************************)

Lemma find_simpl1 (x: Id) (t: VTyp) :
    forall (env: valEnv), findE ((x, t) :: valEnv2valTC env) x =
                          Some t.
  intros.
  simpl.
  destruct (IdT.IdEqDec x x).
  auto.
  intuition.
Defined.


Lemma lengthVal (ls: list Value) : length (map Val ls) = length ls.   
  induction ls.
  simpl.
  auto.
  simpl in *.
  rewrite IHls.
  auto.
Defined.  


(*********************************************************************)

(** lemmas about parameter typing *)

Definition vlsTyping (vs: list Value) (pt: list VTyp) : Type :=
           Forall2T VTyping vs pt.


Lemma prmsTypingAux_T (fps : valTC) (vls : list Value)
                       (h: length fps = length vls):
          vlsTyping vls (map snd fps) ->
                         MatchEnvsT VTyping (mkVEnv fps vls) fps.
Proof.
  unfold mkVEnv.
  intros.
  apply prmsTypingAux2_T.
  auto.
  eapply prmsTypingAux1_T.
  auto.
  auto.
Defined.



Lemma Exp2ValueTyping 
      (ftenv: funTC) (tenv: valTC) 
      (v: Value) (t: VTyp) :
  ExpTyping ftenv tenv (Val v) t ->
  VTyping v t.
Proof.
  intros.
  inversion X; subst.
  exact H2.
Defined.

Lemma Exp2ValueTypingA 
      (ftenv: funTC) (tenv: valTC) 
      (v: Value) (t: VTyp) :
  ExpTyping ftenv tenv (Val v) t ->
  ExpTyping emptyE emptyE (Val v) t.
Proof.
intro.
constructor.
eapply Exp2ValueTyping.
eassumption.
Defined.


Lemma Value2ExpTyping 
      (ftenv: funTC) (tenv: valTC) 
      (v: Value) (t: VTyp) :
  VTyping v t ->
  ExpTyping ftenv tenv (Val v) t.
Proof.
  intros.
  inversion H; subst.
  constructor.
  exact H.
Defined.  


Lemma prmsTypingAux01_T 
      (ftenv: funTC) (tenv: valTC)
      (vs: list Value) (ts: list VTyp) :
          vlsTyping vs ts ->
          PrmsTyping ftenv tenv (PS (map Val vs)) (PT ts).
Proof.
  unfold vlsTyping.
  intros.
  induction X.
  constructor.
  constructor.
  constructor.
  exact r.
  exact IHX.
Defined.


Lemma matchListsAux02_T1 
      (ftenv: funTC) (tenv: valTC) 
                       (ts: list VTyp)
                       (es : list Exp) (vs : list Value) : 
  isValueList2T es vs -> 
  PrmsTyping ftenv tenv (PS es) (PT ts) -> 
  vlsTyping vs ts.
Proof.
  unfold vlsTyping.
  unfold isValueList2T.
  intros.
  inversion H; subst.
  clear H0.
  dependent induction X.
  symmetry in x.
  eapply map_eq_nil in x.
  rewrite x.
  constructor.
  destruct vs.
  simpl in x.
  inversion x.
  simpl in x.
  inversion x; subst. 
  constructor.
  inversion e0; subst.
  exact H2.
  eapply IHX.
  reflexivity.
  reflexivity.
Defined.  


Program Definition matchListsAux02_T 
      (ftenv: funTC) (tenv: valTC) 
                       (ts: list VTyp)
                       (es : list Exp) (vs : list Value) : 
  isValueList2T es vs -> 
  PrmsTyping ftenv tenv (PS es) (PT ts) -> 
  vlsTyping vs ts := _.

Next Obligation.
  unfold vlsTyping.
  unfold isValueList2T in X.
  rewrite X in *.
  clear X.
  clear es.
  revert X0.
  revert ts.
  induction vs.
  intros.
  inversion X0; subst.
  constructor.
  intros.
  inversion X0; subst.
  econstructor.
  inversion X; subst.
  exact H2.
  eapply IHvs.
  exact X1.
Defined.  
  
(*********************************************************************)

Lemma prod_eq {T1 T2 T3 T4: Type} (te1: T1 = T2) (te2: T3 = T4) :
  T1 * T3 = T2 * T4.
  rewrite te1.
  rewrite te2.
  reflexivity.
Defined.  

End StaticSem.


(*

Inductive Pure : Exp -> Type :=
| Pure_Val : forall v: Value, Pure (Val v)
| Pure_Var : forall x: Id, Pure (Var x)
| Pure_IfThenElse : forall (e1 e2 e3: Exp),
    Pure e1 -> Pure e2 -> Pure e3 -> Pure (IfThenElse e1 e2 e3).

Definition IdCEnvTyping : tfcEnv -> Id -> FTyp -> Type :=
  EnvrDAssign snd.

Definition IdCEnvNaming : tfcEnv -> Id -> Id -> Type :=
  EnvrDAssign (fun x => fst (fst x)).

Definition IdCEnvFuelling : tfcEnv -> Id -> nat -> Type :=
  EnvrDAssign (fun x => snd (fst x)).
*)

(** typed call environments *)
(*
Definition IdCall2IdFTyp (p: Id * (Id * nat * FTyp)) : Id * FTyp :=
  (fst p, snd (snd p)).

Definition tfcEnv2funTC (env: tfcEnv) : funTC :=
  map IdCall2IdFTyp env.

Definition CEnvTyping (env: tfcEnv) (tenv: funTC) : Type :=
  tenv = tfcEnv2funTC env.

Definition CIdFTyp (env: tfcEnv) (x: Id) : option FTyp :=
  option_map snd (findE env x). 
*)


(* relationally create a typed call 
   from a local name assignment, relying on a function environment 
   and a fuel value *)
(*
Inductive lfun2fcall (fenv: funEnv) : nat -> (Id * Id) ->  
                      (Id * (Id * nat * FTyp)) -> Type := 
| lfun2fcall_C : forall (x1 x2: Id)
                       (lfs: lfEnv) (tenv: valTC) (t: VTyp) 
                       (e0 e1: Exp)
                       (pt: PTyp) (n: nat) 
                       (fc: Id * (Id * nat * FTyp)),
    findE fenv x2 = (Some (FC lfs tenv t e0 e1)) ->
    pt = PT (map snd tenv) -> 
    lfun2fcall fenv n (x1, x2) (x1, (x2, n, FT pt t)).
*)

(* relationally create a typed call environment 
   from a local name environment, relying on a function environment 
   and a fuel value *) 
(*
Definition lfEnv2tfcEnv (fenv: funEnv) (n: nat)
                        (lenv: lfEnv) (cenv: tfcEnv) : Type :=
  Forall2T (lfun2fcall fenv n) lenv cenv.
*)
(*
Definition lfEnv2tfcEnvPM (fenv: funEnv) (n: nat)
           (lenv: lfEnv) (cenv: tfcEnv) : Type :=
  match n with
  | 0 => unit  
  | S n' => Forall2T (lfun2fcall fenv n') lenv cenv
  end.                   
*)

(*
(* Id1-Fun pair, Id2-Bound pair and Id2-Call pair agree  *)
Inductive Agree_Fun_LBound_Call : (Id * Fun) -> (Id * (Id * nat)) ->  
                      (Id * (Id * nat * FTyp)) -> Type := 
| Agree_Fun_LBound_Call_C : forall (f: Fun) (ft: FTyp)
                                   (x1 x2: Id) (n: nat),
    ft = funFTyp f -> 
    Agree_Fun_LBound_Call (x1, f) (x2, (x1, n)) (x2, (x1, n, ft)).
(*
| Agree_Fun_Bound_Call_C : forall (x1 x2: Id) (f: Fun)
                     (lfs: lfEnv) (tenv: valTC) (t: VTyp) (g: Tag)
                     (e0 e1: Exp)
                     (pt: PTyp) (n: nat),
    f = FC lfs tenv t g e0 e1 ->
    pt = PT (map snd tenv) -> 
    Agree_Fun_Bound_Call (x1, f) (x2, (x1, n)) (x2, (x1, n, FT pt t g)).
*)

Definition EnvAgree_Fun_LBound_Call
           (fenv: funEnv) (cenv: fcEnv) (tcenv: tfcEnv) :
  Type :=
  Forall3T Agree_Fun_LBound_Call fenv cenv tcenv.


Inductive Agree_Fun_GBound_Call : (Id * Fun) -> (Id * nat) ->  
                      (Id * (Id * nat * FTyp)) -> Type := 
| Agree_Fun_GBound_Call_C : forall (f: Fun) (ft: FTyp)
                                   (x1 x2: Id) (n: nat),
    ft = funFTyp f -> 
    Agree_Fun_GBound_Call (x1, f) (x1, n) (x2, (x1, n, ft)).

Definition EnvAgree_Fun_GBound_Call
           (fenv: funEnv) (benv: list (Id * nat)) (tcenv: tfcEnv) :
  Type :=
  Forall3T Agree_Fun_GBound_Call fenv benv tcenv.


Inductive Agree_Fun_Call : (Id * Fun) ->   
                      (Id * (Id * nat * FTyp)) -> Type := 
| Agree_Fun_Call_C : forall (f: Fun) (ft: FTyp)
                            (x1 x2: Id) (n: nat),
    ft = funFTyp f -> 
    Agree_Fun_Call (x1, f) (x2, (x1, n, ft)).

Definition EnvAgree_Fun_Call
           (fenv: funEnv) (tcenv: tfcEnv) :
  Type :=
  Forall2T Agree_Fun_Call fenv tcenv.


Definition ExpTTyping (cenv: tfcEnv) (env: valEnv)
                      (e: Exp) (t: VTyp) : Type :=
forall (ftenv: funTC) (tenv: valTC),    
  CEnvTyping cenv ftenv ->
  EnvTyping env tenv -> 
  ExpTyping ftenv tenv e t.

Definition PrmsTTyping (cenv: tfcEnv) (env: valEnv) 
                       (ps: Prms) (pt: PTyp) : Type :=
forall (ftenv: funTC) (tenv: valTC),    
  CEnvTyping cenv ftenv ->  
  EnvTyping env tenv -> 
  PrmsTyping ftenv tenv ps pt.
*)

(*
Inductive FEnvWT_Strong (fenv: funEnv) : Type :=
| FEnvWT_C : forall (x: Id) (f: Fun),
    findE fenv x = Some f -> 
    forall (lenv: lfEnv) (tenv: valTC) (t: VTyp) (g: Tag)
           (e0 e1: Exp),
       f = FC lenv tenv t g e0 e1 ->
       ExpTyping nil tenv e0 t ->
       (forall (n: nat) (cenv: tfcEnv) (ftenv: funTC),
           lfEnv2tfcEnvPM fenv g n lenv cenv ->
           (match n with
            | 0 => (unit: Type)
            | S n' => CEnvTyping cenv ftenv
            end) ->         
           (match n with
            | 0 => (unit: Type)
            | S n' => ExpTyping ftenv tenv e1 t
            end)) ->
  FEnvWT fenv.    
*)
(*
Inductive lfun2fcall (fenv: funEnv) : Tag -> nat -> (Id * Id) ->  
                      (Id * (Id * nat * FTyp)) -> Type := 
| lfun2fcallC : forall (x1 x2: Id)
                       (lfs: lfEnv) (tenv: valTC) (t: VTyp) (g: Tag)
                       (e0 e1: Exp)
                       (n: nat) (pt: PTyp)
                       (fc: Id * (Id * nat * Tag * FTyp)),
    findE fenv x2 = (Some (FC lfs tenv t g e0 e1)) ->
    pt = PT (map snd tenv) -> 
    lfun2fcall fenv II n (x1, x2) (x1, (x2, n, FT pt t g)).
                
    
Definition lfEnv2tfcEnv (fenv: funEnv) (g: Tag) (n: nat)
                        (lenv: lfEnv) (cenv: tfcEnv) : Type :=
  Forall2T (lfun2fcall fenv g n) lenv cenv.
*)

(*
(* WRONG!
the keys of ftenv (function variables) should not be those of fenv 
(function names) 
*)
Inductive FEnvWT_Weak (fenv: funEnv) : Type :=
| FEnvWT_WC : forall (x: Id) (f: Fun),
    findE fenv x = Some f -> 
    forall (lenv: lfEnv) (tenv: valTC) (t: VTyp) (g: Tag)
           (e0 e1: Exp),
       f = FC lenv tenv t g e0 e1 ->
       ExpTyping nil tenv e0 t ->
       (forall ftenv: funTC,
           FEnvTyping fenv ftenv ->
           ExpTyping ftenv tenv e1 t) ->
  FEnvWT_Weak fenv.    
*)

(*
(** Typing of function environments *)

Definition FEnvTyping : funEnv -> funTC -> Type :=
    MatchEnvsT FunTyping.


(** Typing of top-level programs *)

Inductive ProgTyping : 
    funTC -> funEnv -> Prog -> VTyp -> Type := 
| Prog_Typing : forall (ftenv: funTC) (fenv: funEnv) (e: Exp) (t: VTyp),
                   MatchEnvsT FunTyping fenv ftenv -> 
                   ProgTyping ftenv fenv (prog e) t
| Define_Typing : forall (ftenv ftenv': funTC) (fenv fenv': funEnv)   
                         (x: Id) (f: Fun) (p: Prog)
                         (ft: FTyp) (t: VTyp), 
      MatchEnvsT FunTyping fenv ftenv -> 
      ftenv' = (x, ft) :: ftenv -> 
      fenv' = (x, f) :: fenv -> 
      QFunTyping ftenv fenv (QF f) ft ->
      ProgTyping ftenv' fenv' p t ->
      ProgTyping ftenv fenv (define x f p) t.
*)





