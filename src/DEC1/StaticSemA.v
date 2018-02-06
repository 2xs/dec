(* DEC1 language development.
   Paolo Torrini, with David Nowak 
   Universite' Lille-1 - CRIStAL-CNRS
*)
(* language syntax and static semantics *)

Require Export EnvLibA.
Require Export RelLibA.

Require Export Basics.
Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Export IdModTypeA. 

Import ListNotations.

Module Static (IdT: IdModType) <: IdModType.
Export IdT.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

  
(** generic effect record *)

Record XFun (T1 T2: Type) : Type := {
    b_mod : W -> T1 -> prod W T2 ;
    b_exec : W -> T1 -> W := fun state input => fst (b_mod state input) ;
    b_eval : W -> T1 -> T2 := fun state input => snd (b_mod state input)        
}.                                                     


(** some admissible value types *)

Instance NatVT : ValTyp nat.
  
Instance UnitVT : ValTyp unit.

Instance BoolVT : ValTyp bool.


(**********************************************************************)

(**** value types in the deep embedding *)

(** the type of value types - 
    syntactic types are parametrised by semantic ones *)
Definition VTyp : Type := sig ValTyp.

(** smart value type constructor *)
Definition vtyp (T: Type) {VT: ValTyp T} : VTyp :=
    @exist Type ValTyp T VT.

(** extractor *)
Definition vtypExt (t: VTyp) : Type := proj1_sig t.


(** value type abbreviations *)

Definition Nat : VTyp := vtyp nat.

Definition Unit : VTyp := vtyp unit.

Definition Bool : VTyp := vtyp bool.


(************************************************************************)

(** Parameter types *)
Inductive PTyp : Type := PT (ts: list VTyp).

(** Value-typing contexts *)
Definition valTC : Type := list (Id * VTyp).

(** Function types *)
Inductive FTyp : Type := FT (prs_type: valTC) (ret_type: VTyp).

(** Function-typing contexts *)
Definition funTC : Type := list (Id * FTyp).

(** extractors for function types *)
Definition extParType (ft: FTyp) : valTC :=
  match ft with FT ps _ => ps end.

Definition extRetType (ft: FTyp) : VTyp :=
  match ft with FT _ t => t end.


(***************************************************************************)

(**** Value expressions *)

(** the internal type of values, parametrised by a semantic type *)
Inductive ValueI (T: Type) : Type := Cst (v: T).

(** the external type of values, hiding the semantic type *)
Definition Value : Type := sigT ValueI.

(** smart value constructor *)
Definition cst (T: Type) (v: T) : Value :=
           @existT Type ValueI T (Cst T v).

(** extractors *)
Definition ValueI2T (T: Type) (v: ValueI T) : T :=
    match v with Cst _  x => x end.             

Definition cstExt (v: Value) : projT1 v := ValueI2T (projT1 v) (projT2 v).


(** sanity conditions *)
Lemma cstSound1 (v: Value) : v = cst (projT1 v) (cstExt v).
Proof.
  unfold cst.
  unfold cstExt.
  destruct v as [T v].
  simpl.
  assert (v = Cst T (ValueI2T T v)).
  destruct v.
  simpl.
  reflexivity.
  rewrite <- H.
  reflexivity.
Defined.  

Lemma cstSound2 (T: Type) (v: T) : v = cstExt (cst T v).
Proof.
  unfold cstExt.
  simpl.
  auto.
Defined.

Lemma cstEq (T: Type) (v1 v2: T) : cst T v1 = cst T v2 -> v1 = v2.
  intros.
  assert (projT2 (cst T v1) = projT2 (cst T v2)).
  intuition.  
  simpl in H0.
  inversion H0; subst.
  reflexivity.
Defined.  


(***********************************************************************)

(** Value environments *)
Definition valEnv : Type := list (Id * Value).

(** Quasi-values *)
Inductive QValue : Type := Var (x: Id) | QV (v: Value).


(*************************************************************************)

(** syntactic tag type - NOT USED, TO BE REMOVED *)

Inductive Tag : Type := LL | RR.

(**** Terms *)

Inductive Fun : (** Functions *)
   Type := FC (fenv: Envr Id Fun) 
              (tenv: valTC) (e0 e1: Exp) (x: Id) (n: nat)
with QFun : (** Quasi-functions *)
   Type := FVar (x: Id) | QF (v: Fun)
with Exp : (** Expressions *)
       Type :=
         | Modify (T1 T2: Type) (VT1: ValTyp T1) (VT2: ValTyp T2)
                  (XF: XFun T1 T2) (q: QValue)
         | Return (G: Tag) (q: QValue)
         | BindN (e1: Exp) (e2: Exp) 
         | BindS (x: Id) (e1: Exp) (e2: Exp) 
         | BindMS (fenv: Envr Id Fun) (venv: valEnv) (e: Exp)
         | Apply (q: QFun) (ps: Prms) 
         | Val (v: Value)
         | IfThenElse (e1: Exp) (e2: Exp) (e3: Exp)       
with Prms : (** Parameters *)
   Type := PS (es: list Exp).


Scheme Fun_mut := Induction for Fun Sort Type
with QFun_mut := Induction for QFun Sort Type
with Exp_mut := Induction for Exp Sort Type
with Prms_mut := Induction for Prms Sort Type.


Inductive Prog : (** Programs *)
       Type := prog (e: Exp)
             | define (x: Id) (f: Fun) (p: Prog).


(** Function environments *)
Definition funEnv : Type := Envr Id Fun.

  
(* Conversion from typing contexts to type lists *)
Definition env2ptyp (m: valTC) : PTyp := PT (map snd m).


(* Creation of value environments *)
Definition mkVEnv (tenv: valTC) (vs: list Value) : valEnv :=
     interleave (map fst tenv) vs.

  
(************************************************************************)

(** Static semantics *)

(* definition of value typing *)
Inductive ValueTyping (v: Value) (t: VTyp) : Type :=
| ValueTypingC : let T := projT1 v
          in T = (proj1_sig t) ->
             ValTyp T -> 
             ValueTyping v t.

(** smart value constructor *)
Definition valueTyping (T: Type) {VT: ValTyp T} (v: T) :
  ValueTyping (cst T v) (vtyp T) :=
   ValueTypingC (cst T v) (vtyp T) eq_refl VT. 

Inductive IdTyping : valTC -> Id -> VTyp -> Type :=
   | Id_Typing : forall (tenv: valTC) (x: Id) (t: VTyp), 
                    findET tenv x t -> 
                    IdTyping tenv x t.
   
Inductive QValueTyping : valTC -> QValue -> VTyp -> Type :=
  | ProperValue_Typing : forall (tenv: valTC ) (v: Value) (t: VTyp),
                   ValueTyping v t -> 
                   QValueTyping tenv (QV v) t
  | Var_Typing : forall (tenv: valTC) (x: Id) (t: VTyp),
                   IdTyping tenv x t -> 
                   QValueTyping tenv (Var x) t.

Definition EnvTyping : valEnv -> valTC -> Type :=
    MatchEnvsT ValueTyping.

Inductive FunTyping : (** Functions *)
                  Fun -> FTyp -> Type :=
  | FunZ_Typing: forall (ftenv: funTC) (tenv: valTC)
                        (fenv: funEnv) 
                        (e0 e1: Exp) (x: Id) (t: VTyp),
      MatchEnvsT FunTyping fenv ftenv -> 
      ExpTyping ftenv tenv fenv e0 t -> 
      FunTyping (FC fenv tenv e0 e1 x 0) (FT tenv t)
  | FunS_Typing: forall (ftenv: funTC) (tenv: valTC)
                        (fenv: funEnv) 
            (e0 e1: Exp) (x: Id) (n: nat) (t: VTyp),
      let ftenv' := (x, FT tenv t) :: ftenv in 
      let fenv' := (x, FC fenv tenv e0 e1 x n) :: fenv in 
      MatchEnvsT FunTyping fenv ftenv -> 
      ExpTyping ftenv' tenv fenv' e1 t -> 
      FunTyping (FC fenv tenv e0 e1 x n) (FT tenv t) ->
      FunTyping (FC fenv tenv e0 e1 x (S n)) (FT tenv t)
with QFunTyping : (** Quasi-functions *)
                  funTC -> funEnv -> QFun -> FTyp -> Type :=
  | QF_Typing: forall (ftenv: funTC) (fenv: funEnv) (f: Fun) (ft: FTyp),
      FunTyping f ft ->
      QFunTyping ftenv fenv (QF f) ft
  | FVar_Typing: forall (ftenv: funTC) (fenv: funEnv)
                       (x: Id) (f: Fun) (ft: FTyp),
      MatchEnvs2BT FunTyping x f ft fenv ftenv ->  
      QFunTyping ftenv fenv (FVar x) ft
with ExpTyping : (** expressions *)
        funTC -> valTC -> funEnv -> Exp -> VTyp -> Type := 
  | Modify_Typing : forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                           (T1 T2: Type) (VT1: ValTyp T1) (VT2: ValTyp T2)
                           (XF: XFun T1 T2) (q: QValue),
                     QValueTyping tenv q (vtyp T1) ->  
                     ExpTyping ftenv tenv fenv
                               (Modify T1 T2 VT1 VT2 XF q) (vtyp T2)
  | Return_Typing : forall (G: Tag)
                           (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                           (q: QValue) (t: VTyp),
                       QValueTyping tenv q t ->  
                       ExpTyping ftenv tenv fenv (Return G q) t 
  | BindN_Typing : forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                          (e1 e2: Exp) (t1 t2: VTyp), 
                       ExpTyping ftenv tenv fenv e1 t1 ->
                       ExpTyping ftenv tenv fenv e2 t2 ->
                       ExpTyping ftenv tenv fenv (BindN e1 e2) t2
  | BindS_Typing : forall (ftenv: funTC) (tenv: valTC) 
                          (fenv: funEnv) (x: Id) 
                          (e1 e2: Exp) (t1 t2: VTyp), 
                       let tenv' := (x, t1) :: tenv in  
                       ExpTyping ftenv tenv fenv e1 t1 ->
                       ExpTyping ftenv tenv' fenv e2 t2 ->
                       ExpTyping ftenv tenv fenv (BindS x e1 e2) t2
  | BindMS_Typing : forall (ftenv ftenvP ftenv': funTC)
                           (tenv tenvP tenv': valTC)
                           (fenv fenvP fenv': funEnv) (envP: valEnv) 
                           (e: Exp) (t: VTyp), 
                       MatchEnvsT ValueTyping envP tenvP ->
                       MatchEnvsT FunTyping fenv ftenv -> 
                       MatchEnvsT FunTyping fenvP ftenvP ->
                       tenv' = tenvP ++ tenv ->
                       ftenv' = ftenvP ++ ftenv ->                        
                       fenv' = fenvP ++ fenv ->                         
                       ExpTyping ftenv' tenv' fenv' e t ->
                       ExpTyping ftenv tenv fenv (BindMS fenvP envP e) t
  | Apply_Typing : forall (ftenv: funTC) (tenv fps: valTC) (fenv: funEnv)
                          (q: QFun) (ps: Prms) (pt: PTyp) (t: VTyp),
              pt = PT (map snd fps) ->    
              MatchEnvsT FunTyping fenv ftenv -> 
              QFunTyping ftenv fenv q (FT fps t) ->
              PrmsTyping ftenv tenv fenv ps pt ->
              ExpTyping ftenv tenv fenv (Apply q ps) t
  | Val_Typing : forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv) 
                        (v: Value) (t: VTyp), 
                       ValueTyping v t -> 
                       ExpTyping ftenv tenv fenv (Val v) t
  | IfThenElse_Typing : forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                               (e1 e2 e3: Exp) (t: VTyp),
             ExpTyping ftenv tenv fenv e1 Bool ->
             ExpTyping ftenv tenv fenv e2 t ->
             ExpTyping ftenv tenv fenv e3 t ->
             ExpTyping ftenv tenv fenv (IfThenElse e1 e2 e3) t
with PrmsTyping : (** parameters *)
         funTC -> valTC -> funEnv -> Prms -> PTyp -> Type :=
| PS_Typing: forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                    (es: list Exp) (ts: list VTyp),
      Forall2T (ExpTyping ftenv tenv fenv) es ts ->          
      PrmsTyping ftenv tenv fenv (PS es) (PT ts).


Definition FEnvTyping : funEnv -> funTC -> Type :=
    MatchEnvsT FunTyping.

Scheme FunTyping_mut := Induction for FunTyping Sort Type
with QFunTyping_mut := Induction for QFunTyping Sort Type
with ExpTyping_mut := Induction for ExpTyping Sort Type
with PrmsTyping_mut := Induction for PrmsTyping Sort Type.


(*********************************************************************)

Inductive ProgTyping : (** Functions *)
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


(**********************************************************************)

(** value typing lemmas from RelLib *)

Definition ExTDefVal := ExRelValT ValueTyping.

Definition ExTDefValProj1 := ExRelValTProj1 ValueTyping.

Definition updateVEnvLemma := updateEnvLemmaT ValueTyping.

Definition overrideVEnvLemma := overrideEnvLemmaT ValueTyping.

Definition ValTypedByEnv := RelatedByEnvEP2_T ValueTyping.

Definition ValTypedByEnvA := RelatedByEnvEP_T ValueTyping.


(** fun typing lemmas from RelLib *)

Definition ExTDefFun := ExRelValT FunTyping.

Definition ExTDefFunProj1 := ExRelValTProj1 FunTyping.

Definition updateFEnvLemma := updateEnvLemmaT FunTyping.

Definition overrideFEnvLemma := overrideEnvLemmaT FunTyping.

Definition FunTypedByEnv := RelatedByEnvEP2_T FunTyping.

Definition FunTypedByEnvA := RelatedByEnvEP_T FunTyping.


(********************************************************************)

(** value lists  in Prop *)

Inductive isValue (e: Exp) : Prop :=
  IsValue : forall (v: Value), e = Val v -> isValue e.

Definition isValueList (ls : list Exp) : Prop :=
Forall isValue ls.

Inductive isValueList2  
  (els : list Exp) (vls : list Value) : Prop :=
IsValueList2 :  els = map Val vls -> isValueList2 els vls.

(** value lists in Type *)

Inductive isValueT (e: Exp) : Type :=
  IsValueT : forall (v: Value), e = Val v -> isValueT e.

Definition isValueListT (ls : list Exp) : Type :=
ForallT isValueT ls.

Inductive isValueList2T  
  (els : list Exp) (vls : list Value) : Type :=
IsValueList2T :  els = map Val vls -> isValueList2T els vls.

(***************************************************************)

(** lemmas about value lists in Type *)

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
  intros.
  inversion H; subst.
  unfold isValueList.
  revert H.
  induction vls.
  simpl.
  constructor.
  constructor.
  econstructor.
  reflexivity.
  eapply IHvls.
  constructor.
  auto.
Defined.  

Lemma isValueList22_T (ls : list Exp) : isValueListT ls ->
             sigT (fun vs => isValueList2T ls vs). 
Proof.
  induction ls.
  intros.
  exists nil.  
  constructor.
  simpl.
  reflexivity.
  intros.
  assert (isValueListT ls).
  inversion X; subst.
  assumption.
  inversion X; subst.
  inversion X1; subst. 
  eapply IHls in X0.
  destruct X0 as [vs1 X0].
  constructor 1 with (x := v::vs1).
  constructor.
  inversion X0; subst.
  simpl.
  reflexivity.
Defined.  

Lemma ExTDefNatT (T: Type) {VT: ValTyp T}
           (tenv: valTC) (venv: valEnv) (t: VTyp) (x: Id): 
    MatchEnvsT ValueTyping venv tenv ->
    findET tenv x t ->
    T = proj1_sig t -> 
    sigT (fun v: T => findET venv x (cst T v)). 
Proof.
  intros.
  subst.
  cut (sigT2 (findET venv x) (fun v: Value => ValueTyping v t)).
  intro.
  destruct X1 as [v E1 E2].
  inversion E2; subst.
  subst T.
  destruct v as [T b].
  destruct b.
  compute in H.
  assert (T = proj1_sig t).
  compute.
  assumption.
  clear H.
  subst.
  econstructor 1 with (x:=v).
  unfold cst.
  assumption.
  eapply ExTDefVal.
  eassumption.
  assumption.
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
intros.  
inversion H; subst.
clear H.
induction vs.
auto.
simpl.
rewrite IHvs.
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


(***************************************************************)

(** parameter typing *)

Definition vlsTyping (vs: list Value) (pt: list VTyp) : Type :=
           Forall2T ValueTyping vs pt.

Definition PrmsValTyping (es: list Exp) (ts: list VTyp) : Type :=
  sigT2 (isValueList2 es) (fun vs => vlsTyping vs ts).

Definition PrmsValTypingT (es: list Exp) (ts: list VTyp) : Type :=
  sigT2 (isValueList2T es) (fun vs => vlsTyping vs ts).

(***************************************************************)

(** lemmas about parameter typing *)

Lemma prmsTypingAux_T (fps : valTC) (vls : list Value)
                       (h: length fps = length vls):
          vlsTyping vls (map snd fps) ->
                         MatchEnvsT ValueTyping (mkVEnv fps vls) fps.
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
      (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
      (v: Value) (t: VTyp) :
  ExpTyping ftenv tenv fenv (Val v) t ->
  ValueTyping v t.
Proof.
  intros.
  dependent induction X.
  auto.
Defined.


Lemma Exp2ValueTypingA 
      (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
      (v: Value) (t: VTyp) :
  ExpTyping ftenv tenv fenv (Val v) t ->
  ExpTyping emptyE emptyE emptyE (Val v) t.
Proof.
intro.
constructor.
eapply Exp2ValueTyping.
eassumption.
Defined.


Lemma Value2ExpTyping 
      (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
      (v: Value) (t: VTyp) :
  ValueTyping v t ->
  ExpTyping ftenv tenv fenv (Val v) t.
Proof.
  intros.
  inversion H; subst.
  constructor.
  auto.
Defined.  


Lemma prmsTypingAux01_T 
      (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
      (vs: list Value) (ts: list VTyp) :
          vlsTyping vs ts ->
          PrmsTyping ftenv tenv fenv (PS (map Val vs)) (PT ts).
Proof.
  unfold vlsTyping.
  intros.
  induction X.
  constructor.
  constructor.
  simpl.
  constructor.
  constructor.
  eapply Value2ExpTyping.
  auto.
  auto.
  inversion IHX; subst.
  auto.
Defined.


Lemma matchListsAux02_T 
      (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                       (ts: list VTyp)
                       (es : list Exp) (vs : list Value) : 
  isValueList2T es vs -> 
  PrmsTyping ftenv tenv fenv (PS es) (PT ts) -> 
  vlsTyping vs ts.
Proof.
  unfold vlsTyping.
  intros.
  inversion H; subst.
  inversion X; subst.
  revert X.
  revert H.
  dependent induction X0 generalizing vs.
  - intros.
    symmetry in x.
    eapply map_eq_nil in x.
    rewrite x.
    constructor.
  - intros.
    simpl in x.
    destruct vs.
    simpl in x.
    inversion x.
    constructor.
    simpl in x.
    inversion x; subst.
    eapply Exp2ValueTyping.
    eassumption.
    simpl in x.
    inversion x; subst.
    specialize (IHX0 vs).
    eapply IHX0.
    reflexivity.
    econstructor.  
    auto.
    constructor.
    auto.
Defined.

Lemma matchListsAux02 
      (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                       (ts: list VTyp)
                       (es : list Exp) (vs : list Value) : 
  isValueList2 es vs -> 
  PrmsTyping ftenv tenv fenv (PS es) (PT ts) -> 
  vlsTyping vs ts.
Proof.
  unfold vlsTyping.
  intros.
  inversion H; subst.
  inversion X; subst.
  revert H.
  revert X.
  dependent induction X0 generalizing vs.
  - intros.
    symmetry in x.
    eapply map_eq_nil in x.
    rewrite x.
    constructor.
  - simpl in x.
    destruct vs.
    simpl in x.
    inversion x.
    constructor.
    simpl in x.
    inversion x; subst.
    eapply Exp2ValueTyping.
    eassumption.
    simpl in x.
    inversion x; subst.
    specialize (IHX0 vs).
    eapply IHX0.
    reflexivity.
    econstructor.  
    auto.
    constructor.
    auto.
Defined.
  
Lemma matchListsAux1A 
      (ftenv: funTC) (tenv: valTC) (fenv: funEnv) (ts: list VTyp)
                       (es : list Exp) (vs : list Value) : 
  isValueList2T es vs -> 
  Forall2T (ExpTyping ftenv tenv fenv) es ts -> 
  Forall2T (ExpTyping emptyE emptyE emptyE) es ts.
Proof.
  intros.
  revert H.
  revert vs.  
  dependent induction X.
  intros.
  inversion H; subst.
  symmetry in H0.
  eapply map_eq_nil in H0; subst.
  constructor.
  intros.
  destruct vs.
  inversion H; subst.
  simpl in H0.
  inversion H0.
  inversion H; subst.
  simpl in H0.
  inversion H0; subst.
  assert (isValueList2T (map Val vs) vs).
  constructor.
  reflexivity.
  eapply IHX in H1.
  constructor.
  eapply Exp2ValueTypingA.
  eassumption.
  assumption.
Defined.


Lemma matchListsAux1 
      (ftenv: funTC) (tenv: valTC) (fenv: funEnv) (ts: list VTyp)
                       (es : list Exp) (vs : list Value) : 
  isValueList2T es vs -> 
  Forall2T (ExpTyping ftenv tenv fenv) es ts -> 
  Forall2T ValueTyping vs ts.
Proof.
  intros.
  revert H.
  revert vs.  
  dependent induction X.
  intros.
  inversion H; subst.
  symmetry in H0.
  eapply map_eq_nil in H0; subst.
  constructor.
  intros.
  destruct vs.
  inversion H; subst.
  simpl in H0.
  inversion H0.
  inversion H; subst.
  simpl in H0.
  inversion H0; subst.
  assert (isValueList2T (map Val vs) vs).
  constructor.
  reflexivity.
  eapply IHX in H1.
  constructor.
  eapply Exp2ValueTyping.
  eassumption.
  assumption.
Defined.


Lemma prmsAux2 (vls: list Value) (fps: valTC) :  
vlsTyping vls (map snd fps) -> 
  length fps = length vls. 
Proof.
  intros.
  unfold vlsTyping in X.  
  eapply sameBehSameLength_T in X.
  rewrite X.
  rewrite map_length.
  auto.
Defined.


Lemma prmsAux3 
      (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                (ls: list Exp) (fps: valTC) :  
PrmsTyping ftenv tenv fenv (PS ls) (env2ptyp fps) -> 
  length fps = length ls. 
Proof.
  intros. 
  unfold env2ptyp in X.
  inversion X; subst.
  eapply sameBehSameLength_T in X0.
  rewrite X0 at 1.
  rewrite map_length.
  auto.
Defined.


(*******************************************************************)

(** lemmas about function typing *)

Lemma funTypingAux1 
      (fenv: funEnv) (tenv fps: valTC) (e0 e1: Exp)
                     (x: Id) (i: nat) (t: VTyp) :
      FunTyping (FC fenv tenv e0 e1 x i) (FT fps t) ->
                        tenv = fps.
Proof.
  intros.
  inversion X; subst.
  reflexivity.
  reflexivity.
Defined.


(********************************************************************)

(** lemmas about value lists in Prop *)

Lemma isValueList2IsValue (els : list Exp) (vls : list Value) :
  isValueList2 els vls -> isValueList els.
Proof.
  intros.
  inversion H; subst.
  unfold isValueList.
  revert H.
  induction vls.
  simpl.
  constructor.
  constructor.
  econstructor.
  reflexivity.
  eapply IHvls.
  constructor.
  auto.
Defined.  

Lemma isValueListT_triv (vls : list Value) :
  isValueListT (map Val vls).
Proof.
  induction vls.
  constructor.
  constructor.
  econstructor.
  reflexivity.
  auto.
Defined.  
  

Lemma isValueList22 (ls : list Exp) : isValueList ls ->
             exists vs, isValueList2 ls vs. 
Proof.
  induction ls.
  intros.
  exists nil.  
  constructor.
  simpl.
  reflexivity.
  intros.
  assert (isValueList ls).
  inversion H; subst.
  assumption.
  inversion H; subst.
  inversion H3; subst.
  eapply IHls in H0.
  destruct H0.
  rename x into vs1.
  exists (v::vs1).
  constructor.
  inversion H0; subst.
  simpl.
  reflexivity.
Defined.  


Lemma mkEnvTyping_aux0 (fps: valTC) (vs: list Value):
  length fps = length vs ->
  vlsTyping vs (map snd fps) ->
    EnvTyping (mkVEnv fps vs) fps.
  intros.
  eapply prmsTypingAux_T.
  auto.
  auto.
Defined.


End Static.


  





