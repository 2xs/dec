(*  DEC 2.0 language specification.
   Paolo Torrini, 
   Universite' Lille-1 - CRIStAL-CNRS
*)

Require Import List.
Require Import Equality.

Require Import ModTypE1. 
Require Import TypSpecE1. 
Require Import LangSpecE1. 

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

Definition VTyping (v: Value) (t: VTyp) : Type :=
  valueVTyp v = t.                       

Definition sVTyping (T: Type) (v: T) (t: VTyp) : Type :=
    sVTyp t = T. 

Definition FTyping (f: Fun) (ft: FTyp) : Type :=
   funFTyp f = ft.


Lemma VTyping2sVTyp_lemma (v: Value) (t: VTyp) :
         VTyping v t -> sVTyp t.
  intros.
  destruct v.
  destruct v.
  unfold VTyping in X.
  rewrite <- X.
  simpl.
  exact v.
  Show Proof.
Defined.  

Definition VTyping2sVTyp {v: Value} {t: VTyp} : VTyping v t -> sVTyp t :=
 let (x, v0) as s return (VTyping s t -> sVTyp t) := v in
  match v0 as v1 return (VTyping (existT ValueI x v1) t -> sVTyp t) with
  | Cst _ v1 =>
      fun X1 : VTyping (existT ValueI x (Cst x v1)) t =>
      eq_rect (valueVTyp (existT ValueI x (Cst x v1)))
        (fun t0 : VTyp => sVTyp t0) v1 t X1
  end.

(*
 match v0 with
  | Cst _ v1 =>
      fun X1 : VTyping (existT ValueI x (Cst x v1)) t => 
      eq_rect_r sVTyp v1 X1
  end.
*)
Definition VTyping_lemma {v: Value} {t: VTyp} : VTyping v t ->
                sigT (fun x : sVTyp t => v = cst t x). 
  intros.
  destruct v.
  destruct v.
  unfold VTyping in X.
  simpl in X.
  rewrite <- X.
  constructor 1 with (x:=v).
  auto.
Defined.  

  
(** Typing of identifiers *)

Definition IdTyping : valTC -> Id -> VTyp -> Type := EnvrAssign. 

Definition IdFTyping : funTC -> Id -> FTyp -> Type := EnvrAssign. 

(*
Inductive EnvrDAssign {K V1 V2: Type} {h: DEq K} (f: V2 -> V1) :
      Envr K V2 -> K -> V1 -> Type.
*)

Definition IdEnvTyping : valEnv -> Id -> VTyp -> Type :=
  EnvrDAssign valueVTyp.

Definition IdFEnvTyping : funEnv -> Id -> FTyp -> Type :=
  EnvrDAssign funFTyp.



(** Environment manipulation *)

(* value environments *)

Definition IdValue2IdVTyp (p: Id * Value) : Id * VTyp :=
    thicken Id valueVTyp p.
(*  (fst p, valueVTyp (snd p)). *)

Definition valEnv2valTC (env: valEnv) : valTC :=
    map (thicken Id valueVTyp) env.
(*  map IdValue2IdVTyp env. *)

Definition EnvTyping (env: valEnv) (tenv: valTC) : Type :=
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

Definition FEnvTyping (env: funEnv) (tenv: funTC) : Type :=
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
(*  | BindS_N_Typing : forall (ftenv: funTC) (tenv tenv': valTC)
                            (x: Id) (e1 e2: Exp) (t1 t2: VTyp), 
                       tenv' = (x, t1) :: tenv ->   
                       ExpTyping ftenv tenv e1 t1 ->
                       ExpTyping ftenv tenv' e2 t2 ->
                       ExpTyping ftenv tenv
                                 (BindS x None e1 e2) t2
*)
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




(** function is well typed *)

Definition FunWT (ftenv: funTC) (f: Fun) : Type :=
    match f with 
      | FC tenv t v e =>
        (VTyping v t * ExpTyping ftenv tenv e t)
    end.                            


(** the function environment is well typed *)
Inductive FEnvWT (fenv: funEnv) : Type :=
| FEnvWT_SC : (forall (ftenv: funTC) (x: Id) (f: Fun),
    FEnvTyping fenv ftenv -> 
    findE fenv x = Some f ->
    FunWT ftenv f) -> FEnvWT fenv.
    

(*
(** the function environment is well typed *)
Inductive FEnvWT (fenv: funEnv) : Type :=
| FEnvWT_SC : (forall (ftenv: funTC) (x: Id) (f: Fun),
    findE fenv x = Some f -> 
    forall (tenv: valTC) (t: VTyp) 
           (v: Value) (e: Exp),
      f = FC tenv t v e ->
      FEnvTyping fenv ftenv -> 
      (VTyping v t *
      ExpTyping ftenv tenv e t)) ->
   FEnvWT fenv.
*)
 

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

(** Value lists in Prop *)

Inductive isValue (e: Exp) : Prop :=
  IsValue : forall (v: Value), e = Val v -> isValue e.

Definition isValueList (ls : list Exp) : Prop :=
Forall isValue ls.

Inductive isValueList2  
  (els : list Exp) (vls : list Value) : Prop :=
IsValueList2 :  els = map Val vls -> isValueList2 els vls.

(** Value lists in Type *)

Inductive isValueT (e: Exp) : Type :=
  IsValueT : forall (v: Value), e = Val v -> isValueT e.

Definition isValueListT (ls : list Exp) : Type :=
ForallT isValueT ls.

Inductive isValueList2T  
  (els : list Exp) (vls : list Value) : Type :=
IsValueList2T :  els = map Val vls -> isValueList2T els vls.

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
  econstructor.
  intros.
  inversion H.
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


Lemma FunTyping0_lemma (ftenv: funTC) (fenv: funEnv)
      (x: Id) (f: Fun) (v: Value) (t: VTyp) :
    FEnvWT fenv ->
    FEnvTyping fenv ftenv ->
    findE fenv x = Some f ->
    v = fun0Exp f ->
    t = funVTyp f -> 
    VTyping v t.
  intros.
  inversion X; subst.
  specialize (X1 ftenv x f X0 H).
  destruct f.
(*  specialize (X1 tenv t v e eq_refl X0).*)
  destruct X1.
  simpl.
  assumption.
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
  inversion X; subst.
  specialize (X1 ftenv x f X0 H).
  destruct f.
(*  specialize (X1 tenv t v e eq_refl X0).*)
  destruct X1.
  simpl.
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
  eapply FunTyping0_lemma.
  exact X.
  eassumption.
  eassumption.
  simpl.
  auto.
  assumption.
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
  inversion X2; subst.
  simpl in *.
  inversion IHvs.
  rewrite H at 1.
  auto.
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





