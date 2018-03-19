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
Require Import TSoundnessE2.

Import ListNotations.


Module Reflect (IdT: ModTyp) <: ModTyp.

Module TSoundnessL := TSoundness IdT.
Export TSoundnessL.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.


Open Scope type_scope.

Definition MM (S A : Type) : Type := S -> A * S.

Definition ret {S A : Type} (a : A) : MM S A :=
  fun s => (a , s).

Definition bind {S A B : Type} (m : MM S A)(f : A -> MM S B) : MM S B :=  
fun s => match m s with
    | (a, s') => f a s'
    end.

Definition WW := W * nat.

(**********************************************************************)

(* type translation *)

Fixpoint tlist2type (ts: list Type) : Type :=
  match ts with
    | nil => unit
    | (t::ts') => t * tlist2type ts'
  end.                               

Definition TList_Type {T: Type} (f: T -> Type) (ts: list T) : Type :=
  tlist2type (map f ts). 

(*
Fixpoint TList_Type {T: Type} (f: T -> Type) (ts: list T) : Type :=
  match ts with
      | nil => unit
      | (t::ts') => (f t) * (TList_Type f ts')
  end.                                    
*)
(*
Fixpoint TList_TypeList {T: Type} (f: T -> Type) (ts: list T) :
  list Type :=
    match ts with
      | nil => nil
      | (t::ts') => (f t) :: (TList_TypeList f ts')
  end.                                    

Definition TList_TypeList {T: Type} (f: T -> Type) (ts: list T) :
  list Type := map f ts. 
*)

Definition VTyp_Trans (t: VTyp) : Type :=
  sVTyp t.

Definition PTyp_ListTrans (pt: PTyp) : list Type :=
  match pt with
      PT ts => map sVTyp ts
  end.                 

Definition VTyp_Trans_map (ts: list VTyp) : list Type :=
  map VTyp_Trans ts.
  
Definition VTList_Trans (ts: list VTyp) : Type :=
  TList_Type VTyp_Trans ts.
   
  
Definition valTC_Trans (tenv: valTC) : Type := VTList_Trans (map snd tenv).

Definition PTyp_Trans (pt: PTyp) : Type :=
  match pt with
      PT ts => VTList_Trans ts
  end.                 

Fixpoint FType_mk (ts: list Type) (t: Type) : Type :=
  match ts with
    | nil => unit -> MM WW t
    | t' :: ts' => t' -> FType_mk ts' t
  end.                                



(* Definitional interpreter: types could match this definition, 
   except here the definition actually generates a function type,
   by calling FType_mk (which is recursive)
*)
Definition VTypInTC_Trans (tenv: valTC) (t: VTyp) : Type :=
 let ts := VTyp_Trans_map (map snd tenv) in FType_mk ts (VTyp_Trans t).  


(* Similar to VTypinTC_Trans, except the context is given as a
   parameters type rather than as a TC.  
*)
Definition FTyp_Trans (ft: FTyp) : Type :=
  match ft with
    | FT pt t => let ts := PTyp_ListTrans pt in FType_mk ts (VTyp_Trans t) 
 end.                               

(* Similar to FTyp_Trans, except returns a pair instead of building
   the function type. 
*)
Definition FTyp_TRN (ft: FTyp) : (list Type * Type) :=
  match ft with
    | FT pt t => let ts := PTyp_ListTrans pt in (ts, VTyp_Trans t) 
 end.                               

(* translates funTC to an environment using FTyp_TRN *)
Fixpoint FTTList_Trans (ftenv: funTC) : list (Id * (list Type * Type)) :=
  map (fun p => (fst p, FTyp_TRN (snd p))) ftenv.

(* translates a FTyp list to a type list using FTyp_Trans *)
Fixpoint FTyp_Trans_map (ts: list FTyp) : list Type :=
  map FTyp_Trans ts.
  
Fixpoint FTList_Trans (ts: list FTyp) : Type :=
  TList_Type FTyp_Trans ts.
   
Definition funTC_Trans (ftenv: funTC) : Type := FTList_Trans (map snd ftenv).

(***********************************************************************)

Definition FType_mk2 (x: (list Type) * Type) : Type :=
    tlist2type (fst x) -> MM WW (snd x).

Definition FTyp_Trans2 (ft: FTyp) : Type :=  
  match ft with
    | FT pt t => let ts := PTyp_ListTrans pt in FType_mk2 (ts, (VTyp_Trans t)) 
 end.                               

Definition FTyp_TRN2 (ft: FTyp) : Type :=
   FType_mk2 (FTyp_TRN ft).

Definition FunTyp_TRN (f: Fun) : Type :=
   FTyp_TRN2 (funFTyp f).

Definition FunTC_ListTrans (ftenv: funTC) : list (Id * Type) :=
  map (fun p => (fst p, (FTyp_TRN2 (snd p)))) ftenv.

Definition FunEnv_ListTrans (fenv: funEnv) : list (Id * Type) :=
  map (fun p => (fst p, (FunTyp_TRN (snd p)))) fenv.


(*Fixpoint FType_mk2 (x: (list Type) * Type) : Type :=
    FType_mk1 (fst x) (snd x).
*)
(* translates funTC to an environment using FTyp_TRN *)
(*
Definition FunTC_ListTrans (ftenv: funTC) : list (Id * Type) :=
  map (fun p => (fst p, FType_mk2 (FTyp_TRN (snd p)))) ftenv.
*)

(**********************************************************************)

(* value translation *)

Definition Value_Trans (v: Value) :  valueSTyp v := (* sVTyp (projT1 v) := *)
    sValue v.

Fixpoint TList_Trans (ts: list VTyp) : Type :=
  match ts with
      | nil => unit
      | (t::ts') => (VTyp_Trans t) * (TList_Trans ts')
  end.                                    

Fixpoint listTypTr (xts: list VTyp) :
  TList_Trans xts -> list Value :=
   match xts as l return (TList_Trans l -> list Value) with
   | [] => fun _ : TList_Trans [] => []
   | t :: ts =>
     fun ps : TList_Trans (t :: ts) =>
       cst t (fst ps) :: (listTypTr ts (snd ps))
   end.


Obligation Tactic := idtac. 

Program Definition Value_TRN_P (v: Value) (t: VTyp) (k: VTyping v t) :
  sVTyp t := _.
Next Obligation.
  intros.
  unfold sVTyp.
  unfold VTyping in k.
  unfold valueVTyp in k.
  destruct v as [t2 v].
  destruct v.
  unfold sVTyp in v.
  simpl in k.
  rewrite <- k.
  destruct t2.
  exact v.
  Show Proof.
Defined.


Definition Value_TRN (v: Value) (t: VTyp) (k: VTyping v t)  
 : match t with | VT st _ => st end :=
 (let
    (t2, v0) as s return (projT1 s = t -> match t with
                                          | VT st _ => st
                                          end) := v in
  fun k0 : projT1 (existT ValueI t2 v0) = t =>
  match
    v0 as v1
    return
      (projT1 (existT ValueI t2 v1) = t -> match t with
                                           | VT st _ => st
                                           end)
  with
  | Cst _ v1 =>
      fun k1 : projT1 (existT ValueI t2 (Cst t2 v1)) = t =>
      eq_rect t2 (fun t0 : VTyp => match t0 with
                                   | VT st _ => st
                                   end)
        (match
           t2 as v2
           return
             (match v2 with
              | VT st _ => st
              end -> v2 = t -> match v2 with
                               | VT st _ => st
                               end)
         with
         | VT st ct => fun (v2 : st) (_ : VT st ct = t) => v2
         end v1 k1) t k1
  end k0) k.


(***************************************************************************)

(* not really used *)
Fixpoint TTList_TypeList (tenv: valTC) :
  list (Id * Type) :=
    match tenv with
      | nil => nil
      | ((x,t)::tenv') => (x,VTyp_Trans t) :: (TTList_TypeList tenv')
  end.                                    

(* valenv translated to environment of hidden types *)
Definition EnvTrans (env: valEnv) :
  list (Id * sigT (fun T:Type => MM WW T)) :=
  map (fun (w: Id * Value) => let (x,v) := w in 
         (x, existT _ (valueSTyp v) (ret (sValue v)))) env.

(* not really used - 
   typing of shallow application - just needed to deal with arguments
   typed by type list *)
Definition TypeListApply {T1 T2: Type}
           (ps: list T1) (f: list T1 -> T2) : T2 := f ps.


Definition MIfThenElse {T: Type} (d1: MM WW bool) (d2 d3: MM WW T) :
  MM WW T :=
     bind d1 (fun x: bool => match x with
                             | true => d2
                             | bool => d3
                             end).            

(* abbreviation, corresponding to shallow embedding of a 
   function typing context *)
Definition SFenv' : Type := list (Id *
  sigT (fun T:Type => list (sigT (fun T:Type => MM WW T)) -> MM WW T)).

(* shallow d-value type *)
Definition SVTyp : Type := sigT (fun T:Type => MM WW T).

(* shallow d-function type *)
Definition SFTyp : Type :=
  sigT (fun T:Type => list SVTyp -> MM WW T).

(* shallow d-function TC type; can be used to type a shallow fenv *)
Definition SFenv : Type := list (Id * SFTyp).

(* Definition FTyp2S (ft: FTyp) : SFTyp :=
  (@existT Type (fun T:Type => list SVTyp -> MM W T) (ret_type ft)
*)                                                 


(******************************************************)

(*
Lemma VTList_Trans_equiv (ts: list VTyp) : 
  VTList_Trans ts = TList_Type VTyp_Trans ts.
  auto.
--
  induction ts.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Defined.
*)
     
Lemma extract_from_valTC_Trans (tenv: valTC)
      (X: valTC_Trans tenv)             
      (x: Id) (t: VTyp) (k: findE tenv x = Some t) : sVTyp t.
  unfold valTC_Trans in *.
  induction tenv.
  inversion k.
  destruct a as [x0 t0].
  inversion k; subst.
  destruct (IdT.IdEqDec x x0) in H0.
  inversion H0; subst.
  inversion X; subst.
  simpl in *.
  unfold VTyp_Trans in X0.
  exact X0.
  inversion X; subst.
  simpl in *.
(*  
  rewrite <- VTList_Trans_equiv in X1.
*)
  eapply IHtenv.
  exact X1.
  exact H0.
Defined.  


Lemma extend_valTC_Trans (env0: valEnv) (tenv tenv0: valTC) :
       EnvTyping env0 tenv0 ->     
       valTC_Trans tenv ->     
       valTC_Trans (tenv0 ++ tenv).
  intros.
  inversion X; subst.
  induction env0.
  simpl in *.
  exact X0.
  destruct a as [x v].
  simpl in *.
  constructor.
  simpl.
  exact (sValue v).
  assert (EnvTyping env0 (map (thicken StaticSemL.Id valueVTyp) env0)).
  unfold EnvTyping.
  unfold MatchEnvs.
  reflexivity.
  specialize (IHenv0 X1).
  exact IHenv0.
Defined.  


Lemma extract_from_funTC_Trans (ftenv: funTC)
      (sftenv : list (Id * Type))
      (sfenv: tlist2type (map snd sftenv))             
      (x: Id) (ft: FTyp) (k: findE ftenv x = Some ft) :
  sftenv = FunTC_ListTrans ftenv ->
  FTyp_Trans2 ft.
  revert sfenv.
  revert sftenv.
  induction ftenv.
  - intros.
    simpl in *.
    inversion k.
  - destruct a as [x0 ft0].
    destruct ft.
    intros.
    simpl in k.
    destruct (IdT.IdEqDec x x0) in k.
    + inversion e; subst.
      inversion k; subst.
      simpl in *.
      intro X.
      eapply (fst sfenv).
      exact X.
    + specialize (IHftenv k).
      specialize (IHftenv (FunTC_ListTrans ftenv)).
      inversion H; subst.
      clear H0.
      simpl in *.
      intros.
      specialize (IHftenv (snd sfenv) eq_refl).
      eapply IHftenv.
(*      exact X.*)
Defined.      
      

(********************************************************)

Definition ExpTrans_def (sftenv: list (Id * Type)) :=   
   fun (ftenv: funTC) (tenv: valTC) (e: Exp) (t: VTyp) 
       (k: ExpTyping ftenv tenv e t) =>
     forall (ET VT: Type) (sfenv: tlist2type (map snd sftenv)),
      sftenv = FunTC_ListTrans ftenv ->        
      VT = sVTyp t ->
      ET = valTC_Trans tenv ->
      (ET -> MM WW VT).     

Definition PrmsTrans_def (sftenv: list (Id * Type)) :=   
   fun (ftenv: funTC) (tenv: valTC) (ps: Prms) (pt: PTyp) 
       (k: PrmsTyping ftenv tenv ps pt) =>        
     forall (ET PT: Type) (sfenv: tlist2type (map snd sftenv)),
      sftenv = FunTC_ListTrans ftenv ->        
      PT = PTyp_Trans pt ->
      ET = valTC_Trans tenv ->
      (ET -> MM WW PT).

Definition Trans_ExpTyping_mut (sfenv: list (Id * Type)) :=
  ExpTyping_mut (ExpTrans_def sfenv) (PrmsTrans_def sfenv). 

Definition Trans_PrmsTyping_mut (sfenv: list (Id * Type)) :=
  PrmsTyping_mut (ExpTrans_def sfenv) (PrmsTrans_def sfenv). 


Program Fixpoint ValEnvTRN (env: valEnv) :
  valTC_Trans (valEnv2valTC env) := _.
Next Obligation.
  intros.
  unfold valTC_Trans.
  unfold VTList_Trans.
  unfold TList_Type.
  unfold valEnv2valTC.
  unfold VTyp_Trans.
  unfold thicken.
  unfold valueVTyp.
  Show Proof.
  rewrite map_map.
  rewrite map_map.
  simpl.
  Show Proof.
  induction env.
  simpl.
  exact tt.
  destruct a.
  simpl in *.
  split.
  exact (sValue v).
  eapply IHenv.
  Show Proof.
Defined.  

Program Fixpoint ValEnvTRN0 (env: valEnv) :
  valTC_Trans (valEnv2valTC env) := _.
Next Obligation.
  intros.
  unfold valTC_Trans.
  unfold VTList_Trans.
  unfold TList_Type.
  unfold valEnv2valTC.
  unfold VTyp_Trans.
  unfold thicken.
  unfold valueVTyp.
  induction env.
  exact tt.
  Show Proof.
(*  rewrite map_map.
  rewrite map_map.
  simpl.
  Show Proof.
  induction env.
  simpl.
  exact tt.
*)
  destruct a.
  simpl in *.
  split.
  exact (sValue v).
  eapply IHenv.
  Show Proof.
Defined.  


Fixpoint ValEnvTRN1 (env: valEnv) : valTC_Trans (valEnv2valTC env) :=
 eq_rect_r (fun l : list Type => tlist2type l)
   (eq_rect_r (fun l : list Type => tlist2type l)
      (list_rect
         (fun env0 : list (LangSpecL.Id * Value) =>
          tlist2type
            (map (fun x : StaticSemL.Id * Value => sVTyp (projT1 (snd x)))
               env0)) tt
         (fun (a : LangSpecL.Id * Value) (env0 : list (LangSpecL.Id * Value))
            (IHenv : tlist2type
                       (map
                          (fun x : StaticSemL.Id * Value =>
                           sVTyp (projT1 (snd x))) env0)) =>
          let
            (i, v) as p
             return
               (tlist2type
                  (map
                     (fun x : StaticSemL.Id * Value => sVTyp (projT1 (snd x)))
                     (p :: env0))) := a in
          (sValue v, IHenv)) env)
      (map_map (fun p : StaticSemL.Id * Value => (fst p, projT1 (snd p)))
         (fun x : LangSpecL.Id * VTyp => sVTyp (snd x)) env))
   (map_map snd (fun t : VTyp => sVTyp t)
      (map (fun p : StaticSemL.Id * Value => (fst p, projT1 (snd p))) env)).


Definition ValEnvTRN2 (env: valEnv) : valTC_Trans (valEnv2valTC env) :=
 list_rect
   (fun env0 : list (LangSpecL.Id * Value) =>
    tlist2type
      (map (fun t : VTyp => sVTyp t)
         (map snd
            (map (fun p : StaticSemL.Id * Value => (fst p, projT1 (snd p)))
               env0)))) tt
   (fun (a : LangSpecL.Id * Value) (env0 : list (LangSpecL.Id * Value))
      (IHenv : tlist2type
                 (map (fun t : VTyp => sVTyp t)
                    (map snd
                       (map
                          (fun p : StaticSemL.Id * Value =>
                           (fst p, projT1 (snd p))) env0)))) =>
    let
      (i, v) as p
       return
         (tlist2type
            (map (fun t : VTyp => sVTyp t)
               (map snd
                  (map
                     (fun p0 : StaticSemL.Id * Value =>
                      (fst p0, projT1 (snd p0))) (p :: env0))))) := a in
    (sValue v, IHenv)) env.


  
(******************************************************)
(*** NEW STUFF *)

Program Definition extract_from_valTC_TransA (tenv: valTC)
      (X: valTC_Trans tenv)             
      (x: Id) (t: VTyp) (k: findE tenv x = Some t) : sVTyp t := _.
Next Obligation.
  intros.
  unfold valTC_Trans in *.
  unfold VTyp_Trans in X.
  unfold VTList_Trans in X.
  unfold TList_Type in X.
  unfold VTyp_Trans in X.
  Show Proof.
  induction tenv.
  Show Proof.
  inversion k.
  destruct a as [x0 t0].
  simpl in k.
  Show Proof.
  destruct (IdT.IdEqDec x x0) in k.
  inversion k; subst.
  simpl in X.
  destruct X.
  exact s.
  simpl in X.
  destruct X.
  apply IHtenv.
  exact t1.
  exact k.
  Show Proof.
Defined.
  
Definition extract_from_valTC_TransB (tenv: valTC)
      (X: valTC_Trans tenv)             
      (x: Id) (t: VTyp) (k: findE tenv x = Some t) : sVTyp t := 
 list_rect
   (fun tenv0 : list (LangSpecL.Id * VTyp) =>
    tlist2type (map (fun t0 : VTyp => sVTyp t0) (map snd tenv0)) ->
    findE tenv0 x = Some t -> sVTyp t)
   (fun (_ : tlist2type (map (fun t0 : VTyp => sVTyp t0) (map snd [])))
      (k0 : findE [] x = Some t) =>
    let X1 :=
      match k0 in (_ = y) return (y = Some t -> sVTyp t) with
      | eq_refl =>
          fun H : findE [] x = Some t =>
          (fun H0 : findE [] x = Some t =>
           let H1 :=
             eq_ind (findE [] x)
               (fun e : option VTyp =>
                match e with
                | Some _ => False
                | None => True
                end) I (Some t) H0
             :
             False in
           False_rect (sVTyp t) H1) H
      end in
    X1 eq_refl)
   (fun (a : LangSpecL.Id * VTyp) (tenv0 : list (LangSpecL.Id * VTyp))
      (IHtenv : tlist2type (map (fun t0 : VTyp => sVTyp t0) (map snd tenv0)) ->
                findE tenv0 x = Some t -> sVTyp t)
      (X0 : tlist2type
              (map (fun t0 : VTyp => sVTyp t0) (map snd (a :: tenv0))))
      (k0 : findE (a :: tenv0) x = Some t) =>
    (let
       (x0, t0) as p
        return
          (tlist2type (map (fun t0 : VTyp => sVTyp t0) (map snd (p :: tenv0))) ->
           findE (p :: tenv0) x = Some t -> sVTyp t) := a in
     fun
       (X1 : tlist2type
               (map (fun t1 : VTyp => sVTyp t1) (map snd ((x0, t0) :: tenv0))))
       (k1 : findE ((x0, t0) :: tenv0) x = Some t) =>
     let s := IdT.IdEqDec x x0 in
     match
       s as s0
       return ((if s0 then Some t0 else findE tenv0 x) = Some t -> sVTyp t)
     with
     | left e =>
         fun k2 : Some t0 = Some t =>
         let X2 :=
           match k2 in (_ = y) return (y = Some t -> sVTyp t) with
           | eq_refl =>
               fun H : Some t0 = Some t =>
               (fun H0 : Some t0 = Some t =>
                let H1 :=
                  f_equal
                    (fun e0 : option VTyp =>
                     match e0 with
                     | Some v => v
                     | None => t0
                     end) H0
                  :
                  t0 = t in
                (fun H2 : t0 = t =>
                 let H3 := H2 : t0 = t in
                 eq_rect_r (fun _ : VTyp => sVTyp t)
                   (eq_rect_r
                      (fun x1 : IdT.Id =>
                       (tlist2type
                          (map (fun t1 : VTyp => sVTyp t1) (map snd tenv0)) ->
                        findE tenv0 x1 = Some t -> sVTyp t) -> 
                       sVTyp t)
                      (fun
                         _ : tlist2type
                               (map (fun t1 : VTyp => sVTyp t1)
                                  (map snd tenv0)) ->
                             findE tenv0 x0 = Some t -> sVTyp t =>
                       eq_rect_r
                         (fun t1 : VTyp =>
                          tlist2type
                            (map (fun t2 : VTyp => sVTyp t2)
                               (map snd ((x0, t1) :: tenv0))) ->
                          Some t1 = Some t -> sVTyp t)
                         (fun
                            (X2 : tlist2type
                                    (map (fun t1 : VTyp => sVTyp t1)
                                       (map snd ((x0, t) :: tenv0))))
                            (_ : Some t = Some t) => 
                          let (s0, _) := X2 in s0) H2 X1 k2) e IHtenv) H3) H1)
                 H
           end in
         X2 eq_refl
     | right _ =>
         fun k2 : findE tenv0 x = Some t => let (_, t1) := X1 in IHtenv t1 k2
     end k1) X0 k0) tenv X k.

Lemma ValEnvTRN_ok (env: valEnv) 
(*      (X: valTC_Trans (valEnv2valTC env)) *)            
      (x: Id) (t: VTyp) (v: sVTyp t)
      (k1: findE (valEnv2valTC env) x = Some t)
      (k2: findE env x = Some (cst t v)) :
  v = extract_from_valTC_TransB (valEnv2valTC env) (ValEnvTRN2 env) x t k1.
  induction env.
  inversion k1.
  destruct a.
  simpl in k1, k2.
  simpl.
  destruct (IdT.IdEqDec x i).
  simpl.
  inversion e; subst.
  unfold eq_rect_r.
  unfold eq_rect_r. 
  simpl.
  dependent destruction k1. 
  rewrite <- eq_rect_eq.
  rewrite <- eq_rect_eq.
  destruct v0.
  destruct v0.
  dependent destruction k2.
  unfold sValue.
  simpl.
  reflexivity.
  eapply IHenv.
  exact k2.
Defined.  
  
(* ON MY WAY ... *)


Program Definition ExpTransVar (sftenv : list (Id * Type)) :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (t : VTyp) (i : IdTyping tenv x t),
    ExpTrans_def sftenv ftenv tenv (Var x) t (Var_Typing ftenv tenv x t i) := _.
Next Obligation.
     unfold ExpTrans_def.
     intros.
     inversion i; subst.
     eapply extract_from_valTC_TransB with (x:=x) (t:=t) in X.
     exact (ret X).
     exact H2.
     Show Proof.
Defined.     


Definition ExpTransVar1 
   (ftenv : funTC) (tenv : valTC) (x : Id) 
   (t : VTyp) (k: findE tenv x = Some t)
   (FE: tlist2type (map snd (FunTC_ListTrans ftenv)))
   (VE: valTC_Trans tenv) : sVTyp t :=
  extract_from_valTC_TransB tenv VE x t k.


Program Definition ExpTransVar2 (sftenv : list (Id * Type)) :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (t : VTyp) (i : IdTyping tenv x t),
    ExpTrans_def sftenv ftenv tenv (Var x) t (Var_Typing ftenv tenv x t i) := _.
Next Obligation.
     unfold ExpTrans_def.
     intros.
     inversion i; subst.
     unfold MM.
     intro.
     split.
     eapply extract_from_valTC_TransB with (x:=x) (t:=t) (tenv:=tenv). 
     exact X. 
     exact H2.
     exact X0.
     Show Proof.
Defined.
     

Program Definition ExpTransVar3 (sftenv : list (Id * Type)) :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (t : VTyp) (i : IdTyping tenv x t),
    ExpTrans_def sftenv ftenv tenv (Var x) t (Var_Typing ftenv tenv x t i) := _.
Next Obligation.
     unfold ExpTrans_def.
     intros.
     Show Proof.
     inversion i; subst.
     Show Proof.
     unfold MM.
     intro.
     split.
     eapply ExpTransVar1 with (x:=x) (t:=t) (tenv:=tenv).
     exact H2.
     exact sfenv.
     exact X.
     exact X0.
     Show Proof.
Defined.     



(*
    ExpTrans_def sftenv ftenv tenv (Var x) t (Var_Typing ftenv tenv x t i) :=


  extract_from_valTC_TransA tenv
      (X: valTC_Trans tenv)             
      (x: Id) (t: VTyp) (k: findE tenv x = Some t)
.
Next Obligation.
*)


(*****************************************************)


Definition ExpTrans1_def :=   
   fun (ftenv: funTC) (tenv: valTC) (e: Exp) (t: VTyp) 
       (k: ExpTyping ftenv tenv e t) =>
     forall (sfenv: tlist2type (map snd (FunTC_ListTrans ftenv))),        
      (valTC_Trans tenv -> MM WW (sVTyp t)).     

Definition PrmsTrans1_def :=   
   fun (ftenv: funTC) (tenv: valTC) (ps: Prms) (pt: PTyp) 
       (k: PrmsTyping ftenv tenv ps pt) =>        
     forall (sfenv: tlist2type (map snd (FunTC_ListTrans ftenv))),
      (valTC_Trans tenv -> MM WW (PTyp_Trans pt)).


Definition Trans_ExpTyping_mut1 :=
  ExpTyping_mut ExpTrans1_def PrmsTrans1_def. 

Definition Trans_PrmsTyping_mut1 :=
  PrmsTyping_mut ExpTrans1_def PrmsTrans1_def.


Program Fixpoint ExpTrans (ftenv: funTC) (tenv: valTC) (e: Exp) (t: VTyp) 
       (k: ExpTyping ftenv tenv e t) :
  forall (sfenv: tlist2type (map snd (FunTC_ListTrans ftenv))),      
      (valTC_Trans tenv -> MM WW (sVTyp t)) := _    
with PrmsTrans (ftenv: funTC) (tenv: valTC) (ps: Prms) (pt: PTyp) 
       (k: PrmsTyping ftenv tenv ps pt) :        
  forall (sfenv: tlist2type (map snd (FunTC_ListTrans ftenv))),       
      (valTC_Trans tenv -> MM WW (PTyp_Trans pt)) := _.              
Next Obligation.
   eapply Trans_ExpTyping_mut1.   
   - unfold ExpTrans1_def.
     intros.
     inversion v0; subst.
     exact (ret (sValue v)).
   - (* apply ExpTransVar. *)
     unfold ExpTrans1_def.
     intros.
     inversion i; subst.
     unfold MM.
     intro.
     split.
     eapply (extract_from_valTC_TransB tenv X x).
     exact H.
     exact X0.
     Show Proof.
   - unfold ExpTrans1_def.
     intros.
     specialize (X sfenv X1).   
     specialize (X0 sfenv X1).
     exact (bind X (fun _ => X0)).
   - unfold ExpTrans1_def.
     intros.
     specialize (X sfenv X1).   
     specialize (X0 sfenv).
     inversion e; subst.
     unfold valTC_Trans in X1.
     unfold VTList_Trans in X1.
     unfold MM.
     unfold MM in X.
     intro w0.
     specialize (X w0).
     destruct X as [sv1 w1].
     assert (valTC_Trans ((x, t1) :: tenv)).
     {+ unfold valTC_Trans.
        simpl.
        constructor.
        exact sv1.
        exact X1.
     }
     specialize (X0 X).
     unfold MM in X0.
     specialize (X0 w1).
     exact X0.
   - unfold ExpTrans1_def.
     intros.
     specialize (X sfenv).
     inversion e1; subst.
     clear H.
     eapply extend_valTC_Trans with (env0:=env0) (tenv0:=tenv0) in X0.
     eapply X.
     exact X0.
     exact e0.
   - unfold ExpTrans1_def.
     intros.
     specialize (X sfenv X2).
     specialize (X0 sfenv X2).
     specialize (X1 sfenv X2).
     intro w0.
     specialize (X w0).
     destruct X as [b w1].
     inversion b; subst.
     specialize (X0 w1).
     exact X0.
     specialize (X1 w1).
     exact X1.
   - unfold ExpTrans1_def, PrmsTrans1_def.
     intros.
     specialize (X0 sfenv X1).
     unfold MM.
     unfold MM in X0.
     intro w0.
     specialize (X0 w0).
     destruct X0 as [nn w1].
     destruct w1 as [s1 n1].
     assert WW as w2.
     exact (s1, min nn n1).
     specialize (X sfenv X1).
     assert (FTyp_Trans2 (FT pt t)).
     eapply extract_from_funTC_Trans with
         (sftenv:=(FunTC_ListTrans ftenv)) (ftenv:=ftenv) (x:=x).
     exact sfenv.
     inversion i; subst.
     exact H.
     reflexivity.
     unfold FTyp_Trans2 in X0.
     unfold FType_mk2 in X0.
     simpl in X0.
     destruct pt.
     unfold PTyp_Trans in X.
     unfold VTList_Trans in X.
     unfold PTyp_ListTrans in X0.
     unfold TList_Type in X.
     unfold VTyp_Trans in X.
     unfold VTyp_Trans in X0.
     revert w2.
     exact (bind X X0).
   - unfold ExpTrans1_def, PrmsTrans1_def.
     intros.
     specialize (X sfenv X0).
     assert (FTyp_Trans2 (FT pt t)).
     eapply extract_from_funTC_Trans with
         (sftenv:=(FunTC_ListTrans ftenv)) (ftenv:=ftenv) (x:=x).
     exact sfenv.
     inversion i; subst.
     exact H.
     reflexivity.
     unfold FTyp_Trans2 in X1.
     unfold FType_mk2 in X1.
     simpl in X1.
     destruct pt.
     unfold PTyp_Trans in X.
     unfold VTList_Trans in X.
     unfold PTyp_ListTrans in X1.
     unfold TList_Type in X.
     unfold VTyp_Trans in X.
     unfold VTyp_Trans in X1.  
     exact (bind X X1).
   - unfold ExpTrans1_def.
     intros.
     specialize (X sfenv X0).
     unfold MM in *.
     intro w0.
     specialize (X w0).
     destruct X as [v0 w1].
     destruct w1 as [s1 n1].
     destruct XF.
     set (x_mod0 v0 s1) as p.
     subst inpT0.
     subst outT0.
     exact (fst p, (snd p, n1)).
   - unfold PrmsTrans1_def.
     intros.
     intro.
     split.
     constructor.
     exact X0.
   - unfold ExpTrans1_def, PrmsTrans1_def.
     intros.
     specialize (X sfenv X1).
     specialize (X0 sfenv X1). 
     intro w0.
     specialize (X w0).
     destruct X as [v1 w1].
     specialize (X0 w1).
     destruct X0 as [vs w2].
     split.
     unfold PTyp_Trans in *.
     constructor.
     exact v1.
     exact vs.
     exact w2.
Defined.     

Next Obligation.
   eapply Trans_PrmsTyping_mut1.   
   - unfold ExpTrans1_def.
     intros.
     inversion v0; subst.
     exact (ret (sValue v)).
   - (* apply ExpTransVar. *)
     unfold ExpTrans1_def.
     intros.
     inversion i; subst.
     unfold MM.
     intro.
     split.
     eapply (extract_from_valTC_TransB tenv X x).
     exact H.
     exact X0.
   - unfold ExpTrans1_def.
     intros.
     specialize (X sfenv X1).   
     specialize (X0 sfenv X1).
     exact (bind X (fun _ => X0)).
   - unfold ExpTrans1_def.
     intros.
     specialize (X sfenv X1).   
     specialize (X0 sfenv).
     inversion e; subst.
     unfold valTC_Trans in X1.
     unfold VTList_Trans in X1.
     unfold MM.
     unfold MM in X.
     intro w0.
     specialize (X w0).
     destruct X as [sv1 w1].
     assert (valTC_Trans ((x, t1) :: tenv)).
     {+ unfold valTC_Trans.
        simpl.
        constructor.
        exact sv1.
        exact X1.
     }
     specialize (X0 X).
     unfold MM in X0.
     specialize (X0 w1).
     exact X0.
   - unfold ExpTrans1_def.
     intros.
     specialize (X sfenv).
     inversion e1; subst.
     clear H.
     eapply extend_valTC_Trans with (env0:=env0) (tenv0:=tenv0) in X0.
     eapply X.
     exact X0.
     exact e0.
   - unfold ExpTrans1_def.
     intros.
     specialize (X sfenv X2).
     specialize (X0 sfenv X2).
     specialize (X1 sfenv X2).
     intro w0.
     specialize (X w0).
     destruct X as [b w1].
     inversion b; subst.
     specialize (X0 w1).
     exact X0.
     specialize (X1 w1).
     exact X1.
   - unfold ExpTrans1_def, PrmsTrans1_def.
     intros.
     specialize (X0 sfenv X1).
     unfold MM.
     unfold MM in X0.
     intro w0.
     specialize (X0 w0).
     destruct X0 as [nn w1].
     destruct w1 as [s1 n1].
     assert WW as w2.
     exact (s1, min nn n1).
     specialize (X sfenv X1).
     assert (FTyp_Trans2 (FT pt t)).
     eapply extract_from_funTC_Trans with
         (sftenv:=(FunTC_ListTrans ftenv)) (ftenv:=ftenv) (x:=x).
     exact sfenv.
     inversion i; subst.
     exact H.
     reflexivity.
     unfold FTyp_Trans2 in X0.
     unfold FType_mk2 in X0.
     simpl in X0.
     destruct pt.
     unfold PTyp_Trans in X.
     unfold VTList_Trans in X.
     unfold PTyp_ListTrans in X0.
     unfold TList_Type in X.
     unfold VTyp_Trans in X.
     unfold VTyp_Trans in X0.
     revert w2.
     exact (bind X X0).
   - unfold ExpTrans1_def, PrmsTrans1_def.
     intros.
     specialize (X sfenv X0).
     assert (FTyp_Trans2 (FT pt t)).
     eapply extract_from_funTC_Trans with
         (sftenv:=(FunTC_ListTrans ftenv)) (ftenv:=ftenv) (x:=x).
     exact sfenv.
     inversion i; subst.
     exact H.
     reflexivity.
     unfold FTyp_Trans2 in X1.
     unfold FType_mk2 in X1.
     simpl in X1.
     destruct pt.
     unfold PTyp_Trans in X.
     unfold VTList_Trans in X.
     unfold PTyp_ListTrans in X1.
     unfold TList_Type in X.
     unfold VTyp_Trans in X.
     unfold VTyp_Trans in X1.  
     exact (bind X X1).
   - unfold ExpTrans1_def.
     intros.
     specialize (X sfenv X0).
     unfold MM in *.
     intro w0.
     specialize (X w0).
     destruct X as [v0 w1].
     destruct w1 as [s1 n1].
     destruct XF.
     set (x_mod0 v0 s1) as p.
     subst inpT0.
     subst outT0.
     exact (fst p, (snd p, n1)).
   - unfold PrmsTrans1_def.
     intros.
     intro.
     split.
     constructor.
     exact X0.
   - unfold ExpTrans1_def, PrmsTrans1_def.
     intros.
     specialize (X sfenv X1).
     specialize (X0 sfenv X1). 
     intro w0.
     specialize (X w0).
     destruct X as [v1 w1].
     specialize (X0 w1).
     destruct X0 as [vs w2].
     split.
     unfold PTyp_Trans in *.
     constructor.
     exact v1.
     exact vs.
     exact w2.
Defined.     


(*****************************************************)

(** function is well typed *)

Definition FunWT1 (ftenv: funTC) (f: Fun) : Type :=
    match f with 
      | FC tenv t v e => VTyping v t
    end.                            


(** the function environment is well typed *)
Inductive FEnvWT1 (fenv: funEnv) : Type :=
| FEnvWT1_SC : (forall (ftenv: funTC) (x: Id) (f: Fun),
    FEnvTyping fenv ftenv -> 
    findE fenv x = Some f ->
    FunWT1 ftenv f) -> FEnvWT1 fenv.


(* translation of d-function base case *)
Program Definition preZero (ftenv: funTC) (f: Fun) :
   FunWT1 ftenv f -> FunTyp_TRN f := _.

Next Obligation.
  intros.
  destruct f.
  unfold FunTyp_TRN.
  unfold FTyp_TRN2.
  unfold FType_mk2.
  simpl.
  intros.
  unfold FunWT1 in X.
(*  destruct X as [k0 k1]. *)
  inversion X; subst.
  exact (ret (sValue v)).
Defined.

Definition noDup {K V: Type} (ls: list (K * V)) :=
  NoDup (map fst ls).

Lemma noDup_prop {K V: Type} (ls: list (K * V)) (x: K) (v: V) :
  noDup ((x,v)::ls) -> noDup ls.
  unfold noDup.
  intros.
  simpl in *.
  inversion H; subst.
  exact H3.
Defined.

Lemma someMember {K V: Type} {h: DEq K} (ls: list (K * V)) (x: K) (v: V) :
  findE ls x = Some v ->
  In x (map fst ls).
  induction ls.
  intros.
  simpl in H.
  inversion H.
  intros.
  destruct a.
  simpl in *.
  destruct (dEq x k) in H.
  left.
  symmetry.
  exact e.
  right.
  eapply IHls.
  exact H.
Defined.  

Lemma distThendiff {A: Type} (ls: list A) (x x0: A) :      
  ~ In x ls -> In x0 ls -> x0 <> x.
  induction ls.
  intros.
  simpl in H0.
  intuition H0.
  intros.
  simpl in H.
  simpl in H0.
  intuition.
  inversion H1; subst.
  eapply H0 in H4.
  auto.
Defined.


Lemma FEnvWT1_prop (fenv: funEnv) (x: Id) (f: Fun) :
  noDup ((x,f)::fenv) ->
  FEnvWT1 ((x,f)::fenv) ->
  FEnvWT1 fenv.
  intros.
  constructor.
  intros.
  inversion X; subst.
  specialize (X1 (funEnv2funTC ((x,f)::fenv))).
  specialize (X1 x0 f0).
  assert (FEnvTyping ((x, f) :: fenv) (funEnv2funTC ((x, f) :: fenv))).
  constructor.
  specialize (X1 X2).   
  assert (findE ((x, f) :: fenv) x0 = Some f0).
  {- rewrite <- update_simpl1.
     exact H0.   
     inversion H; subst.
     assert (In x0 (map fst fenv)).
     eapply someMember with (v:=f0).
     exact H0.
     eapply distThendiff.
     exact H3.
     exact H1.
  }
  specialize (X1 H1).
  unfold FunWT1 in *.
  exact X1.
Defined.


Fixpoint suffix {A: Type} (ls1 ls2: list A) : Prop :=
  match ls1 with
  | nil => True
  | _ => match ls2 with
         | nil => False
         | c::cs => (ls1 = ls2) \/ suffix ls1 cs
         end
  end.             
      

(* translation of fenv base case *)
Program Definition ZeroTRN1 (fenv: funEnv)        
        (k: FEnvWT1 fenv) :
  noDup fenv ->
  tlist2type (map snd (FunEnv_ListTrans fenv)) := _.
Next Obligation.
  intro fenv.
  induction fenv.
  intros.
  simpl.
  exact tt.
  intros.
  destruct a.
  simpl in *.
  inversion k; subst.
  specialize (X (funEnv2funTC ((i, f) :: fenv)) i f).
  assert (FEnvTyping ((i, f) :: fenv) (funEnv2funTC ((i, f) :: fenv))).
  constructor.
  specialize (X X0).
  assert (findE ((i, f) :: fenv) i = Some f).
  simpl.
  destruct (IdT.IdEqDec i i).
  auto.
  intuition n.
  specialize (X H0).
  split.
  eapply preZero with (ftenv:= funEnv2funTC ((i, f) :: fenv)).
  exact X.
(*  specialize (IHfenv fenv). *)
  eapply FEnvWT1_prop in k.
  specialize (IHfenv k).
  eapply noDup_prop in H.
  specialize (IHfenv H).
  exact IHfenv.
  exact H.
Defined.  

Lemma FunEnv_Trans_lemma (fenv: funEnv) :
  FunEnv_ListTrans fenv = FunTC_ListTrans (funEnv2funTC fenv).
 unfold FunEnv_ListTrans.
 unfold FunTC_ListTrans.
 induction fenv.
 simpl.
 auto.
 simpl in *.
 rewrite IHfenv.
 auto.
Defined. 

Program Definition ZeroTRN2 (fenv: funEnv)        
        (k: FEnvWT1 fenv) :
  noDup fenv ->
  tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) := _.
Next Obligation.
  intros.
  eapply ZeroTRN1 in H.
  rewrite FunEnv_Trans_lemma in H.
  exact H.
  exact k.
Defined.

Program Definition ZeroTRN3 (fenv: funEnv)        
        (k: FEnvWT fenv) :
  noDup fenv ->
  tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) := _.
Next Obligation.
  intros.
  assert (FEnvWT1 fenv).
  inversion k; subst.
  constructor.
  intros.
  unfold FunWT1.
  unfold FunWT in X.
  specialize (X ftenv x f X0 H0).
  destruct f.
  destruct X.
  exact v0.
  eapply ZeroTRN1 in H.
  rewrite FunEnv_Trans_lemma in H.
  exact H.
  exact X.
Defined.



(* use  ZeroTRN1 for the base case; prove 
tlist2type (map snd (FunEnv_ListTrans fenv)) =
  tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv)))
 *)
Program Definition preSucc (fenv: funEnv)        
        (k: FEnvWT fenv) (x: Id) (f: Fun) :
  findE fenv x = Some f -> 
  noDup fenv ->
  forall (sfenv: tlist2type
                   (map snd (FunTC_ListTrans (funEnv2funTC fenv)))), 
  FunTyp_TRN f := _.
Next Obligation.
  intros.
  set (tenv := funValTC f).
  set (e := funSExp f).
  set (t := funVTyp f).
  set (ftenv := funEnv2funTC fenv).
  assert (ExpTyping ftenv tenv e t) as k1.
  inversion k; subst.
  set (sftenv := FunTC_ListTrans ftenv).
  specialize (X ftenv x f).
  assert (FEnvTyping fenv ftenv).
  constructor.
  specialize (X X0 H).
  unfold FunWT in X.
  destruct f.
  subst e.
  subst t.
  subst tenv.
  simpl in *.
  destruct X.
  exact e.
  specialize (ExpTrans ftenv tenv e t k1 sfenv).
  intro.
  unfold FunTyp_TRN.
  unfold FTyp_TRN2.
  unfold FType_mk2.
  unfold valTC_Trans in X.
  unfold VTList_Trans in X.
  destruct f.
  subst tenv e t.
  simpl in *.
  unfold VTyp_Trans.
  unfold TList_Type in X.
  exact X.
Defined.


Program Definition preSucc1 (fenv: funEnv)        
        (k: FEnvWT fenv) : 
  noDup fenv ->
  forall (sfenv: tlist2type
                   (map snd (FunTC_ListTrans (funEnv2funTC fenv))))
         (x: Id) (f: Fun),
  findE fenv x = Some f ->     
  FunTyp_TRN f := _.
Next Obligation.
  intros.
  eapply (preSucc fenv k x f H0 H sfenv).
Defined.


Lemma in_pairs_lemma {K V: Type} (ls: list (K * V))
        (k: K) (v: V) : In (k, v) ls -> (In k (map fst ls)).
  induction ls.
  simpl.
  auto.
  destruct a.
  simpl in *.
  intro.
  destruct H.
  inversion H; subst.
  left.
  auto.
  right.
  eapply IHls.
  exact H.
Defined.  


Lemma in_find_lemma {K V: Type} {h: DEq K} (ls: list (K * V)) (x: K) (v: V) :
    In (x,v) ls -> noDup ls -> findE ls x = Some v.
  intros.
  induction ls.
  inversion H.
  destruct a.
  simpl in *.
  destruct (dEq x k).
  destruct H.
  inversion H; subst.
  auto.
  inversion e; subst.
  unfold noDup in H0.
  inversion H0; subst.
  simpl in *.
  eapply in_pairs_lemma in H.
  intuition.
  destruct H.
  inversion H; subst.
  intuition n.
  specialize (IHls H).
  eapply IHls.
  eapply noDup_prop.
  exact H0.
Defined.  
  

(* (sftenv: list (Id * Type))
   (ftenv: funTC)       
   (k: FEnvWT fenv) : 
  ftenv = funEnv2funTC fenv ->
  sftenv = FunTC_ListTrans ftenv -> 
  noDup fenv -> *)
Program Definition SuccTRN_step (fenv: funEnv) :
  noDup fenv -> 
  (forall (x: Id) (f: Fun),
       findE fenv x = Some f ->     
       FunTyp_TRN f) ->
  forall (fenv1: funEnv),
    (forall a, In a fenv1 -> In a fenv) ->
     tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv1))) := _.
Next Obligation.
  intros fenv D X fenv1.
  induction fenv1.
  intros.
  simpl in *.
  exact tt.
  intro H.
  destruct a as [x f].
  intros.
  assert (forall a : LangSpecL.Id * Fun, In a fenv1 -> In a fenv).
  {- intros.
     specialize (H a).
     simpl in H.
     assert ((x, f) = a \/ In a fenv1).
     right; exact H0.
     eapply H in H1.
     exact H1.
  }
  specialize (IHfenv1 H0).
  simpl in *.
  clear H0.
  split.
  specialize (H (x,f)).
  assert (In (x, f) fenv).
  eapply H.
  left.
  auto.
  apply in_find_lemma in H0.
  eapply X.
  exact H0.
  exact D.
  eapply IHfenv1.
Defined.  


Program Definition preSucc2 (fenv: funEnv)        
        (k: FEnvWT fenv) : 
  noDup fenv ->
  forall (sfenv:
            tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))))
         (fenv1: funEnv),
    (forall a, In a fenv1 -> In a fenv) ->
     tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv1))) := _.
Next Obligation.
  intros.
  eapply (SuccTRN_step fenv H).
  eapply (preSucc1 fenv k).
  exact H.
  exact sfenv.
  exact H0.
Defined.  


Program Definition SuccTRN (fenv: funEnv)        
        (k: FEnvWT fenv) :
  noDup fenv ->
  forall (sfenv:
            tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv)))),
     tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) := _.
Next Obligation.
  intros.
  eapply (preSucc2 fenv k H).
  exact sfenv.
  intros.
  exact H0.
Defined.  


Fixpoint FunEnvTRN (n: nat) (fenv: funEnv)        
        (k1: FEnvWT fenv) (k2: noDup fenv) :
  tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) := match n with
          | 0 => ZeroTRN3 fenv k1 k2
          | S m => SuccTRN fenv k1 k2
                           (FunEnvTRN m fenv k1 k2)
          end.                 

Definition ExpTrans2 (ftenv: funTC) (tenv: valTC)
        (e: Exp) (t: VTyp) 
        (k: ExpTyping ftenv tenv e t) :
  forall (sfenv: tlist2type (map snd (FunTC_ListTrans ftenv))),
    (valTC_Trans tenv) -> MM WW (sVTyp t) := fun sfenv =>
  ExpTrans ftenv tenv e t k sfenv.     

Definition PrmsTrans2 (ftenv: funTC) (tenv: valTC)
        (ps: Prms) (pt: PTyp) 
        (k: PrmsTyping ftenv tenv ps pt) :
  forall (sfenv: tlist2type (map snd (FunTC_ListTrans ftenv))),
    (valTC_Trans tenv) -> MM WW (PTyp_Trans pt) := fun sfenv =>
  PrmsTrans ftenv tenv ps pt k sfenv.     

  
Definition ExpEvalTRN (fenv: funEnv)        
           (k1: FEnvWT fenv) (k2: noDup fenv)
           (env: valEnv) (e: Exp) (t: VTyp) 
  (k: ExpTyping (funEnv2funTC fenv) (valEnv2valTC env) e t) :
  MM WW (sVTyp t) := fun w =>
  let senv := ValEnvTRN env in
  let sfenv := FunEnvTRN (snd w) fenv k1 k2 in
  ExpTrans2 (funEnv2funTC fenv) (valEnv2valTC env) e t k sfenv senv w.

Definition PrmsEvalTRN (fenv: funEnv)        
           (k1: FEnvWT fenv) (k2: noDup fenv)
           (env: valEnv) (ps: Prms) (pt: PTyp) 
  (k: PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) ps pt) :
  MM WW (PTyp_Trans pt) := fun w =>   
  let senv := ValEnvTRN env in
  let sfenv := FunEnvTRN (snd w) fenv k1 k2 in
  PrmsTrans2 (funEnv2funTC fenv) (valEnv2valTC env) ps pt k sfenv senv w.


(********************************************************************)

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
    Show Proof.
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
           (k1: FEnvWT fenv) (*k2: noDup fenv*)
           (env: valEnv) (e: Exp) (t: VTyp) 
           (k3: ExpTyping (funEnv2funTC fenv) (valEnv2valTC env) e t)
           (s: W) (n: nat) : (sVTyp t * (W * nat)) := 
  SOS_Exp1 fenv env e t s n 
  (ExpSoundness (funEnv2funTC fenv) (valEnv2valTC env) e t k3
               fenv env k1 eq_refl eq_refl s n).



(**************************************************************************)
(**************************************************************************)


End Reflect.

(*
Require Import Eqdep FunctionalExtensionality Coq.Program.Tactics.
Require Import Coq.Init.Specif.
Require Import Coq.Logic.JMeq.
*)
