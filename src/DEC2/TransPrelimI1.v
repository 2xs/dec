(*  DEC 2.0 language specification.
   Paolo Torrini  
   Universite' de Lille - CRIStAL-CNRS
*)

Require Import List.
Require Import Equality.
Require Import Eqdep.
Require Import PeanoNat.
Require Import Omega.
Require Import ProofIrrelevance.

Require Import AuxLibI1.
Require Import TypSpecI1. 
Require Import ModTypI1. 
Require Import TypSpecI1. 
Require Import LangSpecI1. 
Require Import StaticSemI1.
Require Import DynamicSemI1.
Require Import WeakenI1.
Require Import UniqueTypI1.
Require Import DerivDynI1.

Import ListNotations.


Module TransPrelim (IdT: ModTyp) <: ModTyp.

Module DerivDynL := DerivDyn IdT.
Export DerivDynL.

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
(*
Fixpoint tlist2type (ts: list Type) : Type :=
  match ts with
    | nil => unit
    | (t::ts') => t * tlist2type ts'
  end.                               
 *)

Definition TList_Type {T: Type} (f: T -> Type) (ts: list T) : Type :=
  tlist2type (map f ts). 

Definition VTyp_Trans (t: VTyp) : Type :=
  sVTyp t.

Definition PTyp_ListTrans (pt: PTyp) : list Type :=
  match pt with
      PT ts => map sVTyp ts
  end.                 

Definition VTyp_Trans_map (ts: list VTyp) : list Type :=
  map sVTyp ts.
  
Definition VTList_Trans (ts: list VTyp) : Type :=
  tlist2type (map sVTyp ts).
   
  
Definition valTC_Trans (tenv: valTC) : Type :=
  tlist2type (map sVTyp (map snd tenv)).

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
 let ts := map (fun x => sVTyp (snd x)) tenv in FType_mk ts (sVTyp t).  


(* Similar to VTypinTC_Trans, except the context is given as a
   parameters type rather than as a TC.  
*)
Definition FTyp_Trans (ft: FTyp) : Type :=
  match ft with
    | FT pt t => let ts := PTyp_ListTrans pt in FType_mk ts (sVTyp t) 
 end.                               

(* Similar to FTyp_Trans, except returns a pair instead of building
   the function type. 
*)
Definition FTyp_TRN (ft: FTyp) : (list Type * Type) :=
  match ft with
    | FT pt t => let ts := PTyp_ListTrans pt in (ts, sVTyp t) 
 end.                               

(* translates funTC to an environment using FTyp_TRN *)
Fixpoint FTTList_Trans (ftenv: funTC) : list (Id * (list Type * Type)) :=
  map (fun p => (fst p, FTyp_TRN (snd p))) ftenv.

(* translates a FTyp list to a type list using FTyp_Trans *)
Fixpoint FTyp_Trans_map (ts: list FTyp) : list Type :=
  map FTyp_Trans ts.
  
Fixpoint FTList_Trans (ts: list FTyp) : Type :=
  tlist2type (map FTyp_Trans ts).
   
Definition funTC_Trans (ftenv: funTC) : Type := FTList_Trans (map snd ftenv).

(***********************************************************************)

Definition FType_mk2 (x: (list Type) * Type) : Type :=
    tlist2type (fst x) -> MM WW (snd x).

Definition FTyp_Trans2 (ft: FTyp) : Type :=  
  match ft with
    | FT pt t => let ts := PTyp_ListTrans pt in FType_mk2 (ts, (sVTyp t)) 
 end.                               

Definition FTyp_TRN2 (ft: FTyp) : Type :=
   FType_mk2 (FTyp_TRN ft).

Definition FunTyp_TRN (f: Fun) : Type :=
   FTyp_TRN2 (funFTyp f).

Definition FunTC_ListTrans (ftenv: funTC) : list (Id * Type) :=
  map (thicken Id FTyp_TRN2) ftenv.

Definition FunEnv_ListTrans (fenv: funEnv) : list (Id * Type) :=
  map (thicken Id FunTyp_TRN) fenv.


(* Important *)
Definition PTyp_TRN (pt: PTyp) : Type :=
     tlist2type (PTyp_ListTrans pt).


(**********************************************************************)

(* value translation *)

Definition Value_Trans (v: Value) :  valueSTyp v := (* sVTyp (projT1 v) := *)
    sValue v.

Fixpoint TList_Trans (ts: list VTyp) : Type :=
  match ts with
      | nil => unit
      | (t::ts') => (sVTyp t) * (TList_Trans ts')
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


(* valenv translated to environment of hidden types *)
Definition EnvTrans (env: valEnv) :
  list (Id * sigT (fun T:Type => MM WW T)) :=
  map (fun (w: Id * Value) => let (x,v) := w in 
         (x, existT _ (valueSTyp v) (ret (sValue v)))) env.


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


(*****************************************************************)

(* not used *)
Fixpoint TTList_TypeList (tenv: valTC) :
  list (Id * Type) :=
    match tenv with
      | nil => nil
      | ((x,t)::tenv') => (x,sVTyp t) :: (TTList_TypeList tenv')
  end.                                    

(* not used - 
   typing of shallow application - just needed to deal with arguments
   typed by type list *)
Definition TypeListApply {T1 T2: Type}
           (ps: list T1) (f: list T1 -> T2) : T2 := f ps.


(*******************************************************************)
     
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
  inversion H; subst.
  induction env0.
  simpl in *.
  exact X.
  destruct a as [x v].
  simpl in *.
  constructor.
  simpl.
  exact (sValue v).
  assert (EnvTyping env0 (map (thicken StaticSemL.Id valueVTyp) env0)).
  unfold EnvTyping.
  unfold MatchEnvs.
  reflexivity.
  specialize (IHenv0 H0).
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
Defined.      
      

(********************************************************************)

Definition ExpTrans_def (sftenv: list (Id * Type)) :=   
   fun (ftenv: funTC) (tenv: valTC) (e: Exp) (t: VTyp) 
       (k: ExpTyping ftenv tenv e t) =>
     forall (ET VT: Type) (sfenv: nat -> tlist2type (map snd sftenv)),
      sftenv = FunTC_ListTrans ftenv ->        
      VT = sVTyp t ->
      ET = valTC_Trans tenv ->
      (ET -> MM WW VT).     

Definition PrmsTrans_def (sftenv: list (Id * Type)) :=   
   fun (ftenv: funTC) (tenv: valTC) (ps: Prms) (pt: PTyp) 
       (k: PrmsTyping ftenv tenv ps pt) =>        
     forall (ET PT: Type) (sfenv: nat -> tlist2type (map snd sftenv)),
      sftenv = FunTC_ListTrans ftenv ->        
      PT = PTyp_Trans pt ->
      ET = valTC_Trans tenv ->
      (ET -> MM WW PT).

Definition Trans_ExpTyping_mut (sftenv: list (Id * Type)) :=
  ExpTyping_mut (ExpTrans_def sftenv) (PrmsTrans_def sftenv). 

Definition Trans_PrmsTyping_mut (sftenv: list (Id * Type)) :=
  PrmsTyping_mut (ExpTrans_def sftenv) (PrmsTrans_def sftenv). 


Program Fixpoint ValEnvTRN_P (env: valEnv) :
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
  rewrite map_map.
  rewrite map_map.
  simpl.
  induction env.
  simpl.
  exact tt.
  destruct a.
  simpl in *.
  split.
  exact (sValue v).
  eapply IHenv.
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
  destruct a.
  simpl in *.
  split.
  exact (sValue v).
  eapply IHenv.
Defined.  


Definition ValEnvTRN (env: valEnv) : valTC_Trans (valEnv2valTC env) :=
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



(*********************************************************************)

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
  induction tenv.
  inversion k.
  destruct a as [x0 t0].
  simpl in k.
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
Defined.

(* Important *)
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
      (x: Id) (t: VTyp) (v: sVTyp t)
      (k1: findE (valEnv2valTC env) x = Some t)
      (k2: findE env x = Some (cst t v)) :
  v = extract_from_valTC_TransB (valEnv2valTC env) (ValEnvTRN env) x t k1.
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
     exact H3.
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
     exact H3.
     exact X0.
Defined.
     

End TransPrelim.

