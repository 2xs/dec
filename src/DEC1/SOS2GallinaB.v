(* DEC1 language development.
   Paolo Torrini, with David Nowak
   Universite' Lille-1 - CRIStAL-CNRS
*)
(* monadic translation from DEC to Gallina *)

Require Import Arith List.
Import List.ListNotations.
Require Import Eqdep FunctionalExtensionality Coq.Program.Tactics.
Require Import Coq.Init.Specif.

Require Import StaticSemA.
Require Import DynamicSemA.
Require Import TRInductA.
Require Import WeakenA.
Require Import TSoundnessA.
Require Import IdModTypeA.
Require Import DetermA.
Require Import AbbrevA.
Require Import HoareA.
Require Import THoareA.
Require Import DECauxB.


Module SOS2Gallina (IdT: IdModType) <: IdModType.


Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module DECauxL := DECaux IdT.
Export DECauxL.

Open Scope type_scope.


Definition MM (S A : Type) : Type := S -> A * S.

Definition ret {S A : Type} (a : A) : MM S A :=
  fun s => (a , s).

Definition bind {S A B : Type} (m : MM S A)(f : A -> MM S B) : MM S B :=  
fun s => match m s with
    | (a, s') => f a s'
    end.

(*************************************************************************)

Definition VTyp_Trans (t: VTyp) : Type :=
  vtypExt t.

Definition VTyp_TRN (t: VTyp) : Type :=
  vtypExt t.

Definition PTyp1_Trans (pt: PTyp) : list Type :=
  match pt with
      PT ts => map vtypExt ts
  end.                 

Fixpoint TList_Trans (ts: list VTyp) : Type :=
  match ts with
      | nil => unit
      | (t::ts') => (VTyp_Trans t) * (TList_Trans ts')
  end.                                    

Definition valTC_Trans (tenv: valTC) : Type := TList_Trans (map snd tenv).


Definition PTyp_Trans (pt: PTyp) : Type :=
  match pt with
      PT ts => TList_Trans ts
  end.                 

Fixpoint tlist2type (ts: list Type) : Type :=
  match ts with
    | nil => unit
    | (t::ts') => t * tlist2type ts'
  end.                               

Inductive IsTypeList1 : list Type -> Type :=
  | IsTLN1 : IsTypeList1 nil
  | IsTLC1 : forall (ts: list Type) (t: Type),
              IsTypeList1 ts -> IsTypeList1 (t::ts).


Obligation Tactic := idtac. 


Program Fixpoint listTypTrA_P (xts: list Type) (ps : tlist2type xts) :
  list Value := _.

Next Obligation.
  fix rec 1.
  intros.
  destruct xts as [ | t ts].
  exact nil.
  destruct ps as [v vs].
  specialize (rec ts vs).
  exact (cst t v :: rec).
Defined.  

Fixpoint listTypTrA (xts: list Type) : 
  tlist2type xts -> list Value :=
   match xts as ls return (tlist2type ls -> list Value) with
   | [] => fun _ : tlist2type [] => []
   | t :: ts =>
     fun ps : tlist2type (t :: ts) =>
       cst t (fst ps) :: (listTypTrA ts (snd ps))
   end.


Program Fixpoint listTypTr_P (xts: list VTyp) (ps : TList_Trans xts) :
  list Value := _.

Next Obligation.
  fix rec 1.
  intros.
  destruct xts as [ | t ts].
  exact nil.
  destruct ps as [v vs].
  specialize (rec ts vs).
  exact (cst (VTyp_TRN t) v :: rec).
Defined.

Fixpoint listTypTr (xts: list VTyp) :
  TList_Trans xts -> list Value :=
   match xts as l return (TList_Trans l -> list Value) with
   | [] => fun _ : TList_Trans [] => []
   | t :: ts =>
     fun ps : TList_Trans (t :: ts) =>
       cst (VTyp_TRN t) (fst ps) :: (listTypTr ts (snd ps))
   end.



Program Definition Value_TRN_P (v: Value) (t: VTyp) (k: ValueTyping v t) :
  VTyp_TRN t := _.

Next Obligation.
  intros.
  unfold VTyp_TRN.
  unfold vtypExt.
  destruct t as [T0 p].
  destruct v as [T1 v].
  destruct v.
  inversion k; subst.
  simpl in *.
  subst T.
  rewrite <- H.
  exact v.
Defined.


Definition Value_TRN (v : Value) (t : VTyp) : ValueTyping v t -> VTyp_TRN t :=
 let (T0, p) as s return (ValueTyping v s -> proj1_sig s) := t in
 let (T1, v0) as s return (ValueTyping s (exist ValTyp T0 p) -> T0) := v in
   (fun k : ValueTyping (existT ValueI T1 v0) (exist ValTyp T0 p) =>
         match k with
         | @ValueTypingC _ _ T H H0 =>
             (fun (H1 : T = T0) (_ : ValTyp T) =>
              eq_rect T1 (fun T2 : Type => T2) (ValueI2T _ v0) T0 H1) H H0
         end).



Fixpoint TList_TRN (ts: list VTyp) : list Type :=
  match ts with
      | nil => nil
      | (t::ts') => (VTyp_Trans t) :: (TList_TRN ts')
  end.                                    

Fixpoint FType_mk (ts: list Type) (t: Type) : Type :=
  match ts with
    | nil => unit -> MM W t
    | t' :: ts' => t' -> FType_mk ts' t
  end.                                

Fixpoint FTyp_TRN (ft: FTyp) : Type :=
  match ft with
    | FT tenv t => let ts := TList_TRN (map snd tenv) in
                   FType_mk ts (VTyp_TRN t)
 end.                               




Lemma listTypTrL1 (t: VTyp) (ts: list VTyp)
                   (v: VTyp_Trans t) (pv: TList_Trans ts) :
  listTypTr (t::ts) (v,pv) = (cst (vtypExt t) v) :: (listTypTr ts pv).

unfold VTyp_Trans in v.
unfold vtypExt in v.
unfold vtypExt.
simpl.
unfold VTyp_TRN.
unfold vtypExt.
auto.
Defined.



Inductive IsTypeList : list Type -> list Value -> Type :=
  | IsTLN : IsTypeList nil nil
  | IsTLC : forall (ts: list Type) (vs: list Value) (t: Type) (v: t),
              IsTypeList ts vs -> IsTypeList (t::ts) (cst t v::vs).


Definition valTC2_Trans (tenv: valTC) : list (Id * Type) :=
  map (fun (x: Id * VTyp) => (fst x, VTyp_Trans (snd x))) tenv.

Definition valTC1_Trans (tenv: valTC) : list Type :=
  map (fun (x: Id * VTyp) => (VTyp_Trans (snd x))) tenv.

Fixpoint valTC_TransA (tenv: valTC) : Type :=
  match tenv with
      | nil => unit
      | (t::ts) => (VTyp_Trans (snd t)) * (valTC_TransA ts)
  end.                                    
  
Definition FTyp_Trans1 (ft: FTyp) : Type :=
  match ft with
    | FT tenv t => valTC_Trans tenv -> MM W (VTyp_Trans t)
  end.                                                

Definition FTyp_Trans (ft: FTyp) : Type :=
   valTC_Trans (extParType ft) -> MM W (VTyp_Trans (extRetType ft)).                                                
Definition funTC2_Trans (tenv: funTC) : list (Id * Type) :=
  map (fun (x: Id * FTyp) => (fst x, FTyp_Trans (snd x))) tenv.

Definition funTC1_Trans (tenv: funTC) : list Type :=
  map (fun (x: Id * FTyp) => (FTyp_Trans (snd x))) tenv.

Fixpoint funTC_Trans (tenv: funTC) : Type :=
  match tenv with
      | nil => unit
      | (t::ts) => (FTyp_Trans (snd t)) * (funTC_Trans ts)
  end.                                    

Definition Value_Trans (v: Value) :  projT1 v := cstExt v.

  
  
(***************************************************************)

Definition valTyp (v: Value) : Type := projT1 v.

Definition vList_Typ_Trans (ls: list Value) : Type :=
      tlist2type (map valTyp ls).

Program Fixpoint vList_Trans_P (ls: list Value) : vList_Typ_Trans ls
  := _.
Next Obligation.
  fix rec 1.
  intros.
  destruct ls as [ | v vs].
  exact tt.
  destruct v as [t v].
  destruct v.
  specialize (rec vs).
  constructor.
  simpl.
  exact v.
  exact rec. 
Defined.  

Fixpoint vList_Trans (ls: list Value) : vList_Typ_Trans ls :=
   match ls as ls return (vList_Typ_Trans ls) with
   | [] => tt
   | v :: vs => (cstExt v, vList_Trans vs)
   end.



Definition valEnv_Typ_Trans (env: valEnv) : Type :=
    vList_Typ_Trans (map snd env).

Definition valEnv_Trans (env: valEnv) : 
  valEnv_Typ_Trans env := vList_Trans (map snd env).

Lemma WT_Value_Trans (v: Value) (t: VTyp) :
   ValueTyping v t -> valTyp v = VTyp_Trans t.
  intros.
  inversion H; subst.
  unfold valTyp.
  unfold VTyp_Trans.
  unfold vtypExt.
  auto.
Defined.
    
Lemma WT_valEnv_Trans_eq (tenv: valTC) (env: valEnv) :
  EnvTyping env tenv -> 
              valTC_Trans tenv = valEnv_Typ_Trans env.
  intros.
  dependent induction X.  
  compute.
  reflexivity.
  assert (valTC_Trans ((k, v2) :: ls2) =
          prod (VTyp_Trans v2) (valTC_Trans ls2)).  
  reflexivity.
  assert (valEnv_Typ_Trans ((k, v1) :: ls1) =
          prod (valTyp v1) (valEnv_Typ_Trans ls1)).
  reflexivity.
  rewrite H.
  rewrite H0.
  rewrite IHX.
  eapply WT_Value_Trans in r.
  rewrite r.
  auto.
Defined.  

Lemma WT_valEnv_Trans (tenv: valTC) (env: valEnv) :
  EnvTyping env tenv -> valTC_Trans tenv.
intros.
assert (valEnv_Typ_Trans env).
exact (valEnv_Trans env).
rewrite (WT_valEnv_Trans_eq tenv env).
exact X0.
exact X.
Defined.

  
(***********************************************************)

Definition E_Trans0 :=
    fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
          (e: Exp) (t: VTyp) (ET: ExpTyping ftenv tenv fenv e t) => 
        MM W (VTyp_Trans t).

Definition F_Trans0 := fun (f: Fun) (ft: FTyp)
               (ET: FunTyping f ft) => FTyp_Trans ft.

Definition Q_Trans0 :=
    fun (ftenv: funTC) (fenv: funEnv) (q: QFun) (ft: FTyp) 
                (ET: QFunTyping ftenv fenv q ft) => 
                        FTyp_Trans ft.

Definition P_Trans0 :=
    fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                (ps: Prms) (ts: PTyp) 
                (ET: PrmsTyping ftenv tenv fenv ps ts) => 
       MM W (PTyp_Trans ts).


Definition ExpTypingTrans0_rect :=
  ExpTyping_str_rect 
           F_Trans0 Q_Trans0 E_Trans0 P_Trans0. 


(*****************************************************************)


Definition E_Trans :=
  fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
          (e: Exp) (t: VTyp) (ET: ExpTyping ftenv tenv fenv e t) => 
  FEnvTyping fenv ftenv ->   
  forall env: valEnv,
        EnvTyping env tenv -> 
        MM W (VTyp_Trans t).


Definition F_Trans :=
  fun (f: Fun) (ft: FTyp)
      (FT: FunTyping f ft) =>
  forall env: valEnv,
       EnvTyping env (extParType ft) ->      
       MM W (VTyp_Trans (extRetType ft)). 
                        

Definition Q_Trans :=
  fun (ftenv: funTC) (fenv: funEnv) (q: QFun) (ft: FTyp) 
                          (QT: QFunTyping ftenv fenv q ft) =>
  FEnvTyping fenv ftenv ->          
  forall env: valEnv,
       EnvTyping env (extParType ft) ->     
       MM W (VTyp_Trans (extRetType ft)). 


Definition P_Trans :=
  fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                (ps: Prms) (ts: PTyp) 
                (ET: PrmsTyping ftenv tenv fenv ps ts) => 
  FEnvTyping fenv ftenv ->   
  forall env: valEnv,
        EnvTyping env tenv -> 
        MM W (PTyp_Trans ts).



Definition ExpTypingTrans_rect :=
  ExpTyping_str_rect 
           F_Trans Q_Trans E_Trans P_Trans. 


Definition FunTypingTrans_rect :=
  FunTyping_str_rect 
           F_Trans Q_Trans E_Trans P_Trans. 


Definition ParTypingTrans_rect :=
  PrmsTyping_str_rect  
           F_Trans Q_Trans E_Trans P_Trans. 


Definition QFunTypingTrans_rect :=
  QFunTyping_str_rect 
           F_Trans Q_Trans E_Trans P_Trans. 


Program Fixpoint envTypingList_P (fps : valTC)
               (t0 : TList_Trans (map snd fps)):
  EnvTyping (mkVEnv fps (listTypTr (map snd fps) t0)) fps := _.
Next Obligation.
  unfold mkVEnv.
  fix rec 1.
  intros.
  destruct fps.
  constructor.

  destruct p.
  simpl in *.
  destruct t0.
  specialize (rec fps t).
  destruct v.

  constructor.
  constructor.
  simpl.
  auto.
  simpl.
  exact v.
  simpl.
  auto.
Defined.  



Fixpoint envTypingList (fps : valTC) :
  forall t0 : TList_Trans (map snd fps),
  EnvTyping (mkVEnv fps (listTypTr (map snd fps) t0)) fps := 
   match
     fps as l
     return
       (forall t1 : TList_Trans (map snd l),
        EnvTyping (interleave (map fst l) (listTypTr (map snd l) t1)) l)
   with
   | [] => fun _ : TList_Trans (map snd []) => MatchEnvs_NilT ValueTyping
   | p :: fps0 =>
       fun t1 : TList_Trans (map snd (p :: fps0)) =>
       
       (let
          (i, v) as p0
           return
             (forall t2 : TList_Trans (map snd (p0 :: fps0)),
              EnvTyping
                (interleave (map fst (p0 :: fps0))
                   (listTypTr (map snd (p0 :: fps0)) t2)) 
                (p0 :: fps0)) := p in
         
        fun t2 : TList_Trans (map snd ((i, v) :: fps0)) =>
        let
          (v0, t) as p0
           return
             (EnvTyping
                ((i, cst (VTyp_TRN v) (fst p0))
                 :: interleave (map fst fps0)
                      (listTypTr (map snd fps0) (snd p0))) 
                ((i, v) :: fps0)) := t2 in
       
        (let
           (x, v1) as s
            return
              (forall v1 : VTyp_Trans s,
               EnvTyping
                 ((i, cst (VTyp_TRN s) (fst (v1, t)))
                  :: interleave (map fst fps0)
                       (listTypTr (map snd fps0) (snd (v1, t))))
                 ((i, s) :: fps0)) := v in

         fun v2 : VTyp_Trans (exist ValTyp x v1) =>
         MatchEnvs_ConsT ValueTyping
           (interleave (map fst fps0)
              (listTypTr (map snd fps0) (snd (v2, t)))) fps0 i
           (cst (VTyp_TRN (exist ValTyp x v1)) (fst (v2, t)))
           (exist ValTyp x v1)
           (ValueTypingC (cst (VTyp_TRN (exist ValTyp x v1)) (fst (v2, t)))
              (exist ValTyp x v1) eq_refl v1) (envTypingList fps0 t)) v0) t1
   end.



Lemma valTypId (xts: list Type) (ps : tlist2type xts) :
  xts = map valTyp (listTypTrA xts ps).
  revert ps.
  induction xts.
  auto.
  intros.  
  destruct ps.
  simpl.
  specialize (IHxts t).
  rewrite IHxts at 1.
  auto.
Defined.

Lemma tlistTypId (xts: list Type) (ps : tlist2type xts) :
  tlist2type xts = vList_Typ_Trans (listTypTrA xts ps).
  unfold vList_Typ_Trans.
  rewrite valTypId at 1.
  reflexivity.
Defined.

Lemma tlistTypIdA (xts: list Type) (ps : tlist2type xts) :
  tlist2type xts = tlist2type (map valTyp (listTypTrA xts ps)).
  rewrite valTypId at 1.
  reflexivity.
Defined.


Lemma valTypIdRF1 : forall (xts: list Type) (ps: tlist2type xts),
           tlist2type (map valTyp (listTypTrA xts ps)).        
  intros.
  induction xts.
  simpl.
  simpl in ps.
  exact ps.
  destruct ps as [x ps].
  simpl.
  specialize (IHxts ps).
  econstructor.
  exact x.
  exact IHxts.
Defined.  

Program Fixpoint valTypIdRF_P (xts: list Type) (ps: tlist2type xts) :
           tlist2type (map valTyp (listTypTrA xts ps)) := _.  
Next Obligation.
 fix rec 1.
 intros.
 destruct xts. 
 simpl.
 exact ps.
 destruct ps as [x ps].
 specialize (rec xts ps).
 simpl.
 constructor. 
 exact x.
 exact rec.
Defined.


Fixpoint valTypIdRF (xts: list Type) (ps: tlist2type xts) :
  tlist2type (map valTyp (listTypTrA xts ps)) :=
   (match xts as ls
     return
     (forall ps0 : tlist2type ls,
                  tlist2type (map valTyp (listTypTrA ls ps0)))
   with
   | [] => fun ps0 : tlist2type [] => ps0
   | T :: xts0 => fun ps0 : tlist2type (T :: xts0) =>
                   ((fst ps0), valTypIdRF xts0 (snd ps0))
   end) ps.


Definition valTypIdRF_inv (xts: list Type) (ps: tlist2type xts)
     (x: tlist2type (map valTyp (listTypTrA xts ps))) :
     tlist2type xts := ps.                                   



Definition ltypFS1 (xts: list Type) (ps: tlist2type xts) :
                   sigT (fun ps: tlist2type xts =>
                           tlist2type (map valTyp (listTypTrA xts ps))) :=
 existT
   (fun ps0 : tlist2type xts => tlist2type (map valTyp (listTypTrA xts ps0)))
   ps (valTypIdRF xts ps).

Definition ltypFS2 (xts: list Type) 
     (x: sigT (fun ps: tlist2type xts =>
                          tlist2type (map valTyp (listTypTrA xts ps)))) :
     tlist2type xts := projT1 x.                                   

Lemma ltypFSId1 : forall (xts: list Type) (ps: tlist2type xts),
     ltypFS2 xts (ltypFS1 xts ps) = ps.                 
intros.
simpl.
auto.
Defined.

  
Lemma listValueId (vs: list Value) :
   vs = listTypTrA (map valTyp vs) (vList_Trans vs).
  induction vs.
  simpl.
  auto.
  simpl.
  rewrite <- IHvs.
  destruct a.
  destruct v.
  simpl.
  unfold cst.
  unfold cstExt.
  simpl.
  auto.
Defined.  



(** main translation function *)
Program Fixpoint Exp_Trans 
        (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (e: Exp) (t: VTyp) (ET: ExpTyping ftenv tenv fenv e t) :
  FEnvTyping fenv ftenv ->   
  forall env: valEnv,
        EnvTyping env tenv -> 
        MM W (VTyp_Trans t) := _ 
with Fun_Trans 
               (f: Fun) (ft: FTyp) 
               (ET: FunTyping f ft) :
   forall env: valEnv,
       EnvTyping env (extParType ft) ->     
       MM W (VTyp_Trans (extRetType ft)) := _ 
with QFun_Trans 
                (ftenv: funTC) (fenv: funEnv) (q: QFun) (ft: FTyp)
                (ET: QFunTyping ftenv fenv q ft) :
  FEnvTyping fenv ftenv ->          
  forall env: valEnv,
       EnvTyping env (extParType ft) ->     
       MM W (VTyp_Trans (extRetType ft)) := _ 
with Prms_Trans 
                (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                (ps: Prms) (ts: PTyp) 
                (ET: PrmsTyping ftenv tenv fenv ps ts) :
  FEnvTyping fenv ftenv ->   
  forall env: valEnv,
        EnvTyping env tenv -> 
        MM W (PTyp_Trans ts) := _.
 
Next Obligation.

  eapply ExpTypingTrans_rect.
  - (* forall2_nil *)
    unfold Par_SSL.
    intros.
    constructor.
  - (* forall2_cons *)
    unfold Par_SSL.
    intros.
    econstructor.
    exact X0.
    exact X.  
  - (* matchenvs_nil *)
    unfold Par_SSA.
    constructor.
  - (* matchenvs_cons *)
    unfold Par_SSA.
    intros.
    econstructor.
    exact X0.
    exact X.    
  - (* matchenvs2_split *)
    unfold Par_SSB, Par_SSA.
    intros.
    econstructor.
    exact m0.
    exact m1.
    assumption.
    assumption.
    exact X.
    exact X0.
    exact X1.
  - (* funz *) 
    unfold E_Trans, F_Trans.  
    unfold FTyp_Trans.
    intros.
    simpl in *.
    specialize (X m env X0).
    exact X.
  - (* funs *)
    unfold E_Trans, F_Trans.
    intros.
    unfold FTyp_Trans.
    assert (FEnvTyping ((x, FC fenv tenv e0 e1 x n) :: fenv)
        ((x, FT tenv t) :: ftenv)).
    + eapply updateFEnvLemma.
      exact m.
      exact k2.
    + simpl in *.
      specialize (X X2 env X1).
      exact X.
  - (* QF *)
    unfold Q_Trans, F_Trans.
    intros.
    simpl in *.
    specialize (X env X1).
    exact X.
  - (* FVar *)
    unfold Par_SSB, Q_Trans, F_Trans.
    intros.
    destruct ft.
    inversion X; subst; clear X.
    simpl in *.
    specialize (X4 env X1).
    exact X4.
  - (* modify *)
    unfold E_Trans.
    intros.
    simpl.
    destruct XF.
    unfold MM.
    inversion k; subst.
    + inversion H; subst.
      subst T.
      simpl in H0.
      destruct v.
      destruct v.
      simpl in H0.
      clear k.
      clear H.
      clear H1.
      rewrite H0 in v.
      intros.
      exact (b_eval0 X1 v, b_exec0 X1 v). 
    + inversion X1; subst.
      eapply ExRelValT with (x0:=x) (t:=vtyp T1) in X0.
      destruct X0.
      destruct x0.
      destruct v0.
      inversion v; subst.
      subst T.
      simpl in H.
      clear f.
      clear v.
      clear H0.
      rewrite H in v0. 
      intros.
      exact (b_eval0 X0 v0, b_exec0 X0 v0). 
      exact X2. 
  - (* return *)
    unfold E_Trans.
    intros.
    simpl.
    inversion k; subst.  
    + inversion H; subst.
      subst T. 
      destruct v.    
      destruct v.
      simpl in H0.
      unfold VTyp_Trans.
      unfold vtypExt.
      clear k H H1.
      rewrite H0 in v.    
      exact (ret v).
    + inversion X1; subst.
      eapply ExRelValT with (x0:=x) (t0:=t) in X0.
      destruct X0.
      destruct x0.
      destruct v0.      
      inversion v; subst.
      subst T.
      simpl in H.
      clear f v H0.
      rewrite H in v0.   
      exact (ret v0).
      exact X2.
  - (* bindn *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X1 env X2).
    specialize (X0 X1 env X2).
    exact (bind X (fun _ => X0)).
  - (* binds *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X1 env X2).
    specialize (X0 X1).
    unfold MM.
    intro w1.
(**)
    unfold MM in X.
    apply X in w1.
    destruct w1 as [v w2].
    eapply (updateVEnvLemma env tenv x
                            (cst (VTyp_Trans t1) v) t1) in X2.
    specialize (X0 (updateE env x (cst (VTyp_Trans t1) v))).
    apply X0 in X2.
    apply (X2 w2).
    unfold VTyp_Trans.
    unfold vtypExt.
    constructor.
    simpl.
    reflexivity.
    constructor.
  - (* bindms *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (overrideFEnvLemma fenvP fenv ftenvP ftenv m2 X0).  
    intro.
    rewrite h2 in X.
    rewrite h3 in X.
    specialize (X X2).
    specialize (overrideVEnvLemma envP env tenvP tenv k1 X1).
    intros.
    rewrite h1 in X.
    apply X in X3.
    exact X3.
  - (* apply *)
    unfold E_Trans, Q_Trans, P_Trans.
    intros.
    simpl in *.
    specialize (X X1).
    specialize (X0 X1 env X2).     
    simpl in X.
    inversion k2; subst.
    unfold env2ptyp in H3.
    inversion H3; subst. 
    simpl in X0.
    unfold MM; intros.
    unfold MM in X0.
    specialize (X0 X4); clear X4.
    destruct X0.
    clear H3.
    assert (EnvTyping (mkVEnv fps (listTypTr (map snd fps) t0)) fps).
    apply envTypingList.    
    apply X in X0.
    apply (X0 w). 
    
  - (* val *)
    unfold E_Trans.
    intros.
    simpl.
    unfold VTyp_Trans.
    unfold vtypExt.
    inversion k.
    subst T.
    rewrite <- H.
    exact (ret (cstExt v)).
  - (* ifthenelse *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X2 env X3).
    specialize (X0 X2 env X3).
    specialize (X1 X2 env X3).
    
    unfold MM; intro.
    unfold MM in X.
    specialize (X X4).
    destruct X.
    simpl in v.
    destruct v.
    exact (X0 w).
    exact (X1 w).
  - (* PS *)
    unfold Par_SSL, P_Trans.
    unfold E_Trans.
    intros.
    simpl.
    induction X.
    simpl.
    exact (ret tt).
    simpl.
    specialize (p0 X0 env X1).
    inversion m; subst.
    specialize (IHX X3).
    unfold MM; intro.
    specialize (p0 X4).
    destruct p0.
    specialize (IHX w).
    destruct IHX.
    exact (v, t, w0).
Defined.    
    
Next Obligation.
  
  eapply FunTypingTrans_rect.

  - (* forall2_nil *)
    unfold Par_SSL.
    intros.
    constructor.
  - (* forall2_cons *)
    unfold Par_SSL.
    intros.
    econstructor.
    exact X0.
    exact X.  
  - (* matchenvs_nil *)
    unfold Par_SSA.
    constructor.
  - (* matchenvs_cons *)
    unfold Par_SSA.
    intros.
    econstructor.
    exact X0.
    exact X.    
  - (* matchenvs2_split *)
    unfold Par_SSB, Par_SSA.
    intros.
    econstructor.
    exact m0.
    exact m1.
    assumption.
    assumption.
    exact X.
    exact X0.
    exact X1.
  - (* funz *) 
    unfold E_Trans, F_Trans.  
    unfold FTyp_Trans.
    intros.
    simpl in *.
    specialize (X m env X0).
    exact X.
  - (* funs *)
    unfold E_Trans, F_Trans.
    intros.
    assert (FEnvTyping ((x, FC fenv tenv e0 e1 x n) :: fenv)
        ((x, FT tenv t) :: ftenv)).
    + eapply updateFEnvLemma.
      exact m.
      exact k2.
    + simpl in *.
      specialize (X X2 env X1).
      exact X.
  - (* QF *)
    unfold Q_Trans, F_Trans.
    intros.
    simpl in *.
    specialize (X env X1).
    exact X.
  - (* FVar *)
    unfold Par_SSB, Q_Trans, F_Trans.
    intros.
    destruct ft.
    inversion X; subst; clear X.
    simpl in *.
    specialize (X4 env X1).
    exact X4.
  - (* modify *)
    unfold E_Trans.
    intros.
    simpl.
    destruct XF.
    unfold MM.
    inversion k; subst.
    + inversion H; subst.
      subst T.
      simpl in H0.
      destruct v.
      destruct v.
      simpl in H0.
      clear k.
      clear H.
      clear H1.
      rewrite H0 in v.
      intros.
      exact (b_eval0 X1 v, b_exec0 X1 v). 
    + inversion X1; subst.
      eapply ExRelValT with (x0:=x) (t:=vtyp T1) in X0.
      destruct X0.
      destruct x0.
      destruct v0.
      inversion v; subst.
      subst T.
      simpl in H.
      clear f.
      clear v.
      clear H0.
      rewrite H in v0. 
      intros.
      exact (b_eval0 X0 v0, b_exec0 X0 v0). 
      exact X2. 
  - (* return *)
    unfold E_Trans.
    intros.
    simpl.
    inversion k; subst.  
    + inversion H; subst.
      subst T. 
      destruct v.    
      destruct v.
      simpl in H0.
      unfold VTyp_Trans.
      unfold vtypExt.
      clear k H H1.
      rewrite H0 in v.    
      exact (ret v).
    + inversion X1; subst.
      eapply ExRelValT with (x0:=x) (t0:=t) in X0.
      destruct X0.
      destruct x0.
      destruct v0.      
      inversion v; subst.
      subst T.
      simpl in H.
      clear f v H0.
      rewrite H in v0.   
      exact (ret v0).
      exact X2.
  - (* bindn *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X1 env X2).
    specialize (X0 X1 env X2).
    exact (bind X (fun _ => X0)).
  - (* binds *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X1 env X2).
    specialize (X0 X1).
    unfold MM.
    intro w1.
(**)
    unfold MM in X.
    apply X in w1.
    destruct w1 as [v w2].
    eapply (updateVEnvLemma env tenv x
                            (cst (VTyp_Trans t1) v) t1) in X2.
    specialize (X0 (updateE env x (cst (VTyp_Trans t1) v))).
    apply X0 in X2.
    apply (X2 w2).
    unfold VTyp_Trans.
    unfold vtypExt.
    constructor.
    simpl.
    reflexivity.
    constructor.
  - (* bindms *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (overrideFEnvLemma fenvP fenv ftenvP ftenv m2 X0).  
    intro.
    rewrite h2 in X.
    rewrite h3 in X.
    specialize (X X2).
    specialize (overrideVEnvLemma envP env tenvP tenv k1 X1).
    intros.
    rewrite h1 in X.
    apply X in X3.
    exact X3.
  - (* apply *)
    unfold E_Trans, Q_Trans, P_Trans.
    intros.
    simpl in *.
    specialize (X X1).
    specialize (X0 X1 env X2).     
    simpl in X.
    inversion k2; subst.
    unfold env2ptyp in H3.
    inversion H3; subst. 
    simpl in X0.
    unfold MM; intros.
    unfold MM in X0.
    specialize (X0 X4); clear X4.
    destruct X0.
    clear H3.
    assert (EnvTyping (mkVEnv fps (listTypTr (map snd fps) t0)) fps).
    apply envTypingList.    
    apply X in X0.
    apply (X0 w). 
    
  - (* val *)
    unfold E_Trans.
    intros.
    simpl.
    unfold VTyp_Trans.
    unfold vtypExt.
    inversion k.
    subst T.
    rewrite <- H.
    exact (ret (cstExt v)).
  - (* ifthenelse *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X2 env X3).
    specialize (X0 X2 env X3).
    specialize (X1 X2 env X3).
    
    unfold MM; intro.
    unfold MM in X.
    specialize (X X4).
    destruct X.
    simpl in v.
    destruct v.
    exact (X0 w).
    exact (X1 w).
  - (* PS *)
    unfold Par_SSL, P_Trans.
    unfold E_Trans.
    intros.
    simpl.
    induction X.
    simpl.
    exact (ret tt).
    simpl.
    specialize (p0 X0 env X1).
    inversion m; subst.
    specialize (IHX X3).
    unfold MM; intro.
    specialize (p0 X4).
    destruct p0.
    specialize (IHX w).
    destruct IHX.
    exact (v, t, w0).
Defined.    



Next Obligation.

  eapply ParTypingTrans_rect.

  - (* forall2_nil *)
    unfold Par_SSL.
    intros.
    constructor.
  - (* forall2_cons *)
    unfold Par_SSL.
    intros.
    econstructor.
    exact X0.
    exact X.  
  - (* matchenvs_nil *)
    unfold Par_SSA.
    constructor.
  - (* matchenvs_cons *)
    unfold Par_SSA.
    intros.
    econstructor.
    exact X0.
    exact X.    
  - (* matchenvs2_split *)
    unfold Par_SSB, Par_SSA.
    intros.
    econstructor.
    exact m0.
    exact m1.
    assumption.
    assumption.
    exact X.
    exact X0.
    exact X1.
  - (* funz *) 
    unfold E_Trans, F_Trans.  
    unfold FTyp_Trans.
    intros.
    simpl in *.
    specialize (X m env X0).
    exact X.
  - (* funs *)
    unfold E_Trans, F_Trans.
    intros.
    unfold FTyp_Trans.
    intros.
    assert (FEnvTyping ((x, FC fenv tenv e0 e1 x n) :: fenv)
        ((x, FT tenv t) :: ftenv)).
    + eapply updateFEnvLemma.
      exact m.
      exact k2.
    + simpl in *.
      specialize (X X2 env X1).
      exact X.
  - (* QF *)
    unfold Q_Trans, F_Trans.
    intros.
    simpl in *.
    specialize (X env X1).
    exact X.
  - (* FVar *)
    unfold Par_SSB, Q_Trans, F_Trans.
    intros.
    destruct ft.
    inversion X; subst; clear X.
    simpl in *.
    specialize (X4 env X1).
    exact X4.
  - (* modify *)
    unfold E_Trans.
    intros.
    simpl.
    destruct XF.
    unfold MM.
    inversion k; subst.
    + inversion H; subst.
      subst T.
      simpl in H0.
      destruct v.
      destruct v.
      simpl in H0.
      clear k.
      clear H.
      clear H1.
      rewrite H0 in v.
      intros.
      exact (b_eval0 X1 v, b_exec0 X1 v). 
    + inversion X1; subst.
      eapply ExRelValT with (x0:=x) (t:=vtyp T1) in X0.
      destruct X0.
      destruct x0.
      destruct v0.
      inversion v; subst.
      subst T.
      simpl in H.
      clear f.
      clear v.
      clear H0.
      rewrite H in v0. 
      intros.
      exact (b_eval0 X0 v0, b_exec0 X0 v0). 
      exact X2. 
  - (* return *)
    unfold E_Trans.
    intros.
    simpl.
    inversion k; subst.  
    + inversion H; subst.
      subst T. 
      destruct v.    
      destruct v.
      simpl in H0.
      unfold VTyp_Trans.
      unfold vtypExt.
      clear k H H1.
      rewrite H0 in v.    
      exact (ret v).
    + inversion X1; subst.
      eapply ExRelValT with (x0:=x) (t0:=t) in X0.
      destruct X0.
      destruct x0.
      destruct v0.      
      inversion v; subst.
      subst T.
      simpl in H.
      clear f v H0.
      rewrite H in v0.   
      exact (ret v0).
      exact X2.
  - (* bindn *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X1 env X2).
    specialize (X0 X1 env X2).
    exact (bind X (fun _ => X0)).
  - (* binds *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X1 env X2).
    specialize (X0 X1).
    unfold MM.
    intro w1.
(**)
    unfold MM in X.
    apply X in w1.
    destruct w1 as [v w2].
    eapply (updateVEnvLemma env tenv x
                            (cst (VTyp_Trans t1) v) t1) in X2.
    specialize (X0 (updateE env x (cst (VTyp_Trans t1) v))).
    apply X0 in X2.
    apply (X2 w2).
    unfold VTyp_Trans.
    unfold vtypExt.
    constructor.
    simpl.
    reflexivity.
    constructor.
  - (* bindms *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (overrideFEnvLemma fenvP fenv ftenvP ftenv m2 X0).  
    intro.
    rewrite h2 in X.
    rewrite h3 in X.
    specialize (X X2).
    specialize (overrideVEnvLemma envP env tenvP tenv k1 X1).
    intros.
    rewrite h1 in X.
    apply X in X3.
    exact X3.
  - (* apply *)
    unfold E_Trans, Q_Trans, P_Trans.
    intros.
    simpl in *.
    specialize (X X1).
    specialize (X0 X1 env X2).     
    simpl in X.
    inversion k2; subst.
    unfold env2ptyp in H3.
    inversion H3; subst. 
    simpl in X0.
    unfold MM; intros.
    unfold MM in X0.
    specialize (X0 X4); clear X4.
    destruct X0.
    clear H3.
    assert (EnvTyping (mkVEnv fps (listTypTr (map snd fps) t0)) fps).
    apply envTypingList.    
    apply X in X0.
    apply (X0 w). 
    
  - (* val *)
    unfold E_Trans.
    intros.
    simpl.
    unfold VTyp_Trans.
    unfold vtypExt.
    inversion k.
    subst T.
    rewrite <- H.
    exact (ret (cstExt v)).
  - (* ifthenelse *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X2 env X3).
    specialize (X0 X2 env X3).
    specialize (X1 X2 env X3).
    
    unfold MM; intro.
    unfold MM in X.
    specialize (X X4).
    destruct X.
    simpl in v.
    destruct v.
    exact (X0 w).
    exact (X1 w).
  - (* PS *)
    unfold Par_SSL, P_Trans.
    unfold E_Trans.
    intros.
    simpl.
    induction X.
    simpl.
    exact (ret tt).
    simpl.
    specialize (p0 X0 env X1).
    inversion m; subst.
    specialize (IHX X3).
    unfold MM; intro.
    specialize (p0 X4).
    destruct p0.
    specialize (IHX w).
    destruct IHX.
    exact (v, t, w0).
Defined.    

Next Obligation.

  eapply QFunTypingTrans_rect.

  - (* forall2_nil *)
    unfold Par_SSL.
    intros.
    constructor.
  - (* forall2_cons *)
    unfold Par_SSL.
    intros.
    econstructor.
    exact X0.
    exact X.  
  - (* matchenvs_nil *)
    unfold Par_SSA.
    constructor.
  - (* matchenvs_cons *)
    unfold Par_SSA.
    intros.
    econstructor.
    exact X0.
    exact X.    
  - (* matchenvs2_split *)
    unfold Par_SSB, Par_SSA.
    intros.
    econstructor.
    exact m0.
    exact m1.
    assumption.
    assumption.
    exact X.
    exact X0.
    exact X1.
  - (* funz *) 
    unfold E_Trans, F_Trans.  
    unfold FTyp_Trans.
    intros.
    simpl in *.
    specialize (X m env X0).
    exact X.
  - (* funs *)
    unfold E_Trans, F_Trans.
    intros.
    unfold FTyp_Trans.
    intros.
    assert (FEnvTyping ((x, FC fenv tenv e0 e1 x n) :: fenv)
        ((x, FT tenv t) :: ftenv)).
    + eapply updateFEnvLemma.
      exact m.
      exact k2.
    + simpl in *.
      specialize (X X2 env X1).
      exact X.
  - (* QF *)
    unfold Q_Trans, F_Trans.
    intros.
    simpl in *.
    specialize (X env X1).
    exact X.
  - (* FVar *)
    unfold Par_SSB, Q_Trans, F_Trans.
    intros.
    destruct ft.
    inversion X; subst; clear X.
    simpl in *.
    specialize (X4 env X1).
    exact X4.
  - (* modify *)
    unfold E_Trans.
    intros.
    simpl.
    destruct XF.
    unfold MM.
    inversion k; subst.
    + inversion H; subst.
      subst T.
      simpl in H0.
      destruct v.
      destruct v.
      simpl in H0.
      clear k.
      clear H.
      clear H1.
      rewrite H0 in v.
      intros.
      exact (b_eval0 X1 v, b_exec0 X1 v). 
    + inversion X1; subst.
      eapply ExRelValT with (x0:=x) (t:=vtyp T1) in X0.
      destruct X0.
      destruct x0.
      destruct v0.
      inversion v; subst.
      subst T.
      simpl in H.
      clear f.
      clear v.
      clear H0.
      rewrite H in v0. 
      intros.
      exact (b_eval0 X0 v0, b_exec0 X0 v0). 
      exact X2. 
  - (* return *)
    unfold E_Trans.
    intros.
    simpl.
    inversion k; subst.  
    + inversion H; subst.
      subst T. 
      destruct v.    
      destruct v.
      simpl in H0.
      unfold VTyp_Trans.
      unfold vtypExt.
      clear k H H1.
      rewrite H0 in v.    
      exact (ret v).
    + inversion X1; subst.
      eapply ExRelValT with (x0:=x) (t0:=t) in X0.
      destruct X0.
      destruct x0.
      destruct v0.      
      inversion v; subst.
      subst T.
      simpl in H.
      clear f v H0.
      rewrite H in v0.   
      exact (ret v0).
      exact X2.
  - (* bindn *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X1 env X2).
    specialize (X0 X1 env X2).
    exact (bind X (fun _ => X0)).
  - (* binds *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X1 env X2).
    specialize (X0 X1).
    unfold MM.
    intro w1.
(**)
    unfold MM in X.
    apply X in w1.
    destruct w1 as [v w2].
    eapply (updateVEnvLemma env tenv x
                            (cst (VTyp_Trans t1) v) t1) in X2.
    specialize (X0 (updateE env x (cst (VTyp_Trans t1) v))).
    apply X0 in X2.
    apply (X2 w2).
    unfold VTyp_Trans.
    unfold vtypExt.
    constructor.
    simpl.
    reflexivity.
    constructor.
  - (* bindms *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (overrideFEnvLemma fenvP fenv ftenvP ftenv m2 X0).  
    intro.
    rewrite h2 in X.
    rewrite h3 in X.
    specialize (X X2).
    specialize (overrideVEnvLemma envP env tenvP tenv k1 X1).
    intros.
    rewrite h1 in X.
    apply X in X3.
    exact X3.
  - (* apply *)
    unfold E_Trans, Q_Trans, P_Trans.
    intros.
    simpl in *.
    specialize (X X1).
    specialize (X0 X1 env X2).     
    simpl in X.
    inversion k2; subst.
    unfold env2ptyp in H3.
    inversion H3; subst. 
    simpl in X0.
    unfold MM; intros.
    unfold MM in X0.
    specialize (X0 X4); clear X4.
    destruct X0.
    clear H3.
    assert (EnvTyping (mkVEnv fps (listTypTr (map snd fps) t0)) fps).
    apply envTypingList.    
    apply X in X0.
    apply (X0 w). 
    
  - (* val *)
    unfold E_Trans.
    intros.
    simpl.
    unfold VTyp_Trans.
    unfold vtypExt.
    inversion k.
    subst T.
    rewrite <- H.
    exact (ret (cstExt v)).
  - (* ifthenelse *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X2 env X3).
    specialize (X0 X2 env X3).
    specialize (X1 X2 env X3).
    
    unfold MM; intro.
    unfold MM in X.
    specialize (X X4).
    destruct X.
    simpl in v.
    destruct v.
    exact (X0 w).
    exact (X1 w).
  - (* PS *)
    unfold Par_SSL, P_Trans.
    unfold E_Trans.
    intros.
    simpl.
    induction X.
    simpl.
    exact (ret tt).
    simpl.
    specialize (p0 X0 env X1).
    inversion m; subst.
    specialize (IHX X3).
    unfold MM; intro.
    specialize (p0 X4).
    destruct p0.
    specialize (IHX w).
    destruct IHX.
    exact (v, t, w0).
Defined.    


(**********************************************************************)


Program Definition SOS_Exp_P 
                   (fenv: funEnv) (env: valEnv)
                   (e: Exp) (t: VTyp) (n: W) 
                   (k: SoundExp fenv env e t n) :
                              prod (vtypExt t) W := _.

Next Obligation.
  intros.
  unfold SoundExp in k.
  destruct k.
  split.
  - inversion v; subst.
    subst T.
    rewrite H in H0.
    assert (projT1 x).
    exact (cstExt x).
    unfold vtypExt.
    rewrite <- H.
    exact X.
  - destruct s.
    exact x0.
Defined.    

Definition SOS_Exp (fenv: funEnv) (env: valEnv)
                   (e: Exp) (t: VTyp) (n: W) 
                   (k: SoundExp fenv env e t n) :
  prod (vtypExt t) W :=
 let (x, v, s) := k in
 (match v with
    | @ValueTypingC _ _ T H H0 =>
        (fun (H1 : T = proj1_sig t) (H2 : ValTyp T) =>
         let H3 :=
           eq_ind (projT1 x) (fun T0 : Type => ValTyp T0) H2 (proj1_sig t) H1
           :
           ValTyp (proj1_sig t) in
         let X := cstExt x in
         eq_rect (projT1 x) (fun T0 : Type => T0) X (proj1_sig t) H1) H H0
    end, projT1 s).


Program Definition SOS_Fun
        (f: Fun) (ft: FTyp) (n: W)
        (k0: FunTyping f ft)
        (env: valEnv)
        (k: SoundFun env (extParType ft) f (extRetType ft) n)
                   : prod (vtypExt (extRetType ft)) W := _.

Next Obligation.
  intros.
  unfold SoundFun in k.
  destruct ft.
  (*simpl in m.*)
  simpl in k.
  simpl.
  destruct f.
  inversion k0; subst.
  specialize (k eq_refl).
  eapply SOS_Exp.
  exact k.
  specialize (k eq_refl).
  eapply SOS_Exp.
  exact k.
Defined.  


Program Definition SOS_QFun
         (ftenv: funTC) (fenv: funEnv)
         (q: QFun) (ft: FTyp) (n: W)
         (k0: QFunTyping ftenv fenv q ft)
         (env: valEnv)  
         (k: SoundQFun fenv env (extParType ft) q (extRetType ft) n)
              : prod (vtypExt (extRetType ft)) W := _.

Next Obligation.
  intros.
  unfold SoundQFun in k.
  destruct k.
  specialize (q0 n).
  eapply SOS_Fun in s.
  exact s.
  inversion k0; subst.
  inversion q0; subst.
  exact X.
  inversion X0.
  inversion q0; subst.
  inversion X0; subst.
  inversion X; subst.
  assert (findE ls1 x0 = None).
  eapply ExRelValTNone in X3.
  exact X3.
  exact H.
  inversion X1; subst.
  assert (findE (overrideE ls1 ((x0, f) :: ls3)) x0 =
          findE ((x0, f) :: ls3) x0).
  unfold overrideE.
  rewrite override_simpl2.
  auto.
  exact H0.
  unfold overrideE in H2.
  rewrite H2 in H1.
  simpl in H1.
  destruct (IdT.IdEqDec x0 x0) in H1.
  inversion H1; subst.
  exact X2.
  intuition n.
Defined.  

   
Program Fixpoint SOS_Prms
                   (fenv: funEnv) (env: valEnv)
                   (ps: Prms) (pt: PTyp) (n: W) 
                   (k: SoundPrms fenv env ps pt n) :
                              prod (PTyp_Trans pt) W := _.

Next Obligation.
  intros.
  unfold SoundPrms in k.
  destruct k as [es m].
  split.
(**)  
  - destruct m as [vs m1 k].
    destruct k as [m2 k].
    inversion m2; subst.
    unfold PTyp_Trans.
    revert m1.
    revert vs.
    revert k.
    revert ps.
    revert n.
    induction X.
    + simpl.
      intros.
      exact tt.
    + intros.
      destruct vs.
      inversion m1; subst.
      simpl in H.
      inversion H.
      destruct ps.
      destruct es.
      destruct k as [n2 k].
      inversion k; subst.
      inversion X0.
      inversion m2; subst.
      inversion X0; subst.
      
      assert (PrmsTyping emptyE emptyE emptyE (PS l) (PT l')).
      * constructor.
        exact X2.
      * specialize (IHX X3).
        inversion m1; subst.
        simpl in H.
        inversion H; subst.
        clear H.
        assert (isValueList2T (map Val vs) vs) as J1.
        constructor.
        auto.
        inversion X1; subst.

        eapply PrmsClos_aux1 in k.
        destruct k.
        destruct p.
       
        constructor.
        unfold VTyp_Trans.
        eapply (SOS_Exp fenv env e y n).
        unfold SoundExp.
        constructor 1 with (x:=v).
        exact H3.
        econstructor 1 with (x:=x).
        exact e0.

        specialize (IHX x (PS es) s vs J1).
        exact IHX.
  - destruct m.
    destruct p.
    destruct s.
    exact x0.
Defined.


(**********************************************************************)

(* statements of equivalence between SOS interpreter and monadic
translation *)


Definition InterEquivExp 
         (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (e: Exp) (t: VTyp) (k0: ExpTyping ftenv tenv fenv e t) 
         (k1: FEnvTyping fenv ftenv)   
         (env: valEnv)
         (k2: EnvTyping env tenv) (n: W) :=  
         Exp_Trans ftenv tenv fenv e t k0 k1 env k2 n = 
         SOS_Exp fenv env e t n 
                 (ExpEval ftenv tenv fenv e t k0 k1 env k2 n).


Definition InterEquivPrms  
         (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (ps: Prms) (pt: PTyp) (k0: PrmsTyping ftenv tenv fenv ps pt) 
         (k1: FEnvTyping fenv ftenv)   
         (env: valEnv)
         (k2: EnvTyping env tenv) (n: W) :=  
         Prms_Trans ftenv tenv fenv ps pt k0 k1 env k2 n = 
         SOS_Prms fenv env ps pt n 
                 (PrmsEval ftenv tenv fenv ps pt k0 k1 env k2 n).


Definition InterEquivFun 
         (f: Fun) (ft: FTyp) (k0: FunTyping f ft) 
         (env: valEnv) 
         (k1: EnvTyping env (extParType ft)) (n: W) :=
         Fun_Trans f ft k0 env k1 n = 
         SOS_Fun f ft n k0 env (FunEval f ft k0 env k1 n).


Definition InterEquivQFun
         (ftenv: funTC) (fenv: funEnv)
         (q: QFun) (ft: FTyp) 
         (k0: QFunTyping ftenv fenv q ft)
         (k1: FEnvTyping fenv ftenv)   
         (env: valEnv) 
         (k2: EnvTyping env (extParType ft)) (n: W) :=  
  QFun_Trans ftenv fenv q ft k0 k1 env k2 n = 
         SOS_QFun ftenv fenv q ft n k0 env   
                          (QFunEval ftenv fenv q ft k0 k1 env k2 n).


(*****************************)


Definition InterEquivExpP  
         (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (e: Exp) (t: VTyp) (k0: ExpTyping ftenv tenv fenv e t) :=
 forall (k1: FEnvTyping fenv ftenv)   
        (env: valEnv)
        (k2: EnvTyping env tenv) (n: W),
   InterEquivExp ftenv tenv fenv e t k0 k1 env k2 n.


Definition InterEquivPrmsP  
         (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (ps: Prms) (pt: PTyp) (k0: PrmsTyping ftenv tenv fenv ps pt) := 
  forall (k1: FEnvTyping fenv ftenv)   
         (env: valEnv)
         (k2: EnvTyping env tenv) (n: W),
   InterEquivPrms ftenv tenv fenv ps pt k0 k1 env k2 n.  


Definition InterEquivFunP 
           (f: Fun) (ft: FTyp) (k0: FunTyping f ft) :=
   forall (env: valEnv) 
          (k1: EnvTyping env (extParType ft)) (n: W),
     InterEquivFun f ft k0 env k1 n.


Definition InterEquivQFunP
         (ftenv: funTC) (fenv: funEnv)
         (q: QFun) (ft: FTyp) 
         (k0: QFunTyping ftenv fenv q ft) :=
  forall (k1: FEnvTyping fenv ftenv)   
         (env: valEnv) 
         (k2: EnvTyping env (extParType ft)) (n: W),
     InterEquivQFun ftenv fenv q ft k0 k1 env k2 n.

Definition ExpTypingIEq_rect :=
  ExpTyping_str_rect InterEquivFunP InterEquivQFunP 
                     InterEquivExpP InterEquivPrmsP. 


End SOS2Gallina.

