(*  DEC 2.0 language specification.
   Paolo Torrini  
   Universite' de Lille - CRIStAL-CNRS
*)

Require Import List.
Require Import Equality.
Require Import Eqdep.
Require Import PeanoNat.
Require Import Omega.
Require Import Eqdep FunctionalExtensionality Tactics.
Require Import JMeq.
Require Import ProofIrrelevance.
Require Import GenericMinMax.
Require Import NMaxMin.

Require Import AuxLibI1.
Require Import TypSpecI1. 
Require Import ModTypI1. 
Require Import LangSpecI1. 
Require Import StaticSemI1.
Require Import DynamicSemI1.
Require Import WeakenI1.
Require Import UniqueTypI1.
Require Import DerivDynI1.
Require Import TransPrelimI1.
Require Import TSoundnessI1.
Require Import SReducI1.
Require Import DetermI1.
Require Import PreReflI1.
Require Import ReflectI1.
Require Import PreInterI1.
Require Import InterprBaseI1.
Require Import InterpretI1.
Require Import CHeadAuxI1.

Add LoadPath "~/lib/CompCert-3.0.1" as compcert. 

(*Add LoadPath "/home/ptorrx/svnRepos/ptorrx-leuven/trunk/docsLille/develL5/CompCert-3.0.1" as compcert. *)
(*
Add LoadPath "/home/ptorrx/lib/CompCert-3.0.1/cfrontend" as compcert.cfrontend.
Add LoadPath "/home/ptorrx/lib/CompCert-3.0.1/common" as compcert.common.
*)

Require Import BinNat.
Require Import Integers.

Require VectorDef.

Require Import compcert.common.AST.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Csyntax.

Import ListNotations.
Import Integers.

Import Values.

Module CTrans (IdT: ModTyp) <: ModTyp.

Module CHeadAuxL := CHeadAux IdT.
Export CHeadAuxL.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Open Scope type_scope.

Definition coerce_s (s: TypSpecI1.signedness) : signedness :=
  match s with
  | TypSpecI1.Signed => Signed
  | TypSpecI1.Unsigned => Unsigned
  end.                

Definition coerce_i (i: TypSpecI1.intsize) : intsize :=
  match i with
  | TypSpecI1.I8 => I8
  | TypSpecI1.I16 => I16
  | TypSpecI1.I32 => I32
(*  | TypSpecI1.I64 => I32 *) 
  | TypSpecI1.IBool => IBool                      
  end.                


(* types *)
Fixpoint CTyp2C (t: CTyp) : type :=
  match t with
  | CVoid => Tvoid 
  | CInt i s => Tint (coerce_i i) (coerce_s s) noattr
  | CPtr T => Tpointer (CTyp2C T) noattr    
  end.
        
Definition VTyp2C (t: VTyp) : type := CTyp2C (cVTyp t).

Fixpoint typelistConv1 (ls: list type) : typelist :=
  match ls with
  | [] => Tnil
  | t::ts => Tcons t (typelistConv1 ts)
  end.                 

Definition FTyp2C1 (ft: FTyp) : type :=
  match ft with
  | FT ps t => match ps with
               | PT ts => Tfunction (typelistConv1
                              (map VTyp2C ts))
                                    (VTyp2C t) cc_default
               end
  end.


Definition FTyp2C (ft: FTyp) : (type * typelist) :=
  match ft with
  | FT ps t => match ps with
               | PT ts => (VTyp2C t, typelistConv1 (map VTyp2C ts))
               end
  end.


(***************************************************************)

Definition ValTC2Cmap (tenv : valTC) : list (Id * type) :=
  map (fun p => (fst p, VTyp2C (snd p))) tenv.

Definition FunTC2Cmap (ftenv : funTC) : list (Id * (type * typelist)) :=
  map (fun p => (fst p, FTyp2C (snd p))) ftenv.

Definition FunTC2Cmap1 (ftenv : funTC) : list (Id * type) :=
  map (fun p => (fst p, FTyp2C1 (snd p))) ftenv.

(***************************************************************)

(* translation of typing contexts to extended C typing contexts *)

Definition ValTC2ExtC (tenv : valTC) : list (Id * (ident * type)) :=
 swapTList33 (swapTList22 (ValTC2Cmap tenv)).

Definition FunTC2ExtCX (n: nat) (ftenv : funTC) :
  list (Id * (ident * (type * typelist))) :=
  swapTList33 (swapTList22X n (FunTC2Cmap ftenv)).

Definition FunTC2ExtC (ftenv : funTC) :
  list (Id * (ident * (type * typelist))) :=
  swapTList33 (swapTList22 (FunTC2Cmap ftenv)).

Definition FunTC2ExtC1X (n: nat) (ftenv : funTC) :
  list (Id * (ident * type)) :=
  swapTList33 (swapTList22X n (FunTC2Cmap1 ftenv)).

Definition FunTC2ExtC1 (ftenv : funTC) :
  list (Id * (ident * type)) :=
  swapTList33 (swapTList22 (FunTC2Cmap1 ftenv)).

Definition ValTC2ExtCX (n: nat) (tenv : valTC) :
  list (Id * (ident * type)) :=
  swapTList33 (swapTList22X n (ValTC2Cmap tenv)).

Definition ValTC2ExtCE (n: nat) (tenv : valTC) :
  (list (Id * (ident * type)) * nat) := (ValTC2ExtC tenv, n). 


(***********************************************************)

Definition GlobDef := globdef fundef type.

Record NamedDef : Type := mkNamedDef {
                            gId : ident;
                            gDef : GlobDef; 
                            grType : type; (* can get this out of globDef, 
                                            whether variable or function *)
                            gpsType : typelist           
                            }.           

Definition Globvar := globvar type.

(************************************************************)

Module Make8 := Make Wordsize_8.
Module Make32 := Make Wordsize_32.
Module Make64 := Make Wordsize_64.

Definition nat2_i8 (n: nat) := Make8.repr (Z.of_nat n).
Definition nat2_i32 (n: nat) := Make32.repr (Z.of_nat n).
Definition nat2_i64 (n: nat) := Make64.repr (Z.of_nat n).

Lemma i32_2int : Make32.int -> int.
  intro.
  destruct H.
  econstructor.
  eassumption.
Defined.  

(***************************************************************)

Definition Allowed (t: VTyp) : Type :=
   (t = Nat) + (t = Bool) + (t = Unit).

Definition AllowedF (ft : FTyp) : Type * (list Type) :=
  match ft with
  | FT pt t => match pt with
               | PT ts => (Allowed t, (map Allowed ts))  
               end
  end.               


(*****************************************************************)

(* translate value of permissible type as typed value *)
Lemma Val2C : forall (t: VTyp), Allowed t -> forall (v: Value),
  VTyping v t -> (val * type).
  intros.
  destruct H.
  unfold valueVTyp in *.
  destruct v.
  destruct x as [t ct].
  simpl in *.
  destruct v.
  simpl in v.
  set (ct1 := ct).
  set (ct2 := CTyp2C ct1).
  destruct X.
  destruct s.
  inversion e; subst. 
  exact (Vint (i32_2int (nat2_i32 v)), ct2).
  inversion e; subst.
  remember v as v1.
  destruct v.
  exact (Vint (i32_2int (nat2_i32 1)), ct2).
  exact (Vint (i32_2int (nat2_i32 0)), ct2).
  exact (Vundef, Tvoid).
Defined.  


(* translate value of permissible type as typed expression *)
Lemma Val2Cexp : forall (t: VTyp), Allowed t -> forall (v: Value),
  VTyping v t -> (expr * type).
  intros.
  remember (Val2C t X v H) as ww.
  destruct ww as [v0 t0].
  exact (Eval v0 t0, t0).
Defined.  

(************************************************************************)


Lemma liftFenvE (n: nat)
      (tenv: valTC) (x: Id) (t: VTyp) (k: findE tenv x = Some t) :
  sigT (fun i: ident => findE (ValTC2ExtCX n tenv) x = Some (i, VTyp2C t)).

  induction tenv.
  simpl in k.
  inversion k.
  
  simpl in *.
  destruct a as [y t1].
  destruct (IdT.IdEqDec x y).
  inversion k; subst.
  simpl.
  destruct (IdT.IdEqDec y y).  (* i ~= (length (tl tenv)) + 2 + n *) 
  eauto.

  intuition n.
  simpl.
  
  destruct (IdT.IdEqDec x y).
  inversion e; subst.
  intuition n.
  specialize (IHtenv k).
  destruct IHtenv as [z IH].
  econstructor 1 with (x:=z).
  rewrite <- IH.
  f_equal.
Defined.

Lemma liftFenvF (n: nat)
      (ftenv: funTC) (x: Id) (ft: FTyp) (k: findE ftenv x = Some ft) :
  sigT (fun i: ident => findE (FunTC2ExtCX n ftenv) x = Some (i, FTyp2C ft)).

  induction ftenv.
  simpl in k.
  inversion k.
  simpl in *.
  destruct a as [y t1].
  destruct (IdT.IdEqDec x y).
  inversion k; subst.
  simpl.
  destruct (IdT.IdEqDec y y).
  eauto.

  intuition n.
  simpl.
  
  destruct (IdT.IdEqDec x y).
  inversion e; subst.
  intuition n.
  specialize (IHftenv k).
  destruct IHftenv as [z IH].
  econstructor 1 with (x:=z).
  rewrite <- IH.
  f_equal.
Defined.

(* Axiom allowed_ax : forall (t: VTyp), Allowed t. *)

Lemma mkAssignments_aux
        (allowed_ax : forall (t: VTyp), Allowed t)
        (env: valEnv) (tenv: valTC)
        (k: EnvTyping env tenv)
        (ls: list (Id * (ident * type))) :
        (* note: ls and env must have the same length *)
  list (ident * (val * type)).
  unfold EnvTyping in k.
  unfold MatchEnvs in k.
  dependent induction env.
  exact nil.
  destruct ls.
  exact nil.
  destruct a.
  destruct p.
  destruct p.
  inversion k; subst.
  specialize (IHenv (map (thicken StaticSemL.Id valueVTyp) env) eq_refl ls).
  assert (Allowed (projT1 v)) as a1.
  eapply allowed_ax.
  set (p := (i1, Val2C (projT1 v) a1 v eq_refl)). (* the type is actually
              obtained from translating v, it is not coming from ls, 
              though the two should agree *)
  exact (p :: IHenv).
Defined.  
  

Lemma mkAssignments (ls : list (ident * (val * type)))
      (e: expr) (t: type) : expr.
  induction ls.
  exact e.
  destruct a.
  destruct p.
  set (e1 := Eassign (Evar i t) (Eval v t) t).
  exact (Ecomma e1 e t).
Defined.  


Inductive ExtCAgree : 
 forall (tenv: valTC) (ctenv: list (Id * (ident * type))), Type :=
| ExtCAgree_nil : ExtCAgree nil nil 
| ExtCAgree_cons :
    forall  (tenv: valTC) (ctenv: list (Id * (ident * type)))
            (x: Id) (t: VTyp) (i: ident), 
      ExtCAgree tenv ctenv ->      
      ExtCAgree ((x, t) :: tenv) ((x, (i, VTyp2C t)) :: ctenv). 


Lemma liftFenvE1 (n: nat) (tenv: valTC) :
  ExtCAgree tenv (ValTC2ExtCX n tenv).

  induction tenv.
  econstructor.
  destruct a as [x t].
  unfold ValTC2ExtCX.
  simpl.
  econstructor.
  assumption.
Defined.  
  
Lemma ExtCAgree_app_lemma (tenv1 tenv2: valTC)
      (ctenv1 ctenv2: list (Id * (ident * type))) :
  ExtCAgree tenv1 ctenv1 -> ExtCAgree tenv2 ctenv2 ->
  ExtCAgree (tenv1 ++ tenv2) (ctenv1 ++ ctenv2).
  revert tenv2 ctenv1 ctenv2.
  induction tenv1.
  intros.
  inversion X; subst.
  simpl.
  assumption.
  intros.
  inversion X; subst.
  simpl in *.
  econstructor.
  eapply IHtenv1.
  assumption.
  assumption.
Defined.  


Lemma allowed_ts
      (allowed_ax : forall (t: VTyp), Allowed t)
      (ts: list VTyp) : (tlist2type (map Allowed ts)).
     induction ts.
     simpl.
     exact tt.
     simpl.
     split.
     apply allowed_ax.
     exact IHts.
Defined.     
      
Fixpoint list2exprlist (ls: list expr) : exprlist :=
  match ls with
  | nil => Enil
  | x::xs => Econs x (list2exprlist xs)
  end.                 

(****************************************************************)

Definition Exp2C_def := fun (ftenv: funTC) (tenv: valTC) (e: Exp)
                            (t: VTyp)
                            (k: ExpTyping ftenv tenv e t)  => Allowed t ->
   forall (ctenv: list (Id * (ident * type))),
     ExtCAgree tenv ctenv ->
   forall (ctenvL: list (ident * type)),   
  (expr * type) * list (ident * type).

Definition Prms2C_def := fun (ftenv: funTC) (tenv: valTC) 
                            (ps: Prms) (pt: PTyp)
                            (k: PrmsTyping ftenv tenv ps pt) =>
                           match pt with
                           | PT ts => tlist2type (map Allowed ts) ->
  forall (ctenv: list (Id * (ident * type))),
    ExtCAgree tenv ctenv ->
   forall (ctenvL: list (ident * type)),     
  list (expr * type) * list (ident * type) end.

Definition CTrans_ExpTyping_mut := ExpTyping_mut Exp2C_def Prms2C_def.

Definition CTrans_PrmsTyping_mut := PrmsTyping_mut Exp2C_def Prms2C_def.

Lemma Exp2CC
      (allowed_ax : forall (t: VTyp), Allowed t)
      (xfunenv: list (Id * (ident * type * typelist)))
      (ftenv: funTC) (tenv: valTC) (e: Exp)
                            (t: VTyp)
                            (k: ExpTyping ftenv tenv e t) :
  forall (m: Allowed t) (ctenv: list (Id * (ident * type))),
    ExtCAgree tenv ctenv ->
   forall (ctenvL: list (ident * type)),       
     (expr * type) * list (ident * type).

  set (hhs := (map (fun p => fst (fst (snd p))) xfunenv)).
  set (pf := Pmaximum hhs).
  set (nf := S (Pos.to_nat pf)). 
  
  remember (FunTC2ExtCX nf ftenv) as cftenv. 
  eapply CTrans_ExpTyping_mut.
(* Val *)
  unfold Exp2C_def.
  intros.
  unfold VTyping in v0.
  unfold valueVTyp in v0.
  inversion v0; subst.
  clear H.
  split.
  exact (Val2Cexp (projT1 v) X v eq_refl).
  exact ctenvL.  

(* Var *)  
  unfold Exp2C_def.
  intros.
  unfold IdTyping in i.
  unfold EnvrAssign in i.

  eapply (liftFenvE nf) in i.  
  destruct i as [i H0].
  set (ct := VTyp2C t0).
  exact (Evar i ct, ct, ctenvL).

(* BindN *)
  unfold Exp2C_def.
  intros.
  assert (Allowed t1) as X3.
  eapply allowed_ax.
  specialize (X X3 ctenv X2 ctenvL).
  destruct X as [w1 ctenvL1].
  specialize (X0 X1 ctenv X2 ctenvL1).
  destruct X0 as [w2 ctenvL2].
  destruct w1 as [cv1 ct1].
  destruct w2 as [cv2 ct2].
  exact (Ecomma cv1 cv2 ct2, ct2, ctenvL2).
  
(* BindS *)  
  unfold Exp2C_def.
  intros.
  assert (Allowed t1) as X3.
  eapply allowed_ax.
  specialize (X X3 ctenv X2 ctenvL).
  destruct X as [w1 ctenvL1].
  destruct w1 as [cv1 ct1].
  set (xs := (map (fun p => fst (snd p)) ctenv) ++
             (map fst ctenvL1)). 
  set (n := Pmaximum (pf::xs)).    
  set (ix := Psucc n).          
  set (ct1' := VTyp2C t1).
  set (ctenv' := (x, (ix, ct1')) :: ctenv). 
  assert (ExtCAgree tenv' ctenv') as X4.
  subst tenv'.
  subst ctenv'.
  subst ct1'.
  econstructor.
  assumption.
  
  specialize (X0 X1 ctenv' X4 ctenvL1). 
  destruct X0 as [w2 ctenvL2].      
  destruct w2 as [cv2 ct2].
  set (ctenvL3 := (ix, ct1') :: ctenvL2).   
  exact (Ecomma (Eassign (Evar ix ct1) cv1 ct1') cv2 ct2, ct2, ctenvL3).

(* BindMS *)
  unfold Exp2C_def.
  intros.
  set (xs := (map (fun p => fst (snd p)) ctenv) ++
             (map fst ctenvL)). 
  set (n := Pmaximum (pf::xs)).  

  set (nn := S (Pos.to_nat n)). 
  set (ctenv1 := ValTC2ExtCX nn tenv1).
  set (ctenv2 := ctenv1 ++ ctenv).
  
  set (ct3' := VTyp2C t0).

  assert (ExtCAgree tenv1 ctenv1) as X3.
  eapply liftFenvE1.
  assert (ExtCAgree tenv2 ctenv2) as X3a.
  subst tenv2.
  subst ctenv2.
  eapply ExtCAgree_app_lemma.  
  assumption.
  assumption.
  
  specialize (X X0 ctenv2 X3a ctenvL).
  destruct X as [X ctenvL1].
  destruct X as [ce3 ct3].

  set (ls := mkAssignments_aux allowed_ax
                               env0 tenv1 e1 ctenv1). 
  set (ce := mkAssignments ls ce3 ct3').

  set (ctenvL3 := (map snd ctenv1) ++ ctenvL1).
  
  exact (ce, ct3', ctenvL3).

(* IfThenElse *)  
  unfold Exp2C_def.
  intros.
  assert (Allowed Bool) as X4.
  {- unfold Allowed.
     left.
     right.
     reflexivity. }
  specialize (X X4 ctenv X3 ctenvL).
  destruct X as [w1 ctenvL1].
  specialize (X0 X2 ctenv X3 ctenvL1).
  destruct X0 as [w2 ctenvL2].
  specialize (X1 X2 ctenv X3 ctenvL2).
  destruct X1 as [w3 ctenvL3].
  destruct w1 as [cv1 ct1].
  destruct w2 as [cv2 ct2].
  destruct w3 as [cv3 ct3].
  exact (Econdition cv1 cv2 cv3 ct3, ct3, ctenvL3).
  
(* Apply *)
  unfold Exp2C_def, Prms2C_def.
  intros.
  destruct pt as [ts].
  assert (tlist2type (map Allowed ts)) as X3.
  eapply (allowed_ts allowed_ax).
  specialize (X X3 ctenv X2 ctenvL).
  destruct X as [cps ctenvL1].
  eapply (liftFenvF nf) in i.  
  destruct i as [ix k2].
  simpl in *.

  set (rt := VTyp2C t0).

  split.
  set (lss := list2exprlist (map fst cps)).

  set (cft := Tfunction (typelistConv1 (map VTyp2C ts)) (VTyp2C t0) cc_default).
  
  exact (Ecall (Evar ix cft) lss rt, rt).

  exact ctenvL1.

(* Call *)
  unfold Exp2C_def, Prms2C_def.
  intros.
  destruct pt as [ts].
  assert (tlist2type (map Allowed ts)) as X3.
  eapply (allowed_ts allowed_ax).
  specialize (X X3 ctenv X1 ctenvL).
  destruct X as [cps ctenvL1].
  eapply (liftFenvF nf) in i.  
  destruct i as [ix k2].
  simpl in *.

  set (rt := VTyp2C t0).

  split.
  set (lss := list2exprlist (map fst cps)).

  set (cft := Tfunction (typelistConv1 (map VTyp2C ts)) (VTyp2C t0) cc_default).
  
  exact (Ecall (Evar ix cft) lss rt, rt).

  exact ctenvL1.

(* other goals *)
  
  Focus 4.
  exact k.

  Focus 2.
  unfold Prms2C_def.
  intros.
  exact (nil, ctenvL).

  Focus 2.
  unfold Exp2C_def, Prms2C_def.
  intros.
  
  assert (Allowed t0) as X3.
  apply allowed_ax.

  specialize (X X3 ctenv X2 ctenvL).
  destruct X as [p1 ctenvL1].
  
  assert (tlist2type (map Allowed ts)) as X4.
  {- simpl in X1.
     destruct X1.
     assumption. }
  
  specialize (X0 X4 ctenv X2 ctenvL1).
  destruct X0 as [ps ctenvL2].

  exact (p1::ps, ctenvL2).

(* Modify *)
  unfold Exp2C_def.
  intros.

  assert (Allowed t1) as X3.
  apply allowed_ax.

  specialize (X X3 ctenv X1 ctenvL).
  destruct X as [p1 ctenvL1].
  destruct p1 as [cv1 ct1].
  set (cls1 := Econs cv1 Enil).
  
  destruct XF.
  set (xf := findE xfunenv x_name0).
  destruct xf.

  Focus 2.
  split.
  exact (Eval Vundef Tvoid, Tvoid).
  exact ctenvL1.

  destruct p as [p ts0].
  destruct p as [i0 t0].
  split.
  split.
  set (ctf := Tfunction ts0 t0 cc_default).
  exact (Ecall (Evar i0 ctf) cls1 t0).
  exact t0.
  exact ctenvL1.
Defined.


Lemma Prms2CC
      (allowed_ax : forall (t: VTyp), Allowed t)
      (xfunenv: list (Id * (ident * type * typelist)))
      (ftenv: funTC) (tenv: valTC) (ps: Prms) (pt: PTyp)
                            (k: PrmsTyping ftenv tenv ps pt) : 
                           match pt with
                           | PT ts => tlist2type (map Allowed ts) ->
  forall (ctenv: list (Id * (ident * type))),
    ExtCAgree tenv ctenv ->
   forall (ctenvL: list (ident * type)),     
  list (expr * type) * list (ident * type) end.

  set (hhs := (map (fun p => fst (fst (snd p))) xfunenv)).
  set (pf := Pmaximum hhs).
  set (nf := S (Pos.to_nat pf)). 

  remember (FunTC2ExtCX nf ftenv) as cftenv.   
  eapply CTrans_PrmsTyping_mut.
(* Val *)
  unfold Exp2C_def.
  intros.
  unfold VTyping in v0.
  unfold valueVTyp in v0.
  inversion v0; subst.
  clear H.
  split.
  exact (Val2Cexp (projT1 v) X v eq_refl).
  exact ctenvL.  

(* Var *)  
  unfold Exp2C_def.
  intros.
  unfold IdTyping in i.
  unfold EnvrAssign in i.

  eapply (liftFenvE nf) in i.   
  destruct i as [i H0].
  set (ct := VTyp2C t).
  exact (Evar i ct, ct, ctenvL).

(* BindN *)
  unfold Exp2C_def.
  intros.
  assert (Allowed t1) as X3.
  eapply allowed_ax.
  specialize (X X3 ctenv X2 ctenvL).
  destruct X as [w1 ctenvL1].
  specialize (X0 X1 ctenv X2 ctenvL1).
  destruct X0 as [w2 ctenvL2].
  destruct w1 as [cv1 ct1].
  destruct w2 as [cv2 ct2].
  exact (Ecomma cv1 cv2 ct2, ct2, ctenvL2).
  
(* BindS *)  
  unfold Exp2C_def.
  intros.
  assert (Allowed t1) as X3.
  eapply allowed_ax.
  specialize (X X3 ctenv X2 ctenvL).
  destruct X as [w1 ctenvL1].
  destruct w1 as [cv1 ct1].
  set (xs := (map (fun p => fst (snd p)) ctenv) ++
             (map fst ctenvL1)). 
  set (n := Pmaximum (pf::xs)).  
  set (ix := Psucc n).
  set (ct1' := VTyp2C t1).
  set (ctenv' := (x, (ix, ct1')) :: ctenv).
  assert (ExtCAgree tenv' ctenv') as X4.
  subst tenv'.
  subst ctenv'.
  subst ct1'.
  econstructor.
  assumption.
  
  specialize (X0 X1 ctenv' X4 ctenvL1).
  destruct X0 as [w2 ctenvL2].
  destruct w2 as [cv2 ct2].
  set (ctenvL3 := (ix, ct1') :: ctenvL2).
  exact (Ecomma (Eassign (Evar ix ct1) cv1 ct1') cv2 ct2, ct2, ctenvL3).

(* BindMS *)
  unfold Exp2C_def.
  intros.
  set (xs := (map (fun p => fst (snd p)) ctenv) ++
             (map fst ctenvL)). 
  set (n := Pmaximum (pf::xs)). 

  set (nn := S (Pos.to_nat n)). 
  set (ctenv1 := ValTC2ExtCX nn tenv1).
  set (ctenv2 := ctenv1 ++ ctenv).
  
  set (ct3' := VTyp2C t).

  assert (ExtCAgree tenv1 ctenv1) as X3.
  eapply liftFenvE1.
  assert (ExtCAgree tenv2 ctenv2) as X3a.
  subst tenv2.
  subst ctenv2.
  eapply ExtCAgree_app_lemma.  
  assumption.
  assumption.
  
  specialize (X X0 ctenv2 X3a ctenvL).
  destruct X as [X ctenvL1].
  destruct X as [ce3 ct3].

  set (ls := mkAssignments_aux allowed_ax
                               env0 tenv1 e0 ctenv1). 
  set (ce := mkAssignments ls ce3 ct3').

  set (ctenvL3 := (map snd ctenv1) ++ ctenvL1).
  
  exact (ce, ct3', ctenvL3).

(* IfThenElse *)  
  unfold Exp2C_def.
  intros.
  assert (Allowed Bool) as X4.
  {- unfold Allowed.
     left.
     right.
     reflexivity. }
  specialize (X X4 ctenv X3 ctenvL).
  destruct X as [w1 ctenvL1].
  specialize (X0 X2 ctenv X3 ctenvL1).
  destruct X0 as [w2 ctenvL2].
  specialize (X1 X2 ctenv X3 ctenvL2).
  destruct X1 as [w3 ctenvL3].
  destruct w1 as [cv1 ct1].
  destruct w2 as [cv2 ct2].
  destruct w3 as [cv3 ct3].
  exact (Econdition cv1 cv2 cv3 ct3, ct3, ctenvL3).
  
(* Apply *)
  unfold Exp2C_def, Prms2C_def.
  intros.
  destruct pt0 as [ts].
  assert (tlist2type (map Allowed ts)) as X3.
  eapply (allowed_ts allowed_ax).
  specialize (X X3 ctenv X2 ctenvL).
  destruct X as [cps ctenvL1].
  eapply (liftFenvF nf) in i.  
  destruct i as [ix k2].
  simpl in *.

  set (rt := VTyp2C t).

  split.
  set (lss := list2exprlist (map fst cps)).

  set (cft := Tfunction (typelistConv1 (map VTyp2C ts)) (VTyp2C t) cc_default).
  
  exact (Ecall (Evar ix cft) lss rt, rt).

  exact ctenvL1.

(* Call *)
  unfold Exp2C_def, Prms2C_def.
  intros.
  destruct pt0 as [ts].
  assert (tlist2type (map Allowed ts)) as X3.
  eapply (allowed_ts allowed_ax).
  specialize (X X3 ctenv X1 ctenvL).
  destruct X as [cps ctenvL1].
  eapply (liftFenvF nf) in i.     
  destruct i as [ix k2].
  simpl in *.

  set (rt := VTyp2C t).

  split.
  set (lss := list2exprlist (map fst cps)).

  set (cft := Tfunction (typelistConv1 (map VTyp2C ts)) (VTyp2C t) cc_default).
  
  exact (Ecall (Evar ix cft) lss rt, rt).

  exact ctenvL1.

(* Modify *)
  unfold Exp2C_def.
  intros.

  assert (Allowed t1) as X3.
  apply allowed_ax.

  specialize (X X3 ctenv X1 ctenvL).
  destruct X as [p1 ctenvL1].
  destruct p1 as [cv1 ct1].
  set (cls1 := Econs cv1 Enil).
  
  destruct XF.
  set (xf := findE xfunenv x_name0).
  destruct xf.

  Focus 2.
  split.
  exact (Eval Vundef Tvoid, Tvoid).
  exact ctenvL1.

  destruct p as [p ts0].
  destruct p as [i0 t0].
  split.
  split.
  set (ctf := Tfunction ts0 t0 cc_default).
  exact (Ecall (Evar i0 ctf) cls1 t0).
  exact t0.
  exact ctenvL1.

(* nil *)
  unfold Prms2C_def.
  intros.
  exact (nil, ctenvL).

(* cons *)
  unfold Exp2C_def, Prms2C_def.
  intros.
  
  assert (Allowed t) as X3.
  apply allowed_ax.

  specialize (X X3 ctenv X2 ctenvL).
  destruct X as [p1 ctenvL1].
  
  assert (tlist2type (map Allowed ts)) as X4.
  {- simpl in X1.
     destruct X1.
     assumption. }
  
  specialize (X0 X4 ctenv X2 ctenvL1).
  destruct X0 as [ps0 ctenvL2].

  exact (p1::ps0, ctenvL2).

  Unshelve.
  Focus 3.
  exact k.
Defined.


Lemma Fun2CC
      (allowed_ax : forall (t: VTyp), Allowed t)
      (xfunenv: list (Id * (ident * type * typelist)))
      (ftenv: funTC) (f: Fun) (k1: FunWT ftenv f) : function.

  set (hhs := (map (fun p => fst (fst (snd p))) xfunenv)).
  set (pf := Pmaximum hhs).
  set (nf := S (Pos.to_nat pf)). 

  remember (FunTC2ExtCX nf ftenv) as cftenv.  
  remember (FunTC2ExtC1X nf ftenv) as cftenv1.
  destruct f as [tenv v e].
  destruct v as [t v].
  unfold FunWT in k1.
  simpl in k1.
  
  remember (VTyp2C t) as ct.

  set (n := (nf + length ftenv)%nat).   
  set (ctenv := ValTC2ExtCX n tenv).

  set (ags := liftFenvE1 n tenv). 

  assert (Allowed t) as tt.
  eapply allowed_ax.

  set (st := Exp2CC allowed_ax xfunenv ftenv tenv e t k1 tt ctenv ags nil).
  
  destruct st as [fs ctenvL].
  
  econstructor.
  exact ct.
  exact cc_default.

  set (ps := map snd ctenv).
  exact (ps ++ ctenvL).
  exact (map snd cftenv1).

  destruct fs as [fs t0].
  exact (Sreturn (Some fs)).
Defined.


Lemma Fun2CC_1
      (allowed_ax : forall (t: VTyp), Allowed t)
      (xfunenv: list (Id * (ident * type * typelist)))
      (fenv: funEnv) (x: Id) (f: Fun) 
      (k1: FunWT (funEnv2funTC fenv) f) (m: findE fenv x = Some f) :
  (Id * (ident * function)).

  set (hhs := (map (fun p => fst (fst (snd p))) xfunenv)).
  set (pf := Pmaximum hhs).
  set (nf := S (Pos.to_nat pf)). 
  
  set (ftenv := funEnv2funTC fenv).
  set (cftenv := FunTC2ExtCX nf ftenv).    
  set (ft := funFTyp f).
  assert (findE ftenv x = Some ft) as m1.
  {- eapply (ExtRelVal1 funFTyp ftenv fenv x f eq_refl) in m.
     destruct m.
     destruct f.
     simpl in *.
     inversion e0; subst.
     subst ft.
     assumption. }
  eapply (liftFenvF nf) in m1.    
  destruct m1 as [i m0].
  split.
  exact x.
  split.
  exact i. 
  set (ee := Fun2CC allowed_ax xfunenv ftenv f k1).
  exact ee.
Defined.  


Lemma Fun2CC_all_aux
      (allowed_ax : forall (t: VTyp), Allowed t)
      (xfunenv: list (Id * (ident * type * typelist)))
      (fenv: funEnv)  
      (k1: FEnvWT fenv) (k2: noDup fenv) :
 forall (fenv1: funEnv),
    (forall a, List.In a fenv1 -> List.In a fenv) ->         
  list (Id * (ident * function)).
  unfold FEnvWT in k1. 
  intros.
  induction fenv1.
  exact nil.
  destruct a as [x f].
  assert (forall a : Id * Fun, List.In a fenv1 -> List.In a fenv) as H0.
  {- intros.
     specialize (H a).
     simpl in H.
     assert ((x, f) = a \/ List.In a fenv1).
     right; exact H0.
     eapply H in H1.
     exact H1.
  }
  specialize (IHfenv1 H0).
  specialize (H (x,f)).
  assert (List.In (x, f) ((x, f) :: fenv1)) as H2.
  {- econstructor.
     reflexivity. }
  specialize (H H2).
  eapply in_find_lemma in H.
  Focus 2.
  assumption.

  set (ftenv := funEnv2funTC fenv). 
  specialize (k1 ftenv eq_refl).
  specialize (k1 x f H).
  
  set (ee := Fun2CC_1 allowed_ax xfunenv fenv x f k1 H).
  exact (ee :: IHfenv1).
Defined.


Lemma Fun2CC_all
      (allowed_ax : forall (t: VTyp), Allowed t)
      (xfunenv: list (Id * (ident * type * typelist)))
      (fenv: funEnv)  
      (k1: FEnvWT fenv) (k2: noDup fenv) :
  list (Id * (ident * function)).
  assert (forall a, List.In a fenv -> List.In a fenv) as H.
  intros.
  auto.
  eapply (Fun2CC_all_aux allowed_ax xfunenv fenv k1 k2 fenv H).
Defined.

Lemma function2globdef (p: ident * function) : 
   (ident * globdef (Ctypes.fundef function) type).
  destruct p.
  split.
  exact i.
  econstructor.
  econstructor.
  exact f.
Defined.  

Lemma Fun2CC_all2
      (allowed_ax : forall (t: VTyp), Allowed t)
      (xfunenv: list (Id * (ident * type * typelist)))
      (fenv: funEnv)  
      (k1: FEnvWT fenv) (k2: noDup fenv) :
  list (ident * globdef (Ctypes.fundef function) type).
  set (ls := Fun2CC_all allowed_ax xfunenv fenv k1 k2).
  set (ls1 := map snd ls).
  exact (map function2globdef ls1).
Defined.  
  

(* the names (ident) of the actions are those chosen by the programmer *)
(* 1 should be used for the main *)
Lemma extND_type (p: Id * NamedDef) : (Id * (ident * type * typelist)).
  destruct p.
  destruct n.
  exact (i, (gId0, grType0, gpsType0)).  
Defined.

Lemma extND_globdef (p: NamedDef) :
  (ident * globdef (Ctypes.fundef function) type).
  destruct p.
  unfold GlobDef in gDef0.
  exact (gId0, gDef0).
Defined.  

Lemma TopLevel0 
      (allowed_ax : forall (t: VTyp), Allowed t)
      (xenv: list (Id * NamedDef))
      (fenv: funEnv)  
      (k1: FEnvWT fenv) (k2: noDup fenv) :
  program.
set (xfunenv := map extND_type xenv).            
set (xdefs := map extND_globdef (map snd xenv)).            
set (xdefs2 := Fun2CC_all2 allowed_ax xfunenv fenv k1 k2).

econstructor.
exact (xdefs ++ xdefs2).
exact (map fst xdefs ++ map fst xdefs2).
exact (1%positive).
Unshelve.
Focus 2.
exact nil.
Focus 2.
exact Maps.PTree.Leaf.
auto.
Defined.


Lemma MkMain_aux
      (allowed_ax : forall (t: VTyp), Allowed t)
      (xfunenv: list (Id * (ident * type * typelist)))
      (ftenv: funTC)
      (tenv: valTC)
      (v: Value)
      (e: Exp)
      (k3: FunWT ftenv (FC tenv v e)) : function.
  eapply (Fun2CC allowed_ax xfunenv ftenv (FC tenv v e) k3).
Defined.  

Lemma MkMain1
      (allowed_ax : forall (t: VTyp), Allowed t)
      (xfunenv: list (Id * (ident * type * typelist)))
      (ftenv: funTC)
      (tenv: valTC)
      (v: Value)
      (e: Exp)
      (k3: FunWT ftenv (FC tenv v e)) : NamedDef.
  econstructor.
  exact (1%positive).
  econstructor.
  econstructor.
  eapply (MkMain_aux allowed_ax xfunenv ftenv tenv v e k3).
  exact (VTyp2C (projT1 v)).
  exact (typelistConv1 (map (fun x => VTyp2C (snd x)) tenv)).
Defined.


Lemma MkMain
      (allowed_ax : forall (t: VTyp), Allowed t)
      (xfunenv: list (Id * (ident * type * typelist)))
      (ftenv: funTC)
      (tenv: valTC)
      (v: Value)
      (e: Exp)
      (k3: FunWT ftenv (FC tenv v e)) :
  (ident * globdef (Ctypes.fundef function) type).
  econstructor.
  exact (1%positive).
  econstructor.
  econstructor.
  eapply (MkMain_aux allowed_ax xfunenv ftenv tenv v e k3).
Defined.


Lemma TopLevel 
      (allowed_ax : forall (t: VTyp), Allowed t)
      (xenv: list (Id * NamedDef))
      (fenv: funEnv)
      (k1: FEnvWT fenv) (k2: noDup fenv)
      (tenv: valTC)
      (v: Value)
      (e: Exp)
      (k3: FunWT (funEnv2funTC fenv) (FC tenv v e)) :
  program.
set (xfunenv := map extND_type xenv).            
set (mdef := MkMain allowed_ax xfunenv (funEnv2funTC fenv) tenv v e k3).
set (xdefs := mdef :: (map extND_globdef (map snd xenv))).            
set (xdefs2 := Fun2CC_all2 allowed_ax xfunenv fenv k1 k2).
    
econstructor.
exact (xdefs ++ xdefs2).
exact (map fst xdefs ++ map fst xdefs2).
exact (1%positive).
Unshelve.
Focus 2.
exact nil.
Focus 2.
exact Maps.PTree.Leaf.
auto.
Defined.


End CTrans.

  
