(* DEC1 language development.
   Paolo Torrini, 
   Universite' Lille-1 - CRIStAL-CNRS
*)
(* library of auxiliary functions to support translation and
manipulation of well-typed terms *)

Require Export EnvLibA.
Require Export RelLibA.

Require Export Basics.
Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Import IdModTypeA. 
Require Import StaticSemA.
Require Import THoareA.

Require Coq.Vectors.VectorDef. 

(*
Require Import Csyntax.
Require Import compcert.cfrontend.Csyntax.
*)

Import ListNotations.

Module DECaux (IdT: IdModType) <: IdModType.
Export IdT.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.


Module THoareI := THoare IdT.
Export THoareI.


(***********************************************************)

Definition Char := Nat.

Definition stringT : nat -> Type := fun n => VectorDef.t nat n. 
Instance StringVT : forall n: nat, ValTyp (stringT n).

Definition String : nat -> VTyp := fun n => vtyp (stringT n).


(*****************************************************************)

Definition genEnv (V T: Type) := list (V * T).


Definition extrPrmsTJofQV (TI: Type) (VTI: ValTyp TI) (q: TI) :
  sigT (fun t => PrmsTyping nil nil nil (PS [Val (cst TI q)]) t).
  constructor 1 with (x:=(PT [vtyp TI])).
  constructor.
  constructor.
  constructor.
  constructor.
  simpl.
  auto.
  constructor.
  constructor.
Defined.  
  
Definition extrExpTJofBindN1
           (ftenv: funTC) (tenv: valTC) (fenv: funEnv) (e1 e2: Exp)
           (k: sigT (fun t => ExpTyping ftenv tenv fenv (BindN e1 e2) t)) :
  sigT (fun t => ExpTyping ftenv tenv fenv e1 t).
  destruct k as [t k].
  inversion k; subst.
  constructor 1 with (x:=t1).
  auto.
Defined.  

Definition extrExpTJofBindN2
           (ftenv: funTC) (tenv: valTC) (fenv: funEnv) (e1 e2: Exp)
           (k: sigT (fun t => ExpTyping ftenv tenv fenv (BindN e1 e2) t)) :
  sigT (fun t => ExpTyping ftenv tenv fenv e2 t).
  destruct k as [t k].
  constructor 1 with (x:=t).
  inversion k; subst.
  auto.
Defined.  

Definition extrExpTJofBindS1
           (ftenv: funTC) (tenv: valTC) (fenv: funEnv) (x: Id) (e1 e2: Exp)
           (k: sigT (fun t => ExpTyping ftenv tenv fenv (BindS x e1 e2) t)) :
  sigT (fun t => ExpTyping ftenv tenv fenv e1 t).
  destruct k as [t k].
  inversion k; subst.
  subst tenv'.
  constructor 1 with (x:=t1).
  auto.
Defined.  

Definition extrExpTJofBindS2
           (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
           (k0: FEnvTyping fenv ftenv)
           (x: Id) (e1 e2: Exp)
           (k: sigT (fun t => ExpTyping ftenv tenv fenv (BindS x e1 e2) t))
           (t1: VTyp)
           (k1: ExpTyping ftenv tenv fenv e1 t1):
  sigT (fun t => ExpTyping ftenv ((x, t1)::tenv) fenv e2 t).
  destruct k as [t k].
  constructor 1 with (x:=t).
  inversion k; subst.
  subst tenv'.
  assert (t0 = t1).
  eapply UniqueExpType.
  eauto.
  eauto.
  auto.
  rewrite H in X0.
  auto.
Defined.  

(*
Definition extrExpTJofBindS2
           (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
           (k0: FEnvTyping fenv ftenv)
           (x: Id) (e1 e2: Exp)
           (k: sigT (fun t => ExpTyping ftenv tenv fenv (BindS x e1 e2) t))
            :
  sigT (fun t => ExpTyping ftenv
            ((x, projT1 (extrExpTJofBindS1 ftenv tenv fenv x e1 e2 k))::tenv)
                           fenv e2 t).
  destruct k as [t k].
  constructor 1 with (x:=t).
  inversion k; subst.
  subst tenv'. 
  auto.
Defined.  
*)  

Definition extrPrmsTJofApply
           (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
           (q: QFun) (ps: Prms)
           (k: sigT (fun t => ExpTyping ftenv tenv fenv (Apply q ps) t)) :
     sigT (fun pt => PrmsTyping ftenv tenv fenv ps pt).
Proof.
  destruct k as [t k].
  inversion k; subst.
  constructor 1 with (x:= PT (map snd fps)).
  auto.
Defined.
  
Definition extrQFunTJofApply
           (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
           (q: QFun) (ps: Prms)
           (k: sigT (fun t => ExpTyping ftenv tenv fenv (Apply q ps) t)) :
     sigT (fun ft => QFunTyping ftenv fenv q ft).
Proof.
  destruct k as [t k].
  inversion k; subst.
  constructor 1 with (x:= FT fps t).
  auto.
Defined.
             
Definition extrFunTJofQFun
           (ftenv: funTC) (fenv: funEnv)
           (f: Fun) 
           (k: sigT (fun ft => QFunTyping ftenv fenv (QF f) ft)) :
     sigT (fun ft => FunTyping f ft).
Proof.
  destruct k as [t k].
  inversion k; subst.
  constructor 1 with (x:= t).
  auto.
Defined.

Definition extrFunTJofApply
           (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
           (f: Fun) (ps: Prms)
           (k: sigT (fun t =>
                       ExpTyping ftenv tenv fenv (Apply (QF f) ps) t)) :
     sigT (fun ft => FunTyping f ft).
Proof.
  destruct k as [t k].
  inversion k; subst.
  inversion X0; subst.
  constructor 1 with (x:= (FT fps t)).
  auto.
Defined.
  
Definition extrExpTJofIF1
           (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
           (e1 e2 e3: Exp)
           (k: sigT (fun t =>
                  ExpTyping ftenv tenv fenv (IfThenElse e1 e2 e3) t)) :
     sigT (fun t => ExpTyping ftenv tenv fenv e1 t).
Proof.
  destruct k as [t k].
  inversion k; subst.
  constructor 1 with (x:= Bool).
  auto.
Defined.           

Definition extrExpTJofIF2
           (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
           (e1 e2 e3: Exp)
           (k: sigT (fun t =>
                  ExpTyping ftenv tenv fenv (IfThenElse e1 e2 e3) t)) :
     sigT (fun t => ExpTyping ftenv tenv fenv e2 t).
Proof.
  destruct k as [t k].
  inversion k; subst.
  constructor 1 with (x:= t).
  auto.
Defined.

Definition extrExpTJofIF3
           (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
           (e1 e2 e3: Exp)
           (k: sigT (fun t =>
                  ExpTyping ftenv tenv fenv (IfThenElse e1 e2 e3) t)) :
     sigT (fun t => ExpTyping ftenv tenv fenv e3 t).
Proof.
  destruct k as [t k].
  inversion k; subst.
  constructor 1 with (x:= t).
  auto.
Defined.

Definition extrQValTJofRet (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
           (z: Tag) (q: QValue)
           (k: sigT (fun t =>
                  ExpTyping ftenv tenv fenv (Return z q) t)) :
  sigT (fun t => QValueTyping tenv q t).
Proof.
  destruct k as [t k].
  inversion k; subst.
  constructor 1 with (x:= t).
  auto.
Defined.
  


Lemma FEnvNull : FEnvTyping nil nil.
  constructor.
Defined.  

Definition getFunName (f: Fun) : Id :=
  match f with FC _ _ _ _ x _ => x end.


Obligation Tactic := idtac. 

Program Fixpoint mapF2 {A B C: Type} (R: A -> B -> Type)
               (f: forall e: A, (sigT (fun x => R e x)) -> C)
               (ls: list A)    
               (k: sigT (fun ts => Forall2T R ls ts)): 
               list C := _.
Next Obligation.
  intros.
  destruct k as [ts k].
  induction k.
  exact nil.
  specialize (f x).
  assert ({x0 : B & R x x0}).
  econstructor.
  eauto.
  specialize (f X).
  exact (f::IHk).
Defined.  


Program Fixpoint mapF4A {A B C D M: Type} (R: A -> B -> Type)
               (env: D) (menv: M) 
               (f: forall e: A, M -> (sigT (fun x => R e x)) ->
                                                    option (M * C))
               (ls: list A)    
               (k: sigT (fun ts => Forall2T R ls ts)): 
  option (M * list C) := _.
Next Obligation.
  intros.
  destruct k as [ts k].
  induction k.
  - exact (Some (menv, nil)).
  - specialize (f x).
    destruct IHk.
    + destruct p.
      specialize (f m).
      assert ({x0 : B & R x x0}).
      {- econstructor.
         eauto.
      }   
      {- specialize (f X).
         destruct f.
         {+ destruct p.
            exact (Some (m0, c::l0)).
         }
         {+ exact None.
         }   
      }  
    + exact None. 
Defined.  

Program Fixpoint mapF4 {A B C D M: Type} (R: A -> B -> Type)
               (env: D) (menv: M) 
               (f: forall e: A, M -> (sigT (fun x => R e x)) ->
                                                    option (C * M))
               (ls: list A)    
               (k: sigT (fun ts => Forall2T R ls ts)): 
  option (list C * M) := _.
Next Obligation.
  intros.
  destruct k as [ts k].
  induction k.
  - exact (Some (nil, menv)).
  - specialize (f x).
    destruct IHk.
    + destruct p.
      specialize (f m).
      assert ({x0 : B & R x x0}).
      {- econstructor.
         eauto.
      }   
      {- specialize (f X).
         destruct f.
         {+ destruct p.
            exact (Some (c::l0, m0)).
         }
         {+ exact None.
         }   
      }  
    + exact None. 
Defined.  


Definition extrExpTJofPS (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
           (es: list Exp)
           (k: sigT (fun pt => PrmsTyping ftenv tenv fenv (PS es) pt)) :
           sigT (fun ts => Forall2T (ExpTyping ftenv tenv fenv) es ts).
  intros.
  destruct k.
  destruct x.
  constructor 1 with (x:=ts).
  inversion p; subst.
  auto.
Defined.  

Definition extrFEnvTJofFun (fenv: funEnv) (tenv: valTC)
                             (e0 e1: Exp) (y: Id) (n: nat)
           (k: sigT (fun ft => FunTyping (FC fenv tenv e0 e1 y n) ft)) :
  sigT (fun ftenv => FEnvTyping fenv ftenv).
Proof.
  destruct k.
  inversion f; subst.
  econstructor.
  eauto.
  subst ftenv' fenv'.
  econstructor.
  eauto.
Defined.  

Definition extrFEnvTJofFunX (fenv: funEnv) (tenv: valTC)
                             (e0 e1: Exp) (y: Id) (n: nat)
                             (k: sigT (fun ft =>
                                    FunTyping (FC fenv tenv e0 e1 y n) ft)) :
  FEnvTyping fenv (projT1 (extrFEnvTJofFun fenv tenv e0 e1 y n k)).
Proof.
  eapply (projT2 (extrFEnvTJofFun fenv tenv e0 e1 y n k)).
Defined.  


Definition extrFEnvTJofFun1 (fenv: funEnv) (tenv: valTC)
                             (e0 e1: Exp) (y: Id) (n: nat)
           (k: sigT (fun ft => FunTyping (FC fenv tenv e0 e1 y (S n)) ft)) :
  sigT (fun ftenv => FEnvTyping ((y,FC fenv tenv e0 e1 y n)::fenv) ftenv).
Proof.
  destruct k.
  inversion f; subst.
  econstructor 1 with (x:= ftenv').
  subst ftenv' fenv'.
  constructor.
  auto.
  auto.
Defined.  

Definition extrFEnvTJofFun1X (fenv: funEnv) (tenv: valTC)
                             (e0 e1: Exp) (y: Id) (n: nat)
                             (k: sigT (fun ft =>
                                 FunTyping (FC fenv tenv e0 e1 y (S n)) ft)) :
  FEnvTyping ((y,FC fenv tenv e0 e1 y n)::fenv)
             (projT1 (extrFEnvTJofFun1 fenv tenv e0 e1 y n k)).
Proof.
  eapply (projT2 (extrFEnvTJofFun1 fenv tenv e0 e1 y n k)).
Defined.  

Definition extrFEnvTJofFun1Y (fenv: funEnv) (tenv: valTC)
                             (e0 e1: Exp) (y: Id) (n: nat)
                             (k: sigT (fun ft =>
                                 FunTyping (FC fenv tenv e0 e1 y (S n)) ft)) :
  FEnvTyping ((y,FC fenv tenv e0 e1 y n)::fenv)
     ((y, projT1 k) :: (projT1 (extrFEnvTJofFun fenv tenv e0 e1 y (S n) k))).
Proof.
  constructor.
  eapply UniFTypeLmNZ1.
  eapply (projT2 k).  
  eapply (projT2 (extrFEnvTJofFun fenv tenv e0 e1 y (S n) k)).
Defined.  

Definition extrFEnvTJofFun1Z(fenv: funEnv) (tenv: valTC)
                             (e0 e1: Exp) (y: Id) (n: nat)
                             (k: sigT (fun ft =>
                                 FunTyping (FC fenv tenv e0 e1 y n) ft)) :
  FEnvTyping ((y,FC fenv tenv e0 e1 y n)::fenv)
     ((y, projT1 k) :: (projT1 (extrFEnvTJofFun fenv tenv e0 e1 y n k))).
Proof.
  constructor.
  eapply (projT2 k).  
  eapply (projT2 (extrFEnvTJofFun fenv tenv e0 e1 y n k)).
Defined.  


Program Fixpoint mapG2 {V A B C: Type} {h: DEq V} (R: A -> B -> Type)
        (f: forall e: A, (sigT (fun x => R e x)) -> C)
        (env: genEnv V A)    
        (k: sigT (fun tenv => MatchEnvsT R env tenv)): 
        genEnv V C := _.
Next Obligation.
  intros.
  destruct k.
  induction m.
  exact nil.
  specialize (f v1).
  assert ({x : B & R v1 x}).
  econstructor.
  eauto.
  specialize (f X).
  exact ((k, f):: IHm).
Defined.


Definition extrExpTJofFun0 (fenv: funEnv) (tenv: valTC)
                             (e0 e1: Exp) (y: Id)
                             (k: sigT (fun ft =>
                                   FunTyping (FC fenv tenv e0 e1 y 0) ft))
                             (ftenv: funTC)
                             (k1: FEnvTyping fenv ftenv) :
  sigT (fun t => ExpTyping ftenv tenv fenv e0 t).
destruct k.
inversion f; subst.
assert (ftenv = ftenv0).
eapply UniqueFEnvType.
eauto.
eauto.
econstructor.
rewrite H.
eauto.
Defined.


Definition extrExpTJofFun1 (fenv: funEnv) (tenv: valTC)
                             (e0 e1: Exp) (y: Id) (n: nat)
                             (k: sigT (fun ft =>
                                FunTyping (FC fenv tenv e0 e1 y (S n)) ft)) 
                             (ftenv: funTC)
                             (k1: FEnvTyping fenv ftenv) :
  sigT (fun t => ExpTyping ((y, FT tenv t)::ftenv) tenv
                            ((y, FC fenv tenv e0 e1 y n)::fenv) e1 t).
  destruct k.
  inversion f; subst.
  subst ftenv' fenv'.
  econstructor 1 with (x:=t).
  assert (ftenv = ftenv0).
  eapply UniqueFEnvType.
  eauto.
  eauto.
  rewrite H.
  auto.
Defined.   

Definition extrExpTJofFun1A (fenv: funEnv) (tenv: valTC)
                             (e0 e1: Exp) (y: Id) (n: nat)
                             (k: sigT (fun ft =>
                                FunTyping (FC fenv tenv e0 e1 y (S n)) ft)) 
                             (ftenv: funTC)
                             (k1: FEnvTyping fenv ftenv) :
  sigT (fun t => ExpTyping ((y, FT tenv t)::ftenv) tenv
                            ((y, FC fenv tenv e0 e1 y n)::fenv) e1 t).
  destruct k.
  inversion f; subst.
  subst ftenv' fenv'.
  econstructor 1 with (x:=t).
  assert (ftenv = ftenv0).
  eapply UniqueFEnvType.
  eauto.
  eauto.
  rewrite H.
  auto.
Defined.   


(*********************** TFun *****************************************)

Definition TFun : Type :=
  sigT (fun f:Fun => (sigT (fun ft:FTyp => FunTyping f ft))).  


Definition tfunEnv : Type := 
 list (Id * sigT (fun f:Fun => (sigT (fun ft:FTyp => FunTyping f ft)))).


Definition wtFEnv : Type :=
  sigT (fun fenv: funEnv => sigT (fun ftenv: funTC => FEnvTyping fenv ftenv)).


Program Fixpoint fenvConvP0 (fenv: funEnv) (ftenv: funTC)
        (k: FEnvTyping fenv ftenv) : tfunEnv := _.
Next Obligation.
  intros.
  induction k.
  exact nil.
  eapply ((k, existT _ v1 (existT _ v2 r)) :: IHk).
(*  Show Proof. *)
Defined.

Fixpoint fenvConv0 (fenv: funEnv) (ftenv: funTC) (k: FEnvTyping fenv ftenv) :
              tfunEnv :=
  MatchEnvsT_rect StaticI.Id Fun FTyp IdT.IdEq FunTyping
   (fun (fenv0 : Envr StaticI.Id Fun) (ftenv0 : Envr StaticI.Id FTyp)
      (_ : MatchEnvsT FunTyping fenv0 ftenv0) => tfunEnv) []
   (fun (ls1 : Envr StaticI.Id Fun) (ls2 : Envr StaticI.Id FTyp)
      (k0 : StaticI.Id) (v1 : Fun) (v2 : FTyp) (r : FunTyping v1 v2)
      (_ : MatchEnvsT FunTyping ls1 ls2) (IHk : tfunEnv) =>
    (k0,
    existT (fun f : Fun => {ft : FTyp & FunTyping f ft}) v1
      (existT (fun ft : FTyp => FunTyping v1 ft) v2 r)) :: IHk) fenv ftenv k.


Program Fixpoint fenvConvP (fenv: funEnv) (ftenv: funTC)
        (k: FEnvTyping fenv ftenv) : tfunEnv := _.
Next Obligation.
  fix IH 3.
  intros.
  destruct k. 
  exact nil.
  eapply ((k, existT _ v1 (existT _ v2 f)) :: (IH ls1 ls2 k0)).
  (* Show Proof. *)
Defined.

Fixpoint fenvConv (fenv: funEnv) (ftenv: funTC) (k: FEnvTyping fenv ftenv) :
   tfunEnv :=
   match k with
   | MatchEnvs_NilT _ => []
   | MatchEnvs_ConsT _ ls1 ls2 k0 v1 v2 f k1 =>
       (k0,
       existT (fun f0 : Fun => {ft : FTyp & FunTyping f0 ft}) v1
         (existT (fun ft : FTyp => FunTyping v1 ft) v2 f)) :: 
       fenvConv ls1 ls2 k1
   end.


Program Fixpoint fenvConvXP (w: sigT (fun fenv: funEnv =>
       sigT (fun ftenv: funTC => FEnvTyping fenv ftenv))) : tfunEnv := _.
Next Obligation.
  intros.
  destruct w as [ftenv w].
  destruct w as [fenv w].
  exact (fenvConv ftenv fenv w).
  (* Show Proof. *)
Defined.

Definition fenvConvX (w: sigT (fun fenv: funEnv =>
               sigT (fun ftenv: funTC => FEnvTyping fenv ftenv))) : tfunEnv :=
 let (ftenv, w0) := w in let (fenv, w1) := w0 in fenvConv ftenv fenv w1.



Program Fixpoint fenvConvIP0 (tfenv: tfunEnv) :
  sigT (fun fenv: funEnv =>
          sigT (fun ftenv: funTC => FEnvTyping fenv ftenv)) := _.
Next Obligation.
  intros.
  induction tfenv.
  constructor 1 with (x:=nil).
  constructor 1 with (x:=nil).
  constructor.
  destruct IHtfenv as [fenv H].
  destruct H as [ftenv H].
  destruct a as [x a].
  destruct a as [f a].
  destruct a as [ft k].
  constructor 1 with (x:=(x,f)::fenv).
  constructor 1 with (x:=(x,ft)::ftenv).
  constructor.
  exact k.
  exact H.
  (* Show Proof. *)
Defined.  


Program Fixpoint fenvConvIP (tfenv: tfunEnv) :
  sigT (fun fenv: funEnv =>
          sigT (fun ftenv: funTC => FEnvTyping fenv ftenv)) := _.
Next Obligation.
  fix IH 1.
  intros.
  destruct tfenv.
  constructor 1 with (x:=nil).
  constructor 1 with (x:=nil).
  constructor.
  specialize (IH tfenv).
  destruct IH as [fenv H].
  destruct H as [ftenv H].
  destruct p as [x a].
  destruct a as [f a].
  destruct a as [ft k].
  constructor 1 with (x:=(x,f)::fenv).
  constructor 1 with (x:=(x,ft)::ftenv).
  constructor.
  exact k.
  exact H.
  (* Show Proof. *)
Defined.  
  
Fixpoint fenvConvI (tfenv: tfunEnv) :
  sigT (fun fenv: funEnv =>
          sigT (fun ftenv: funTC => FEnvTyping fenv ftenv)) :=
   match tfenv with
   | [] =>
       existT (fun fenv : funEnv => {ftenv : funTC & FEnvTyping fenv ftenv})
         []
         (existT (fun ftenv : funTC => FEnvTyping [] ftenv) []
            (MatchEnvs_NilT FunTyping))
   | p :: tfenv0 =>
       let (fenv, H) := fenvConvI tfenv0 in
       let (ftenv, H0) := H in
       let (x, a) := p in
       let (f, a0) := a in
       let (ft, k) := a0 in
       existT
         (fun fenv0 : funEnv => {ftenv0 : funTC & FEnvTyping fenv0 ftenv0})
         ((x, f) :: fenv)
         (existT (fun ftenv0 : funTC => FEnvTyping ((x, f) :: fenv) ftenv0)
            ((x, ft) :: ftenv)
            (MatchEnvs_ConsT FunTyping fenv ftenv x f ft k H0))
   end.


Lemma fenvConvE (tfenv: tfunEnv) : fenvConvX (fenvConvI tfenv) = tfenv.
  induction tfenv.
  simpl. 
  auto.  
  simpl.
  rewrite <- IHtfenv at 2.
  unfold fenvConvX.
  simpl.
  destruct a.
  destruct s.
  destruct s.
  destruct (fenvConvI tfenv).
  destruct s.
  simpl.
  f_equal.
Defined.
  
Lemma fenvConvEI (w: sigT (fun fenv: funEnv =>
               sigT (fun ftenv: funTC => FEnvTyping fenv ftenv))) :
  fenvConvI (fenvConvX w) = w.
intros.  
destruct w as [fenv w].
destruct w as [ftenv w].
simpl.
induction w.
simpl.
auto.
simpl.
rewrite IHw.
auto.
Defined.

Inductive WExpTyping (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                      (e: Exp) (t: VTyp)
                      (k: FEnvTyping fenv ftenv) : Type :=
  WExp : 
    ExpTyping ftenv tenv fenv e t ->
    WExpTyping ftenv tenv fenv e t k.

Inductive WPrmsTyping (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                      (ps: Prms) (pt: PTyp)
                      (k: FEnvTyping fenv ftenv) : Type :=
  WPrms : 
    PrmsTyping ftenv tenv fenv ps pt ->
    WPrmsTyping ftenv tenv fenv ps pt k.

Inductive WQFunTyping (ftenv: funTC) (fenv: funEnv)
                      (qf: QFun) (ft: FTyp)
                      (k: FEnvTyping fenv ftenv) : Type :=
  WQFun : 
    QFunTyping ftenv fenv qf ft ->
    WQFunTyping ftenv fenv qf ft k.


Definition TExpTyping (tenv: valTC) (tfenv: tfunEnv) (e: Exp) (t: VTyp) :=
  let wtfenv := fenvConvI tfenv in
  let fenv := projT1 wtfenv in
  let rest := projT2 wtfenv in
  let ftenv := projT1 rest in
  let k := projT2 rest in
  WExpTyping ftenv tenv fenv e t k. 

Definition TPrmsTyping (tenv: valTC) (tfenv: tfunEnv)
                        (ps: Prms) (pt: PTyp) :=
  let wtfenv := fenvConvI tfenv in
  let fenv := projT1 wtfenv in
  let rest := projT2 wtfenv in
  let ftenv := projT1 rest in
  let k := projT2 rest in
  WPrmsTyping ftenv tenv fenv ps pt k. 

Definition TQFunTyping (tfenv: tfunEnv) (qf: QFun) (ft: FTyp) :=
  let wtfenv := fenvConvI tfenv in
  let fenv := projT1 wtfenv in
  let rest := projT2 wtfenv in
  let ftenv := projT1 rest in
  let k := projT2 rest in
  WQFunTyping ftenv fenv qf ft k. 


Definition textrQValTJofRet (tenv: valTC) (tfenv: tfunEnv)
           (z: Tag) (q: QValue)
           (k: sigT (fun t =>
                  TExpTyping tenv tfenv (Return z q) t)) :
  sigT (fun t => QValueTyping tenv q t).
Proof.
  destruct k as [t k].
  inversion k; subst.
  inversion X; subst.
  constructor 1 with (x:= t).
  auto.
Defined.
  
Definition textrQValTJofMod (tenv: valTC) (tfenv: tfunEnv)
           (T1 T2: Type) (VT1: ValTyp T1) (VT2: ValTyp T2)
           (XF: XFun T1 T2)
           (q: QValue)
           (k: sigT (fun t =>
                  TExpTyping tenv tfenv (Modify T1 T2 VT1 VT2 XF q) t)) :
  sigT (fun t => QValueTyping tenv q t).
Proof.
  destruct k as [t k].
  inversion k; subst.
  inversion X; subst.
  constructor 1 with (x:= vtyp T1).
  auto.
Defined.


Definition textrExpTJofBindN1
           (tenv: valTC) (tfenv: tfunEnv) (e1 e2: Exp)
           (k: sigT (fun t => TExpTyping tenv tfenv (BindN e1 e2) t)) :
  sigT (fun t => TExpTyping tenv tfenv e1 t).
  destruct k as [t k].
  inversion k; subst.
  inversion X; subst.
  constructor 1 with (x:=t1).
  constructor.
  auto.
Defined.  

Definition textrExpTJofBindN2
           (tenv: valTC) (tfenv: tfunEnv) (e1 e2: Exp)
           (k: sigT (fun t => TExpTyping tenv tfenv (BindN e1 e2) t)) :
  sigT (fun t => TExpTyping tenv tfenv e2 t).
  destruct k as [t k].
  constructor 1 with (x:=t).
  inversion k; subst.
  inversion X; subst.
  constructor.
  auto.
Defined.  

Definition textrExpTJofBindS1
           (tenv: valTC) (tfenv: tfunEnv) (x: Id) (e1 e2: Exp)
           (k: sigT (fun t => TExpTyping tenv tfenv (BindS x e1 e2) t)) :
  sigT (fun t => TExpTyping tenv tfenv e1 t).
  destruct k as [t k].
  inversion k; subst.
  inversion X; subst.
  subst tenv'.
  constructor 1 with (x:=t1).
  constructor.
  auto.
Defined.  

Definition textrExpTJofBindS2
           (tenv: valTC) (tfenv: tfunEnv)
           (x: Id) (e1 e2: Exp)
           (k: sigT (fun t => TExpTyping tenv tfenv (BindS x e1 e2) t))
           (t1: VTyp)
           (k1: TExpTyping tenv tfenv e1 t1):
  sigT (fun t => TExpTyping ((x, t1)::tenv) tfenv e2 t).
  destruct k as [t k].
  constructor 1 with (x:=t).
  inversion k; subst.
  inversion X; subst.
  subst tenv'.
  assert (t0 = t1).
  eapply UniqueExpType.
  exact (projT2 (projT2 (fenvConvI tfenv))).
  eauto.
  inversion k1; subst.
  eauto.
  rewrite <- H.
  constructor.
  auto.
Defined.  


Definition textrQFunTJofApply
           (tenv: valTC) (tfenv: tfunEnv)
           (q: QFun) (ps: Prms)
           (k: sigT (fun t => TExpTyping tenv tfenv (Apply q ps) t)) :
     sigT (fun ft => TQFunTyping tfenv q ft).
Proof.
  destruct k as [t k].
  inversion k; subst.
  inversion X; subst.
  constructor 1 with (x:= FT fps t).
  constructor.
  auto.
Defined.

Definition textrPrmsTJofApply
           (tenv: valTC) (tfenv: tfunEnv)
           (q: QFun) (ps: Prms)
           (k: sigT (fun t => TExpTyping tenv tfenv (Apply q ps) t)) :
     sigT (fun pt => TPrmsTyping tenv tfenv ps pt).
Proof.
  destruct k as [t k].
  inversion k; subst.
  inversion X; subst.
  constructor 1 with (x:= PT (map snd fps)).
  constructor.
  auto.
Defined.

Definition textrExpTJofIF1
           (tenv: valTC) (tfenv: tfunEnv)
           (e1 e2 e3: Exp)
           (k: sigT (fun t =>
                  TExpTyping tenv tfenv (IfThenElse e1 e2 e3) t)) :
     sigT (fun t => TExpTyping tenv tfenv e1 t).
Proof.
  destruct k as [t k].
  inversion k; subst.
  inversion X; subst.
  constructor 1 with (x:= Bool).
  constructor.
  auto.
Defined.           

Definition textrExpTJofIF2
           (tenv: valTC) (tfenv: tfunEnv)
           (e1 e2 e3: Exp)
           (k: sigT (fun t =>
                  TExpTyping tenv tfenv (IfThenElse e1 e2 e3) t)) :
     sigT (fun t => TExpTyping tenv tfenv e2 t).
Proof.
  destruct k as [t k].
  inversion k; subst.
  inversion X; subst.
  constructor 1 with (x:= t).
  constructor.
  auto.
Defined.

Definition textrExpTJofIF3
           (tenv: valTC) (tfenv: tfunEnv)
           (e1 e2 e3: Exp)
           (k: sigT (fun t =>
                  TExpTyping tenv tfenv (IfThenElse e1 e2 e3) t)) :
     sigT (fun t => TExpTyping tenv tfenv e3 t).
Proof.
  destruct k as [t k].
  inversion k; subst.
  inversion X; subst.
  constructor 1 with (x:= t).
  constructor.
  auto.
Defined.


Definition textrExpTJofPS (tenv: valTC) (tfenv: tfunEnv)
           (es: list Exp)
           (k: sigT (fun pt => TPrmsTyping tenv tfenv (PS es) pt)) :
           sigT (fun ts => Forall2T (TExpTyping tenv tfenv) es ts).
  intros.
  destruct k.
  destruct x.
  constructor 1 with (x:=ts).
  inversion t; subst.
  inversion X; subst.
  induction X0.
  constructor.
  constructor.
  constructor.
  auto.
  eapply IHX0.
  constructor.
  constructor.
  auto.
  constructor.
  auto.
Defined.  


Definition textrFunTJofQFun
           (tfenv: tfunEnv)
           (f: Fun) 
           (k: sigT (fun ft => TQFunTyping tfenv (QF f) ft)) :
     sigT (fun ft => FunTyping f ft).
Proof.
  destruct k as [t k].
  inversion k; subst.
  inversion X; subst.
  constructor 1 with (x:= t).
  auto.
Defined.

Definition textrFunTJofQFunA
           (tfenv: tfunEnv)
           (f: Fun)
           (ft: FTyp)
           (k: TQFunTyping tfenv (QF f) ft) :
           FunTyping f ft.
Proof.
  inversion k; subst.
  inversion X; subst.
  auto.
Defined.


Definition textrFunTJofQFunX
           (tfenv: tfunEnv)
           (f: Fun)
           (ft: FTyp)
           (k: sigT (fun ft => TQFunTyping tfenv (QF f) ft)) :
           FunTyping f (projT1 k).
Proof.
  assert (TQFunTyping tfenv (QF f) (projT1 k)).
  apply (projT2 k).
  inversion X; subst.
  inversion X0; subst.
  auto.
Defined.

(**********************************************************************)

Definition textrFEnvTJofFun0 (fenv: funEnv) (tenv: valTC)
                           (e0 e1: Exp) (y: Id)
                           (k: sigT (fun ft =>
                                FunTyping (FC fenv tenv e0 e1 y 0) ft))
                           (k1: sigT (fun ftenv => FEnvTyping fenv ftenv)) :
  tfunEnv.
Proof.  
  destruct k.
  destruct k1.
  inversion f; subst.
  assert (x0 = ftenv).
  eapply UniqueFEnvType.
  exact f0.
  exact X.
  rewrite H in *.
  clear H X x0.
  exact (fenvConv fenv ftenv f0).
Defined.  
  
Definition mk_wtFEnv (fenv: funEnv) (ftenv: funTC)
           (k: FEnvTyping fenv ftenv) : wtFEnv :=
  existT _ fenv (existT _ ftenv k).

Definition textrExpTJofFun0 (fenv: funEnv) (tenv: valTC)
                             (e0 e1: Exp) (y: Id)
                             (k: sigT (fun ft =>
                                   FunTyping (FC fenv tenv e0 e1 y 0) ft))
                             (ftenv: funTC)
                             (k1: FEnvTyping fenv ftenv) :
  let tfenv := fenvConvX (mk_wtFEnv fenv ftenv k1) in 
  sigT (fun t => TExpTyping tenv tfenv e0 t).
  destruct k.
  cbv zeta.
  inversion f; subst.
  econstructor 1 with (x:=t).
  assert (ftenv = ftenv0).
  eapply UniqueFEnvType.
  eauto.
  eauto.
  unfold TExpTyping.
  constructor.
  revert X.
  revert X0.
  rewrite <- H.
  intros.
  rewrite (fenvConvEI (mk_wtFEnv fenv ftenv k1)).
  simpl.
  auto.
Defined.


Definition tfunEnvExtend (tfenv: tfunEnv)
           (x: Id)
           (f: Fun)
           (k: sigT (fun ft => FunTyping f ft)) : tfunEnv :=
  let ff := existT _ f k in
  (x,ff) :: tfenv.


Program Definition UniFTypeLmNZE1a (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft: FTyp) :
  forall n: nat,
    FunTyping (FC fenv tenv0 e0 e1 x (S n)) ft ->
    sigT (fun ft0 => FunTyping (FC fenv tenv0 e0 e1 x n) ft0) := _.
Next Obligation.
  intros.
  constructor 1 with (x:=ft).
  inversion X.
  exact X2.
Defined.


Definition textrExpTJofFun1 (fenv: funEnv) (tenv: valTC)
                             (e0 e1: Exp) (y: Id) (n: nat)
                             (k: sigT (fun ft =>
                                   FunTyping (FC fenv tenv e0 e1 y (S n)) ft))
                             (ftenv: funTC)
                             (k1: FEnvTyping fenv ftenv) :
  let ft := projT1 k in 
  let fenv' := (y, FC fenv tenv e0 e1 y n)::fenv in
  let ftenv' := (y, ft)::ftenv in
  let k2 := UniFTypeLmNZ1 fenv tenv e0 e1 y ft n (projT2 k) in   
  let k3 := updateFEnvLemma fenv ftenv y (FC fenv tenv e0 e1 y n)
                            ft k1 k2 in
  let tfenv := fenvConvX (mk_wtFEnv fenv' ftenv' k3) in
  sigT (fun t => TExpTyping tenv tfenv e1 t).
  destruct k.
  destruct x.
  cbv zeta.
  constructor 1 with (x:=ret_type). 
  constructor.
  rewrite (fenvConvEI (mk_wtFEnv _ _ _)).
  simpl.
  inversion f; subst.
  subst ftenv' fenv'.
  assert (ftenv = ftenv0).
  eapply UniqueFEnvType.
  eauto.
  eauto.
  revert X X0.
  rewrite <- H.
  intros.
  exact X0.
Defined.



Definition updateEnvT {K V1 V2: Type} {h: DEq K}
     (rel: V1 -> V2 -> Type)
     (env1: Envr K V1) (env2: Envr K V2) (x: K)
     (v1: V1) (v2: V2)
     (X: MatchEnvsT rel env1 env2)
     (X0: rel v1 v2) : 
    MatchEnvsT rel ((x, v1) :: env1) ((x, v2) :: env2) :=
 MatchEnvs_ConsT rel env1 env2 x v1 v2 X0 X.

Definition updateFEnvT := updateEnvT FunTyping.



Lemma updateConvE 
(fenv: funEnv) (tenv: valTC)
(e0 e1: Exp) (y: Id) (n: nat)
(ft : FTyp)               
(k : FunTyping (FC fenv tenv e0 e1 y n) ft)
(ftenv: funTC)
(k1: FEnvTyping fenv ftenv) : 

 (fenvConvI (tfunEnvExtend (fenvConvX (mk_wtFEnv fenv ftenv k1)) y
             (FC fenv tenv e0 e1 y n)
             (existT
                (fun ft0 : FTyp => FunTyping (FC fenv tenv e0 e1 y n) ft0)
                ft k))) = 
 (existT (fun fenv0 => (sigT (fun ftenv0 => FEnvTyping fenv0 ftenv0)))
         ((y,FC fenv tenv e0 e1 y n)::fenv) (existT _ ((y,ft)::ftenv) 
         (updateFEnvT fenv ftenv y (FC fenv tenv e0 e1 y n) ft k1 k))).
Proof.
  simpl.
  unfold updateFEnvT.
  unfold updateEnvT.
  assert (fenvConvI (fenvConv fenv ftenv k1) =
          fenvConvI (fenvConvX (mk_wtFEnv fenv ftenv k1))).
  simpl.
  auto.
  rewrite H.
  rewrite fenvConvEI.
  simpl.
  reflexivity.
Defined.  
  

Definition textrExpTJofFun1b (fenv: funEnv) (tenv: valTC)
                             (e0 e1: Exp) (y: Id) (n: nat)
                             (k0: sigT (fun ft =>
                                   FunTyping (FC fenv tenv e0 e1 y (S n)) ft))
                             (k: sigT (fun ft =>
                                   FunTyping (FC fenv tenv e0 e1 y n) ft))
                             (ftenv: funTC)
                             (k1: FEnvTyping fenv ftenv) :
  let tfenv := fenvConvX (mk_wtFEnv fenv ftenv k1) in
  let tfenv' := tfunEnvExtend tfenv y (FC fenv tenv e0 e1 y n) k in
  sigT (fun t => TExpTyping tenv tfenv' e1 t).
  destruct k.
  destruct x.
  cbv zeta.
  constructor 1 with (x:=ret_type). 
  constructor.

  rewrite updateConvE.
  simpl.
  inversion k0; subst.
  inversion X; subst.
  subst ftenv' fenv'.
  
  assert (StaticI.FT prs_type ret_type = StaticI.FT tenv t).
  eapply UniqueFunType.
  eauto.
  eauto.
  assert (ftenv0 = ftenv).
  eapply UniqueFEnvType.
  eauto.
  eauto.
  injection H.
  intros.
  rewrite H1.
  rewrite H2.
  rewrite H0 in *.
  auto.
Defined.


(*********************** TFun2 ****************************************)

Definition TFunI : Type :=
  sigT (fun ft:FTyp => (sigT (fun f:Fun => FunTyping f ft))).  


Definition tfunEnvI : Type := 
 list (Id * sigT (fun ft:FTyp => (sigT (fun f:Fun => FunTyping f ft)))).


Definition wtFEnvI : Type :=
  sigT (fun ftenv: funTC => sigT (fun fenv: funEnv => FEnvTyping fenv ftenv)).


End DECaux.

