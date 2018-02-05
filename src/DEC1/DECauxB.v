
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

(*
Add LoadPath "/home/ptorrx/lib".
*)


(* Require Import Csyntax. *)

Require Coq.Vectors.VectorDef. 

(*
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

(*
Definition computeFTenv (fenv: funEnv) : funTC :=
  map () 
*)

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



(*
Fixpoint Fun2C_aux1 (f: Fun)
            (k: sigT (fun ft => FunTyping f ft)) (ft: FTyp) :
  sigT (fun ft => FunTyping f ft) -> NamedDef :=
  let 
*)

(*********************** TFun *****************************************)

Definition TFun : Type :=
  sigT (fun f:Fun => (sigT (fun ft:FTyp => FunTyping f ft))).  

(*
Definition tfunEnv : Type := list (Id * TFun).
*)

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

(* ZERO *)
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



(*  ONE *)
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
  

(* TWO - relate to zero *)
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

(*
Definition tfunEnv : Type := list (Id * TFun).
*)

Definition tfunEnvI : Type := 
 list (Id * sigT (fun ft:FTyp => (sigT (fun f:Fun => FunTyping f ft)))).


Definition wtFEnvI : Type :=
  sigT (fun ftenv: funTC => sigT (fun fenv: funEnv => FEnvTyping fenv ftenv)).


End DECaux.

(*
old proofs with tfunEnvI - 

Program Fixpoint fenvConvP0 (fenv: funEnv) (ftenv: funTC) (k: FEnvTyping fenv ftenv) : tfunEnv := _.
Next Obligation.
  intros.
  induction k.
  exact nil.
  eapply ((k, existT _ v2 (existT _ v1 r)) :: IHk).
  Show Proof.
Defined.

Fixpoint fenvConv0 (fenv: funEnv) (ftenv: funTC) (k: FEnvTyping fenv ftenv) : tfunEnv :=
 MatchEnvsT_rect Id Fun FTyp IdEq FunTyping
   (fun (fenv0 : Envr Id Fun) (ftenv0 : Envr Id FTyp)
      (_ : MatchEnvsT FunTyping fenv0 ftenv0) => tfunEnv) []
   (fun (ls1 : Envr Id Fun) (ls2 : Envr Id FTyp)
      (k0 : Id) (v1 : Fun) (v2 : FTyp) (r : FunTyping v1 v2)
      (_ : MatchEnvsT FunTyping ls1 ls2) (IHk : tfunEnv) =>
    (k0,
    existT (fun ft : FTyp => {f : Fun & FunTyping f ft}) v2
      (existT (fun f : Fun => FunTyping f v2) v1 r)) :: IHk) fenv ftenv k.
 


Program Fixpoint fenvConvP (fenv: funEnv) (ftenv: funTC) (k: FEnvTyping fenv ftenv) : tfunEnv := _.
Next Obligation.
  fix IH 3.
  intros.
  destruct k. 
  exact nil.
  eapply ((k, existT _ v2 (existT _ v1 f)) :: (IH ls1 ls2 k0)).
  Show Proof.
Defined.

Fixpoint fenvConv (fenv: funEnv) (ftenv: funTC) (k: FEnvTyping fenv ftenv) :
   tfunEnv :=
   match k with
   | MatchEnvs_NilT _ => []
   | MatchEnvs_ConsT _ ls1 ls2 k0 v1 v2 f k1 =>
       (k0,
       existT (fun ft : FTyp => {f0 : Fun & FunTyping f0 ft}) v2
         (existT (fun f0 : Fun => FunTyping f0 v2) v1 f)) :: 
       fenvConv ls1 ls2 k1
   end.



Program Fixpoint fenvConvXP (w: sigT (fun ftenv: funTC =>
               sigT (fun fenv: funEnv => FEnvTyping fenv ftenv))) : tfunEnv := _.
Next Obligation.
  intros.
  destruct w as [ftenv w].
  destruct w as [fenv w].
  exact (fenvConv fenv ftenv w).
  Show Proof.
Defined.

Definition fenvConvX (w: sigT (fun ftenv: funTC =>
               sigT (fun fenv: funEnv => FEnvTyping fenv ftenv))) : tfunEnv :=
 let (ftenv, w0) := w in let (fenv, w1) := w0 in fenvConv fenv ftenv w1.



Program Fixpoint fenvConvIP0 (tfenv: tfunEnv) :
  sigT (fun ftenv: funTC => sigT (fun fenv: funEnv => FEnvTyping fenv ftenv)) := _.
Next Obligation.
  intros.
  induction tfenv.
  constructor 1 with (x:=nil).
  constructor 1 with (x:=nil).
  constructor.
  destruct IHtfenv as [ftenv H].
  destruct H as [fenv H].
  destruct a as [x a].
  destruct a as [ft a].
  destruct a as [f k].
  constructor 1 with (x:=(x,ft)::ftenv).
  constructor 1 with (x:=(x,f)::fenv).
  constructor.
  exact k.
  exact H.
  Show Proof.
Defined.  


Program Fixpoint fenvConvIP (tfenv: tfunEnv) :
  sigT (fun ftenv: funTC => sigT (fun fenv: funEnv => FEnvTyping fenv ftenv)) := _.
Next Obligation.
  fix IH 1.
  intros.
  destruct tfenv.
  constructor 1 with (x:=nil).
  constructor 1 with (x:=nil).
  constructor.
  specialize (IH tfenv).
  destruct IH as [ftenv H].
  destruct H as [fenv H].
  destruct p as [x a].
  destruct a as [ft a].
  destruct a as [f k].
  constructor 1 with (x:=(x,ft)::ftenv).
  constructor 1 with (x:=(x,f)::fenv).
  constructor.
  exact k.
  exact H.
  Show Proof.
Defined.  
  
Fixpoint fenvConvI (tfenv: tfunEnv) :
  sigT (fun ftenv: funTC => sigT (fun fenv: funEnv => FEnvTyping fenv ftenv)) :=
   match tfenv with
   | [] =>
       existT (fun ftenv : funTC => {fenv : funEnv & FEnvTyping fenv ftenv})
         []
         (existT (fun fenv : funEnv => FEnvTyping fenv []) []
            (MatchEnvs_NilT FunTyping))
   | p :: tfenv0 =>
       let (ftenv, H) := fenvConvI tfenv0 in
       let (fenv, H0) := H in
       let (x, a) := p in
       let (ft, a0) := a in
       let (f, k) := a0 in
       existT
         (fun ftenv0 : funTC => {fenv0 : funEnv & FEnvTyping fenv0 ftenv0})
         ((x, ft) :: ftenv)
         (existT (fun fenv0 : funEnv => FEnvTyping fenv0 ((x, ft) :: ftenv))
            ((x, f) :: fenv)
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
  
Lemma fenvConvEI (w: sigT (fun ftenv: funTC =>
               sigT (fun fenv: funEnv => FEnvTyping fenv ftenv))) :
  fenvConvI (fenvConvX w) = w.
intros.  
destruct w as [ftenv w].
destruct w as [fenv w].
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
  let ftenv := projT1 wtfenv in
  let rest := projT2 wtfenv in
  let fenv := projT1 rest in
  let k := projT2 rest in
  WExpTyping ftenv tenv fenv e t k. 

Definition TPrmsTyping (tenv: valTC) (tfenv: tfunEnv)
                        (ps: Prms) (pt: PTyp) :=
  let wtfenv := fenvConvI tfenv in
  let ftenv := projT1 wtfenv in
  let rest := projT2 wtfenv in
  let fenv := projT1 rest in
  let k := projT2 rest in
  WPrmsTyping ftenv tenv fenv ps pt k. 

Definition TQFunTyping (tfenv: tfunEnv) (qf: QFun) (ft: FTyp) :=
  let wtfenv := fenvConvI tfenv in
  let ftenv := projT1 wtfenv in
  let rest := projT2 wtfenv in
  let fenv := projT1 rest in
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


End DECaux.

************************************************************************* *)

(*
Fixpoint Exp2C

       (P2C : forall (ls: genEnv Id NamedDef)
             (tenv: valTC) (tfenv: tfunEnv)
             (ps: Prms) 
             (k: sigT (fun pt => TPrmsTyping tenv tfenv ps pt)),
          list LStat * tfunEnv)

       (ls: genEnv Id NamedDef)
       (tfenv: tfunEnv)
       (e: Exp) 
       (k: sigT (fun t => TExpTyping tenv tfenv e t)) :
       (LStat * tfunEnv) :=
  
 (match e return (sigT (fun t => ExpTyping ftenv tenv fenv e t) -> LStat) with
  | Modify TI TO VTI VTO XF q => fun k => 
    let f := Effect2C TI TO VTI VTO XF ls q in (LE f, tfenv) 
  | Return z q => fun k => 
    QVal2C tenv q (extrQValTJofRet ftenv tenv fenv z q k)
  | BindN e1 e2 => fun k => 
    let c1 := (Exp2C F2C P2C ls ftenv tenv fenv k0 e1
                     (extrExpTJofBindN1 ftenv tenv fenv e1 e2 k)) in
    let c2 := (Exp2C F2C P2C ls ftenv tenv fenv k0 e2
                     (extrExpTJofBindN2 ftenv tenv fenv e1 e2 k)) in   
    match_Ecomma c1 c2 
  | BindS x e1 e2 => fun k => 
    let k1 := extrExpTJofBindS1 ftenv tenv fenv x e1 e2 k in
    let c1 := (Exp2C F2C P2C ls ftenv tenv fenv k0 e1 k1) in
    let c2 := lstat2glob c1 in
    let tenv' := (x, projT1 k1) :: tenv in
    let ct := VTyp2C (projT1 k1) in
    (* renaming issue *)
    Exp2C F2C P2C ((x, mkNamedDef (Id2ident x) c2 ct)::ls)
          ftenv tenv' fenv k0 e2 
          (extrExpTJofBindS2 ftenv tenv fenv k0 x e1 e2
                             k (projT1 k1) (projT2 k1))
  | BindMS fenv venv e => fun k => SUndef 
  | Apply q ps => fun k => 
    let cs := P2C ls ftenv tenv fenv k0 ps
                     (extrPrmsTJofApply ftenv tenv fenv q ps k) in 
    (match q return
    (sigT (fun t => ExpTyping ftenv tenv fenv (Apply q ps) t) -> LStat) with 
    | QF f => fun k => let x := getFunName f in
              let g := F2C f (extrFunTJofApply ftenv tenv fenv f ps k) in
              FPack (x, (Id2ident x, g)) (match_Ecall (Some g) cs)  
    | FVar x => fun k => match_Ecall (findE ls x) cs
    end) k 
  | Val v => fun k => Val2C v    
  | IfThenElse e1 e2 e3 => fun k => 
    let c1 := Exp2C F2C P2C ls ftenv tenv fenv k0 e1
                    (extrExpTJofIF1 ftenv tenv fenv e1 e2 e3 k) in
    let c2 := Exp2C F2C P2C ls ftenv tenv fenv k0 e2
                    (extrExpTJofIF2 ftenv tenv fenv e1 e2 e3 k) in
    let c3 := Exp2C F2C P2C ls ftenv tenv fenv k0 e3
                    (extrExpTJofIF3 ftenv tenv fenv e1 e2 e3 k) in 
    match_Econdition c1 c2 c3 
  end) k.


Program Fixpoint Fun2C 

        (E2C : forall (ls: genEnv Id NamedDef)                 
                      (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                      (k0: FEnvTyping fenv ftenv)
                      (e: Exp) 
                      (k: sigT (fun t => ExpTyping ftenv tenv fenv e t)),
                    LStat)

        (F2C : forall (f: Fun)
                (k: sigT (fun ft => FunTyping f ft)), NamedDef)

         (f: Fun)
         (k: sigT (fun ft => FunTyping f ft)) : NamedDef := _.

Next Obligation.
  intros.
  inversion k as [ft k0]; subst.
  assert (type) as cft.
  exact (FTyp2C ft).
  assert (globvar type) as y_dec.
  exact (mkglobvar cft nil false false).

  inversion k0; subst.
  
  - assert (list (ident * type)) as ctenv.
    exact (map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv).
    assert (sigT (fun ftenv => FEnvTyping fenv ftenv)) as k1.
    constructor 1 with (x:=ftenv).
    exact X.
    assert (genEnv Id NamedDef) as cfenv.
    exact (mapG2 FunTyping F2C fenv k1).
    assert (list (ident * type)) as cftenv.
    exact (map (fun x => (Id2ident (fst x), FTyp2C (snd x))) ftenv).

    assert (function) as cf.
    exact (mkfunction cft cc_default ctenv cftenv 
                        (lstat2stat (E2C cfenv ftenv tenv fenv X e0
                            (extrExpTJofFun0 fenv tenv e0 e1 x k ftenv X)))).

    apply (mkNamedDef (Id2ident x) (@Gfun fundef type (Internal cf)) cft).  
  - assert (list (ident * type)) as ctenv.
    exact (map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv).
    assert (sigT (fun ftenv => FEnvTyping fenv ftenv)) as k1. 
    constructor 1 with (x:=ftenv).
    exact X.
    assert (genEnv Id NamedDef) as cfenv.
    exact (mapG2 FunTyping F2C fenv k1).
    assert (list (ident * type)) as cftenv.
    exact (map (fun x => (Id2ident (fst x), FTyp2C (snd x))) ftenv).

    assert  (list (ident * type)) as cftenv'.
    exact ((Id2ident x, cft) :: cftenv).

    assert (FEnvTyping fenv' ftenv') as k3.
    constructor.
    exact X1.
    exact X.

    assert (sigT (fun t => ExpTyping ftenv' tenv fenv' e1 t)) as k4.
    constructor 1 with (x:=t).
    exact X0.
    
    assert (function) as cf.
    exact (mkfunction cft cc_default ctenv cftenv' 
                       (lstat2stat (E2C cfenv ftenv' tenv fenv' k3 e1 
                        k4))). 
    apply (mkNamedDef (Id2ident x) (@Gfun fundef type (Internal cf)) cft).
    Show Proof.
Defined.    
*)    


(*

Fixpoint Fun2C 

         (E2C : forall (h: CTag) (ls: genEnv Id NamedDef)                 
                         (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                         (k0: FEnvTyping fenv ftenv)
                         (e: Exp) 
                         (k: sigT (fun t => ExpTyping ftenv tenv fenv e t)),
             LStat h)

         (f: Fun)
         (k: sigT (fun ft => FunTyping f ft)) : NamedDef.

  refine (
  (match f return (sigT (fun ft => FunTyping f ft) -> NamedDef) with
   | FC fenv tenv e0 e1 y n => fun k =>
                                 
    let ft := projT1 k in
    let cft := FTyp2C ft in 
    let y_dec := mkglobvar (FTyp2C ft) nil false false in  
    let ctenv := map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv in

(*                            
        map (fun x => (fst x, (Id2ident (fst x),
                               Fun2C (snd x) (extrLFunTJofFun x k)))) fenv in
*)
    let k1 := extrLFunTJofFun fenv tenv e0 e1 y n k in
    let k2 := extrLFunTJofFunX fenv tenv e0 e1 y n k in 
    let ftenv := projT1 k1 in
    let cfenv := mapG2 FunTyping (Fun2C E2C) fenv k1 in
    let cftenv :=
        map (fun x => (Id2ident (fst x), FTyp2C (snd x))) ftenv in
    let cftenv' := (Id2ident y, cft) :: cftenv in

    let cf := (match n return (forall f, (sigT (fun ft =>
                FunTyping (FC fenv tenv e0 e1 y n) ft) ->
                forall (ftenv' ftenv0: funTC) (fenv' fenv0: funEnv),
                  ftenv' = ftenv0 -> fenv' = fenv0 -> function)) with

               | 0 => fun f k ftenv' ftenv0 fenv' fenv0 E1 E2 =>
                        
                        mkfunction cft cc_default ctenv cftenv 
                        (lstat2stat (E2C CS cfenv ftenv tenv fenv k2 e0
                               (extrExpTJofFun0 fenv tenv e0 e1 y k ftenv k2)))

               | S m => fun k f k ftenv' ftenv0 fenv' fenv0 E1 E2 =>
                                                    
(*                         let ftenv' := (* projT1 (extrLFunTJofFun1
                                                 fenv tenv e0 e1 y m k) in *)  
                                       (y, ft)::ftenv in 
                         let fenv' := (y, FC fenv tenv e0 e1 y m)::fenv in
*)
                         let kf1 := extrLFunTJofFun1 fenv tenv e0 e1 y m k in
                         let kf2 := extrLFunTJofFun1Y fenv tenv e0 e1 y m k in
                mkfunction cft cc_default ctenv cftenv' 
                             (E2C CS cfenv ftenv' tenv fenv' kf2 e1 
                        (extrExpTJofFun1 fenv tenv e0 e1 y m k ftenv k2))
                                          (*extrExpTJofFun1 f e1 k)*)
               end) (FC fenv tenv e0 e1 y n) k
                    (projT1 (extrLFunTJofFun10 fenv tenv e0 e1 y n k))
                    (y, ft)
    in mkNamedDef (Id2ident y) (Gfun cf) FTyp2C (projT1 k)              
  end) k ).








  
  refine (
  (match f return (sigT (fun ft => FunTyping f ft) -> NamedDef) with
   | FC fenv tenv e0 e1 y n => fun k =>
                                 
    let ft := projT1 k in
    let cft := FTyp2C ft in 
    let y_dec := mkglobvar (FTyp2C ft) nil false false in  
    let ctenv := map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv in

(*                            
        map (fun x => (fst x, (Id2ident (fst x),
                               Fun2C (snd x) (extrLFunTJofFun x k)))) fenv in
*)
    let k1 := extrLFunTJofFun fenv tenv e0 e1 y n k in
    let k2 := extrLFunTJofFunX fenv tenv e0 e1 y n k in 
    let ftenv := projT1 k1 in
    let cfenv := mapG2 FunTyping (Fun2C E2C) fenv k1 in
    let cftenv :=
        map (fun x => (Id2ident (fst x), FTyp2C (snd x))) ftenv in
    let cftenv' := (Id2ident y, cft) :: cftenv in

    let cf := (match n return (sigT (fun ft =>
                FunTyping (FC fenv tenv e0 e1 y n) ft) -> function) with
               | 0 => fun k =>

                        mkfunction cft cc_default ctenv cftenv 
                        (lstat2stat (E2C CS cfenv ftenv tenv fenv k2 e0
                               (extrExpTJofFun0 fenv tenv e0 e1 y k ftenv k2)))
               | S m => fun k =>
                                                    
                         let ftenv' := (* projT1 (extrLFunTJofFun1
                                                 fenv tenv e0 e1 y m k) in *)  
                                       (y, ft)::ftenv in 
                         let fenv' := (y, FC fenv tenv e0 e1 y m)::fenv in
                (* let kf1 := extrLFunTJofFun1 fenv tenv e0 e1 y m k in *)
                         let kf2 := extrLFunTJofFun1Y fenv tenv e0 e1 y m k in
                mkfunction cft cc_default ctenv cftenv' 
                       (lstat2stat (E2C CS cfenv ftenv' tenv fenv' kf2 e1 
                        (extrExpTJofFun1 fenv tenv e0 e1 y m k ftenv k2)))
                                          (*extrExpTJofFun1 f e1 k)*)
              end) k
    in mkNamedDef (Id2ident y) (Gfun cf) FTyp2C (projT1 k)              
  end) k ).














  
  refine (
  (match f return (sigT (fun ft => FunTyping f ft) -> NamedDef) with
   | FC fenv tenv e0 e1 y n => fun k =>
(*                                 
    let ft := projT1 k in
    let cft := FTyp2C ft in 
    let y_dec := mkglobvar (FTyp2C ft) nil false false in  
    let ctenv := map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv in
*)
(*                            
        map (fun x => (fst x, (Id2ident (fst x),
                               Fun2C (snd x) (extrLFunTJofFun x k)))) fenv in
*)
(*    let k1 := extrLFunTJofFun fenv tenv e0 e1 y n k in
    let ftenv := projT1 k1 in
    let k2 := extrLFunTJofFunX fenv tenv e0 e1 y n k in 
    let cfenv := mapG2 FunTyping (Fun2C E2C) fenv k1 in
    let cftenv :=
        map (fun x => (Id2ident (fst x), FTyp2C (snd x))) ftenv in
    let cftenv' := (Id2ident y, cft) :: cftenv in
*)    
    let cf := (match n return (sigT (fun ft => FunTyping (FC fenv tenv e0 e1 y n) ft) -> function) with
               | 0 => fun k =>

    let ft := projT1 k in
    let cft := FTyp2C ft in 
    let y_dec := mkglobvar (FTyp2C ft) nil false false in  
    let ctenv := map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv in

    let k1 := extrLFunTJofFun fenv tenv e0 e1 y 0 k in
    let ftenv := projT1 k1 in
    let k2 := extrLFunTJofFunX fenv tenv e0 e1 y 0 k in 
    let cfenv := mapG2 FunTyping (Fun2C E2C) fenv k1 in
    let cftenv :=
        map (fun x => (Id2ident (fst x), FTyp2C (snd x))) ftenv in

                        mkfunction cft cc_default ctenv cftenv 
                        (lstat2stat (E2C CS cfenv ftenv tenv fenv k2 e0
                               (extrExpTJofFun0 fenv tenv e0 e1 y k ftenv k2)))
               | S m => fun k =>
                          
    let ft := projT1 k in
    let cft := FTyp2C ft in 
    let y_dec := mkglobvar (FTyp2C ft) nil false false in  
    let ctenv := map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv in

    let k1 := extrLFunTJofFun fenv tenv e0 e1 y (S m) k in
    let ftenv := projT1 k1 in
    let k2 := extrLFunTJofFunX fenv tenv e0 e1 y (S m) k in 
    let cfenv := mapG2 FunTyping (Fun2C E2C) fenv k1 in
    let cftenv :=
        map (fun x => (Id2ident (fst x), FTyp2C (snd x))) ftenv in
    let cftenv' := (Id2ident y, cft) :: cftenv in
                          
                         let ftenv' := (* projT1 (extrLFunTJofFun1
                                                 fenv tenv e0 e1 y m k) in *) 
                                       (y, ft)::ftenv in 
                         let fenv' := (y, FC fenv tenv e0 e1 y m)::fenv in
                         let kf := extrLFunTJofFun1Y fenv tenv e0 e1 y m k in
                mkfunction cft cc_default ctenv cftenv' 
                             (E2C CS cfenv ftenv' tenv fenv' kf e1 
                        (extrExpTJofFunA1 fenv tenv e0 e1 y m k ftenv ft k2))
                                          (*extrExpTJofFun1 f e1 k)*)
              end) k
    in mkNamedDef (Id2ident y) (Gfun cf) FTyp2C (projT1 k)              
  end) k ).



  



  
  refine (
  (match f return (sigT (fun ft => FunTyping f ft) -> NamedDef) with
  | FC fenv tenv e0 e1 y n => fun k => 
    let ft := projT1 k in
    let k1 := extrLFunTJofFun fenv tenv e0 e1 y n k in
    let ftenv := projT1 k1 in
    let k2 := extrLFunTJofFunX fenv tenv e0 e1 y n k in 
    let cfenv := (* map (fun x => (fst x, (Id2ident (fst x), snd x)))
                     ( *) mapG2 FunTyping (Fun2C E2C) fenv k1 in
(*                            
        map (fun x => (fst x, (Id2ident (fst x),
                               Fun2C (snd x) (extrLFunTJofFun x k)))) fenv in
*)
    let cft := FTyp2C ft in 
    let y_dec := mkglobvar (FTyp2C ft) nil false false in  
(*    let cfenv' := (y, Gvar y_dec) :: cfenv in *)
    let cftenv :=
        map (fun x => (Id2ident (fst x), FTyp2C (snd x))) ftenv in
    let cftenv' := (Id2ident y, cft) :: cftenv in 
    let ctenv := map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv in
    let cf := (match n return (sigT (fun ft => FunTyping (FC fenv tenv e0 e1 y n) ft) -> function) with
              | 0 => fun k => mkfunction cft cc_default ctenv cftenv 
                        (lstat2stat (E2C CS cfenv ftenv tenv fenv k2 e0
                               (extrExpTJofFun0 fenv tenv e0 e1 y k ftenv k2)))
              | S m => fun k =>
                         let ftenv' := (* projT1 (extrLFunTJofFun1
                                                 fenv tenv e0 e1 y m k) in *) 
                                       (y, ft)::ftenv in 
                         let fenv' := (y, FC fenv tenv e0 e1 y m)::fenv in
                         let kf := extrLFunTJofFun1Y fenv tenv e0 e1 y m k in
                mkfunction cft cc_default ctenv cftenv' 
                             (E2C CS cfenv ftenv' tenv fenv' kf e1 
                        (extrExpTJofFun1 fenv tenv e0 e1 y m k ftenv k2))
                                          (*extrExpTJofFun1 f e1 k)*)
              end) k
    in mkNamedDef (Id2ident y) (Gfun cf) FTyp2C (projT1 k)              
  end) k ).




Fixpoint Fun2C (f: Fun)
         (*k0: sigT (fun ft => FunTyping f ft)*)
         (Exp2C : forall (h: CTag) (ls: genEnv Id NamedDef)                 
                         (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                         (k0: FEnvTyping fenv ftenv)
                         (e: Exp) 
                         (k: sigT (fun t => ExpTyping ftenv tenv fenv e t)),
             LStat h)

         (Fun2C' : forall (f: Fun)
                          (k: sigT (fun ft => FunTyping f ft)), NamedDef)
   
         (k: forall f0: Fun, sigT (fun ft => FunTyping f0 ft))

         
  : function :=
(*  
  let ft := projT1 k in
  let cft := FTyp2C ft in 
  let y_dec := mkglobvar cft nil false false in  
*)
  match f with
  | FC fenv tenv e0 e1 y n =>
    let Acft := fun f0 E k => FTyp2C (projT1 k) in 
    let Ay_dec := fun f0 E k => mkglobvar (Acft f0 E k) nil false false in  
    let Ak1 := fun f0 E => extrLFunTJofFun fenv tenv e0 e1 y n in
    let Ak2 := fun f0 E => extrLFunTJofFunX fenv tenv e0 e1 y n in 
    let Aftenv := fun f0 E k => projT1 (Ak1 f0 E k) in
    let Acfenv := fun f0 E k =>
                    (* map (fun x => (fst x, (Id2ident (fst x), snd x)))
                     ( *) mapG2 FunTyping Fun2C' fenv (Ak1 f0 E k) in
    let Acftenv := fun f0 E k => 
        map (fun x => (Id2ident (fst x), FTyp2C (snd x))) (Aftenv f0 E k) in
    let Acftenv' := fun f0 E k => (Id2ident y, Acft f0 E k) ::
                                                 (Acftenv f0 E k) in 
    let ctenv := fun f0 =>
                   map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv in
(*    let Acfenv' := fun k : sigT (fun ft => FunTyping f ft) => 
                     (y, (Id2ident y, Gvar (Ay_dec k))) :: (Acfenv k) in *)
    match n return (forall f0, f0 = f ->
              sigT (fun ft => FunTyping f0 ft) -> function) with
    | 0 => fun f0 E k => mkfunction (Acft f0 E k)
                                    cc_default ctenv (Acftenv k) 
                                    (Exp2C CS (Acfenv f0 E k) (Aftenv f0 E k)
                                           tenv fenv (Ak2 f0 E k) e0
                           (extrExpTJofFun0 fenv tenv e0 e1 y k
                                            (Aftenv f0 E k) (Ak2 f0 E k)))
    | S n => let Aftenv' := fun f0 E k => (y, projT1 k):: (Aftenv f0 E k) in
                 let fenv' := fun f0 E => (y, FC fenv tenv e0 e1 y n)::fenv in 
                 fun f0 E k => mkfunction (Acft f0 E k) cc_default ctenv
                     (Acftenv' f0 E k) 
                     (Exp2C CS (Acfenv f0 E k)
                        (Aftenv' f0 E k) tenv fenv' FEnvNull e1 
                        (extrExpTJofFun1 fenv tenv e0 e1 y n k
                                (Aftenv f0 E k) (Ak2 f0 E k)))
                                          (*extrExpTJofFun1 f e1 k)*)
    end   
  end.




Fixpoint Fun2C (f: Fun)
         (*k0: sigT (fun ft => FunTyping f ft)*)

         (Exp2C : forall (h: CTag) (ls: genEnv Id NamedDef)
           (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
           (k0: FEnvTyping fenv ftenv)
           (e: Exp) 
           (k: sigT (fun t => ExpTyping ftenv tenv fenv e t)), LStat h)

         (Fun2C' : forall (f: Fun)
                  (k: sigT (fun ft => FunTyping f ft)), NamedDef) :
   
  forall f0: Fun, f0 = f ->
                  sigT (fun ft => FunTyping f0 ft) -> function :=
(*  
  let ft := projT1 k in
  let cft := FTyp2C ft in 
  let y_dec := mkglobvar cft nil false false in  
*)
  match f with
  | FC fenv tenv e0 e1 y n =>
    let Acft := fun f0 E k => FTyp2C (projT1 k) in 
    let Ay_dec := fun f0 E k => mkglobvar (Acft f0 E k) nil false false in  
    let Ak1 := fun f0 E => extrLFunTJofFun fenv tenv e0 e1 y n in
    let Ak2 := fun f0 E => extrLFunTJofFunX fenv tenv e0 e1 y n in 
    let Aftenv := fun f0 E k => projT1 (Ak1 f0 E k) in
    let Acfenv := fun f0 E k =>
                    (* map (fun x => (fst x, (Id2ident (fst x), snd x)))
                     ( *) mapG2 FunTyping Fun2C' fenv (Ak1 f0 E k) in
    let Acftenv := fun f0 E k => 
        map (fun x => (Id2ident (fst x), FTyp2C (snd x))) (Aftenv f0 E k) in
    let Acftenv' := fun f0 E k => (Id2ident y, Acft f0 E k) ::
                                                 (Acftenv f0 E k) in 
    let ctenv := fun f0 =>
                   map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv in
(*    let Acfenv' := fun k : sigT (fun ft => FunTyping f ft) => 
                     (y, (Id2ident y, Gvar (Ay_dec k))) :: (Acfenv k) in *)
    match n return (forall f0, f0 = f ->
              sigT (fun ft => FunTyping f0 ft) -> function) with
    | 0 => fun f0 E k => mkfunction (Acft f0 E k)
                                    cc_default ctenv (Acftenv k) 
                                    (Exp2C CS (Acfenv f0 E k) (Aftenv f0 E k)
                                           tenv fenv (Ak2 f0 E k) e0
                           (extrExpTJofFun0 fenv tenv e0 e1 y k
                                            (Aftenv f0 E k) (Ak2 f0 E k)))
    | S n => let Aftenv' := fun f0 E k => (y, projT1 k):: (Aftenv f0 E k) in
                 let fenv' := fun f0 E => (y, FC fenv tenv e0 e1 y n)::fenv in 
                 fun f0 E k => mkfunction (Acft f0 E k) cc_default ctenv
                     (Acftenv' f0 E k) 
                     (Exp2C CS (Acfenv f0 E k)
                        (Aftenv' f0 E k) tenv fenv' FEnvNull e1 
                        (extrExpTJofFun1 fenv tenv e0 e1 y n k
                                (Aftenv f0 E k) (Ak2 f0 E k)))
                                          (*extrExpTJofFun1 f e1 k)*)
    end   
  end.




  
  match f with
  | FC fenv tenv e0 e1 y n =>
    let Acft := fun k => FTyp2C (projT1 k) in 
    let Ay_dec := fun k => mkglobvar (Acft k) nil false false in  
    let Ak1 := extrLFunTJofFun fenv tenv e0 e1 y n in
    let Ak2 := extrLFunTJofFunX fenv tenv e0 e1 y n in 
    let Aftenv := fun k => projT1 (Ak1 k) in
    let Acfenv := fun k => map (fun x => (fst x, (Id2ident (fst x), snd x)))
                     (mapG2 FunTyping Fun2C' fenv (Ak1 k)) in
    let Acftenv := fun k => 
        map (fun x => (Id2ident (fst x), FTyp2C (snd x))) (Aftenv k) in
    let Acftenv' := fun k => (Id2ident y, Acft k) :: (Acftenv k) in 
    let ctenv := map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv in
(*    let Acfenv' := fun k : sigT (fun ft => FunTyping f ft) => 
                     (y, (Id2ident y, Gvar (Ay_dec k))) :: (Acfenv k) in *)
    match n with
        | 0 => fun k => mkfunction (Acft k) cc_default ctenv (Acftenv k) 
                    (Exp2C CS (Acfenv k) (Aftenv k) tenv fenv (Ak2 k) e0
                           (extrExpTJofFun0 fenv tenv e0 e1 y k
                                            (Aftenv k) (Ak2 k)))
        | S n => let Aftenv' := fun k => (y, projT1 k):: (Aftenv k) in
                 let fenv' := (y, FC fenv tenv e0 e1 y n)::fenv in 
            fun k => mkfunction (Acft k) cc_default ctenv (Acftenv' k) 
                     (Exp2C CS (Acfenv k) (Aftenv' k) tenv fenv' FEnvNull e1 
                (extrExpTJofFun1 fenv tenv e0 e1 y n k (Aftenv k) (Ak2 k)))
                                          (*extrExpTJofFun1 f e1 k)*)
    end   
  end.



Fixpoint Fun2C (f: Fun)
         (k: sigT (fun ft => FunTyping f ft)) :
                  sigT (fun ft => FunTyping f ft) -> NamedDef :=
(*  
  let ft := projT1 k in
  let cft := FTyp2C ft in 
  let y_dec := mkglobvar cft nil false false in  
*)
  match f with
  | FC fenv tenv e0 e1 y n =>
    let Acft := fun k => FTyp2C (ft k) in 
    let Ay_dec := fun k => mkglobvar (Acft k) nil false false in  
    let Ak1 := extrLFunTJofFun fenv tenv e0 e1 y n in
    let Ak2 := extrLFunTJofFunX fenv tenv e0 e1 y n in 
    let Aftenv := fun k => projT1 (Ak1 k) in
    let Acfenv := fun k => map (fun x => (fst x, (Id2ident (fst x), snd x)))
                     (mapG2 FunTyping Fun2C fenv (Ak1 k)) in
(*                            
        map (fun x => (fst x, (Id2ident (fst x),
                               Fun2C (snd x) (extrLFunTJofFun x k)))) fenv in
*)
    let Acfenv' := fun k =>
                     (y, (Id2ident y, Gvar (Ay_dec k))) :: (Acfenv k) in
    let cftenv :=
        map (fun x => (Id2ident (fst x), FTyp2C (snd x))) ftenv in
    let Acftenv' := fun k => (Id2ident y, Acft k) :: cftenv in 
    let ctenv := map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv in
    let cf := match n with
        | 0 => fun k => mkfunction (Acft k) cc_default ctenv (Acftenv k) 
                    (Exp2C CS (Acfenv k) (Aftenv k) tenv fenv (Ak2 k) e0
                        (extrExpTJofFun0 fenv tenv e0 e1 y k ftenv (Ak2 k)))
        | S n => let Aftenv' := fun k => (y, projT1 k):: (Aftenv k) in
                 let fenv' := (y, FC fenv tenv e0 e1 y n)::fenv in 
            fun k => mkfunction (Acft k) cc_default ctenv (Acftenv' k) 
                     (Exp2C CS (Acfenv' k) (Aftenv' k) tenv fenv' FEnvNull e1 
                        (extrExpTJofFun1 fenv tenv e0 e1 y n k ftenv k2))
                                          (*extrExpTJofFun1 f e1 k)*)
              end
    in mkNamedDef (Id2ident y) (Gfun cf) FTyp2C ft              
  end

    
(*** here is the original ***)

Fixpoint Fun2C (f: Fun)
           (k: sigT (fun ft => FunTyping f ft)) : NamedDef :=
  match f with
  | FC fenv tenv e0 e1 y n =>
    let ft := projT1 k in
    let k1 := extrLFunTJofFun fenv tenv e0 e1 y n k in
    let ftenv := projT1 k1 in
    let k2 := extrLFunTJofFunX fenv tenv e0 e1 y n k in 
    let cfenv := map (fun x => (fst x, (Id2ident (fst x), snd x)))
                     (mapG2 FunTyping Fun2C fenv k1) in
(*                            
        map (fun x => (fst x, (Id2ident (fst x),
                               Fun2C (snd x) (extrLFunTJofFun x k)))) fenv in
*)
    let cft := FTyp2C ft in 
    let y_dec := mkglobvar (FTyp2C ft) nil false false in  
    let cfenv' := (y, (Id2ident y, Gvar y_dec)) :: cfenv in
    let cftenv :=
        map (fun x => (Id2ident (fst x), FTyp2C (snd x))) ftenv in
    let cftenv' := (Id2ident y, cft) :: cftenv in 
    let ctenv := map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv in
    let cf := match n with
              | 0 => mkfunction cft cc_default ctenv cftenv 
                        (Exp2C CS cfenv ftenv tenv fenv k2 e0
                               (extrExpTJofFun0 fenv tenv e0 e1 y k ftenv k2))
              | S n => let ftenv' := (y, ft)::ftenv in
                       let fenv' := (y, FC fenv tenv e0 e1 y n)::fenv in 
                mkfunction cft cc_default ctenv cftenv' 
                             (Exp2C CS cfenv' ftenv' tenv fenv' FEnvNull e1 
                        (extrExpTJofFun1 fenv tenv e0 e1 y n k ftenv k2))
                                          (*extrExpTJofFun1 f e1 k)*)
              end
    in mkNamedDef (Id2ident y) (Gfun cf) FTyp2C (projT1 k)              
  end
with Prms2C (ls: genEnv Id NamedDef)
             (ftenv: funTC) (tenv: valTC) (fenv: funEnv) 
             (k0: FEnvTyping fenv ftenv)
             (ps: Prms) 
             (k: sigT (fun pt => PrmsTyping ftenv tenv fenv ps pt))
         : list (LStat CE) :=
  match ps with
  | PS es =>
    mapF2 (ExpTyping ftenv tenv fenv) (Exp2C CE ls ftenv tenv fenv k0)
         es (extrExpTJofPS ftenv tenv fenv es k)
  end        
with Exp2C (h: CTag) (ls: genEnv Id NamedDef)
           (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
           (k0: FEnvTyping fenv ftenv)
           (e: Exp) 
           (k: sigT (fun t => ExpTyping ftenv tenv fenv e t)) : LStat CE :=
  match e with
  | Modify TI TO VTI VTO XF q =>
    let f := Effect2C TI TO VTI VTO XF ls q in LE f          
  | Return z q =>
    QVal2C CE tenv q (extrQValTJofRet ftenv tenv fenv z q k)
  | BindN e1 e2 =>
    let c1 := (Exp2C CE ls ftenv tenv fenv k0 e1
                     (extrExpTJofBindN1 ftenv tenv fenv e1 e2 k)) in
    let c2 := (Exp2C CE ls ftenv tenv fenv k0 e2
                     (extrExpTJofBindN2 ftenv tenv fenv e1 e2 k)) in   
    match_Ecomma c1 c2    
  | BindS x e1 e2 =>
    let k1 := extrExpTJofBindS1 ftenv tenv fenv x e1 e2 k in
    let c1 := (Exp2C CE ls ftenv tenv fenv k0 e1 k1) in
    let tenv' := (x, projT1 k1) :: tenv in
    Exp2C CE ((x, (Id2ident x, mkNamedDef x c1))::ls) ftenv tenv' fenv k0 e2 
          (extrExpTJofBindS2 ftenv tenv fenv k0 x e1 e2
                (projT1 k1) (projT2 k1))
  | BindMS fenv venv e => SUndef CE 
  | Apply q ps =>
    let cs := Prms2C ls ftenv tenv fenv ps
                     (extrPrmsTJofApply ftenv tenv fenv q ps k) in 
    match q with 
    | QF f => let x := getFunName f in
              let g := Fun2C f (extrFunTJofApply f k) in
              FPack (x, (Id2ident x, g)) (match_Ecall h g cs)  
    | FVar x => match_Ecall h (findE ls x) cs
    end
  | Val v => Val2C h v    
  | IfThenElse e1 e2 e3 =>
    let c1 := Exp2C CE ls ftenv tenv fenv e1
                    (extrExpTJofIF1 ftenv tenv fenv e1 k) in
    let c2 := Exp2C h ls ftenv tenv fenv e2
                    (extrExpTJofIF2 ftenv tenv fenv e2 k) in
    let c3 := Exp2C h ls ftenv tenv fenv e3
                    (extrExpTJofIF3 ftenv tenv fenv e3 k) in 
    match h with
    | CE => match_Econdition c1 c2 c3
    | CS => match_Sifthenelse c1 c2 c3                     
    end
  end.







with Fun2C (f: Fun)
           (k: sigT (fun ft => FunTyping f ft)) : NamedDef :=
  match f with
  | FC fenv tenv e0 e1 y n =>
    let cfenv :=
        map (fun x => (fst x, (Id2ident (fst x),
                               Fun2C nil (snd x) (extrTypFEnv x k)))) fenv in
    let y_dec := mkglobvar (FTyp2C ft) nil false false in  
    let cfenv' := (y, (Id2ident y, Gvar y_dec)) :: cfenv in
    let cftenv :=
        map (fun x => (Id2ident (fst x), FTyp2C (snd x)))
            (computeFTenv fenv) in
    let cftenv' := (Id2ident y, FTyp2C (computeFTyp f)) :: cftenv in 
    let ctenv := map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv in
    let cf := match n with
              | 0 => mkfunction (computeFTyp f) cc_default ctenv cftenv 
                                  (Exp2C CS cfenv nil tenv nil e0
                                        (extrTypFun0 e0 k))
              | S _ => mkfunction (computeFTyp f) cc_default ctenv cftenv' 
                                    (Exp2C CS cfenv' nil tenv nil e1 
                                          (extrTypFun1 e1 k))
              end
    in mkNamedDef (Id2ident y) (Gfun cf) FTyp2C (computeFTyp f)              
  end.



  (*  match ps with
  | PS es =>   
    match k with
    | existT t k1 =>
      match k1 with
      | PS_Typing ftenv' tenv' fenv' es ts k2 =>
        match k2 =>
        | Forall2_nilT
        | Forall2_consT e t es' ts' k3 ks =>     
        
    let ls := map (fun e => (e, extrExpTJofPS ftenv tenv fenv es k e)) es in
    map2 (Exp2C CE ls ftenv tenv fenv k0) ls
*) 
(*
         map (fun e => (e, Exp2C CE ls ftenv tenv fenv k0 e
                             (extrExpTJofPS ftenv tenv fenv es k e))) es
*)


with Prms2C (ls: genEnv Id NamedDef)
             (ftenv: funTC) (tenv: valTC) (fenv: funEnv) 
             (k0: FEnvTyping fenv ftenv)
             (ps: Prms) 
             (k: sigT (fun pt => PrmsTyping ftenv tenv fenv ps pt))
         : list (LStat CE) :=
  match ps with
  | PS es => map (fun e => Exp2C CE ls ftenv tenv fenv k0 e
                                 (extrTypPS ftenv tenv fenv ps k e)) es
  end.


(************************************************************************)




                                            
Fixpoint Effect2C (TI TO: Type) (VTI: ValTyp TI) (VTO: ValTyp TO)
                   (XF: XFun TI TO)
                   (ls: genEnv Id NamedDef) (q: QValue) : expr :=
  match (type2C TI) with
  | Tvoid => let w := effectTable TI TO XF in Evar (gId w) (gType w)
  | _     => let w := effectTable TI TO XF in  
             Ecall (Evar (gId w) (gType w))
                   (listLStatCE2exprlist
                     (Prms2C ls nil nil nil FEnvNull (PS [Val (cst TI q)])
                             (extrPrmsTJofQV TI VTI q)))
                   (gType w)                
  end
with Exp2C (h: CTag) (ls: genEnv Id NamedDef)
           (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
           (k0: FEnvTyping fenv ftenv)
           (e: Exp) 
           (k: sigT (fun t => ExpTyping ftenv tenv fenv e t)) : LStat h :=
  match e with
  | Modify TI TO VTI VTO XF q =>
    let f := Effect2C TI TO VTI VTO XF ls q in       
    match h with
    | CE => LE f
    | CS => match_Sreturn (type2C TO) f
    end            
  | Return _ q =>
    LE (match q with
             | Val v => Val2C v h
             | QF x  => Evar (Id2ident x) (VTyp2C (projT1 k))
        end) 
  | BindN e1 e2 =>
    let c1 := (Exp2C h ls ftenv tenv fenv k0 e1
                     (extrExpTJofBindN1 ftenv tenv fenv e1 e2 k)) in
    let c2 := (Exp2C h ls ftenv tenv fenv k0 e2
                     (extrExpTJofBindN2 ftenv tenv fenv e1 e2 k)) in   
    match h with
    | CE => match_Ecomma c1 c2  
    | CS => match_Sseq c1 c2  
    end
  | BindS x e1 e2 =>
    let k1 := extrExpTJofBindS1 ftenv tenv fenv x e1 e2 k in
    let c1 := (Exp2C CE ls ftenv tenv fenv k0 e1 k1) in
    let tenv' := (x, projT1 k1) :: tenv in
    Exp2C h ((x, (Id2ident x, mkNamedDef x c1))::ls) ftenv tenv' fenv k0 e2 
          (extrExpTJofBindS2 ftenv tenv fenv k0 x e1 e2
                (projT1 k1) (projT2 k1))
  | BindMS fenv venv e => SUndef h 
  | Apply q ps =>
    let cs := Prms2C ls ftenv tenv fenv ps
                     (extrPrmsTJofApply ftenv tenv fenv q ps k) in 
    match q with 
    | QF f => let x := getFunName f in
              let g := Fun2C f (extrFunTJofApply f k) in
              FPack (x, (Id2ident x, g)) (match_Ecall h g cs)  
    | FVar x => match_Ecall h (findE ls x) cs
    end                  
  | IfThenElse e1 e2 e3 =>
    let c1 := Exp2C CE ls ftenv tenv fenv e1
                    (extrExpTJofIF1 ftenv tenv fenv e1 k) in
    let c2 := Exp2C h ls ftenv tenv fenv e2
                    (extrExpTJofIF2 ftenv tenv fenv e2 k) in
    let c3 := Exp2C h ls ftenv tenv fenv e3
                    (extrExpTJofIF3 ftenv tenv fenv e3 k) in 
    match h with
    | CE => match_Econdition c1 c2 c3
    | CS => match_Sifthenelse c1 c2 c3                     
    end
  end                                                  
with Fun2C (f: Fun)
           (k: sigT (fun ft => FunTyping f ft)) : NamedDef :=
  match f with
  | FC fenv tenv e0 e1 y n =>
    let cfenv :=
        map (fun x => (fst x, (Id2ident (fst x),
                               Fun2C nil (snd x) (extrTypFEnv x k)))) fenv in
    let y_dec := mkglobvar (FTyp2C ft) nil false false in  
    let cfenv' := (y, (Id2ident y, Gvar y_dec)) :: cfenv in
    let cftenv :=
        map (fun x => (Id2ident (fst x), FTyp2C (snd x)))
            (computeFTenv fenv) in
    let cftenv' := (Id2ident y, FTyp2C (computeFTyp f)) :: cftenv in 
    let ctenv := map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv in
    let cf := match n with
              | 0 => mkfunction (computeFTyp f) cc_default ctenv cftenv 
                                  (Exp2C CS cfenv nil tenv nil e0
                                        (extrTypFun0 e0 k))
              | S _ => mkfunction (computeFTyp f) cc_default ctenv cftenv' 
                                    (Exp2C CS cfenv' nil tenv nil e1 
                                          (extrTypFun1 e1 k))
              end
    in mkNamedDef (Id2ident y) (Gfun cf) FTyp2C (computeFTyp f)              
  end     
with Prms2C (ls: genEnv Id NamedDef)
             (ftenv: funTC) (tenv: valTC) (fenv: funEnv) 
             (k0: FEnvTyping fenv ftenv)
             (ps: Prms) 
             (k: sigT (fun pt => PrmsTyping ftenv tenv fenv ps pt))
         : list (LStat CE) :=
  match ps with
  | PS es => map (fun e => Exp2C CE ls ftenv tenv fenv k0 e
                                 (extrTypPS ftenv tenv fenv ps k e)) es
  end.


(************************************************************************)


Fixpoint Effect2C (TI TO: Type) (VTI: ValTyp TI) (VTO: ValTyp TO)
                   (XF: XFun TI TO)
                   (ls: genEnv Id NamedDef) (q: TI) :
    expr :=
  match (type2C TI) with
  | Tvoid => let w := effectTable TI TO XF in Evar (gId w) (gType w)
  | _     => let w := effectTable TI TO XF in  
             Ecall (Evar (gId w) (gType w))
                   (listLStatCE2exprlist
                     (Prms2C ls nil nil nil (PS [Val (cst TI q)])
                             (extrPrmsTJ4QV TI VTI q)))
                   (gType w)                
  end
with Exp2C (h: CTag) (ls: genEnv Id NamedDef)
            (ftenv: funTC) (tenv: valTC) (fenv: funEnv) 
            (e: Exp) 
            (k: sigT (fun t => ExpTyping ftenv tenv fenv e t)) : LStat h :=
  match e with
  | Modify TI TO VTI VTO XF q =>
    let f := Effect2C TI TO VTI VTO XF ls q in       
    match t with
    | CE => LE f
    | CS => match_Sreturn (VTyp2C TO) f
    end            
  | Lift _ q =>
    LE (match q with
             | Val v => Val2C v t
             | QF x  => Id2C x t
        end) 
  | BindN e1 e2 =>
    let c1 := (Exp2C h ls ftenv tenv fenv e1
                     (extrTypBindN1 ftenv tenv fenv e1 k)) in
    let c2 := (Exp2C h ls ftenv tenv fenv e2
                     (extrTypBindN2 ftenv tenv fenv e2 k)) in   
    match h with
    | CE => match_EComma c1 c2  
    | CS => match_Sseq c1 c2  
    end
  | BindS x e1 e2 =>
    let c1 := (Exp2C CE ls ftenv tenv fenv e1
                     (extrTypBindS1 ftenv tenv fenv e1 k)) in
    Exp2C h ((x, (Id2ident x, mkNamedDef x c1))::ls) ftenv tenv fenv e2 t
                     (extrTypBindS2 ftenv tenv fenv x e1 e2 k)
  | BindMS fenv venv e => SUndef h 
  | Apply q ps =>
    let cs := Prms2C ls ftenv tenv fenv ps
                     (extrPTypFT ftenv tenv fenv ps k) in 
    match q with 
    | QF f => let x := getFunName f in
              let g := Fun2C f (extrFTypApply f k) in
              FPack (x, (Id2ident x, g)) (match_Ecall h g cs)  
    | FVar x => match_Ecall h (findE ls x) cs
    end                  
  | IfThenElse e1 e2 e3 =>
    let c1 := Exp2C CE ls ftenv tenv fenv e1
                    (extrTypITE1 ttenv tenv fenv e1 k) in
    let c2 := Exp2C h ls ftenv tenv fenv e2
                    (extrTypITE2 ttenv tenv fenv e2 k) in
    let c3 := Exp2C h ls ftenv tenv fenv e3
                    (extrTypITE3 ttenv tenv fenv e3 k) in 
    match t with
    | CE => match_Econdition c1 c2 c3
    | CS => match_Sifthenelse c1 c2 c3                     
    end
  end                                                  
with Fun2C (f: Fun)
           (k: sigT (fun ft => FunTyping f ft)) : NamedDef :=
  match f with
  | FC fenv tenv e0 e1 y n =>
    let cfenv :=
        map (fun x => (fst x, (Id2ident (fst x),
                               Fun2C nil (snd x) (extrTypFEnv x k)))) fenv in
    let y_dec := mkglobvar (FTyp2C ft) nil false false in  
    let cfenv' := (y, (Id2ident y, Gvar y_dec)) :: cfenv in
    let cftenv :=
        map (fun x => (Id2ident (fst x), FTyp2C (snd x)))
            (computeFTenv fenv) in
    let cftenv' := (Id2ident y, FTyp2C (computeFTyp f)) :: cftenv in 
    let ctenv := map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv in
    let cf := match n with
              | 0 => mkfunction (computeFTyp f) cc_default ctenv cftenv 
                                  (Exp2C CS cfenv nil tenv nil e0
                                        (extrTypFun0 e0 k))
              | S _ => mkfunction (computeFTyp f) cc_default ctenv cftenv' 
                                    (Exp2C CS cfenv' nil tenv nil e1 
                                          (extrTypFun1 e1 k))
              end
    in mkNamedDef (Id2ident y) (Gfun cf) FTyp2C (computeFTyp f)              
  end     
with Prms2C (ls: genEnv Id NamedDef)
             (ftenv: funTC) (tenv: valTC) (fenv: funEnv) 
             (ps: Prms) 
             (k: sigT (fun pt => PrmsTyping ftenv tenv fenv ps pt))
         : list (LStat CE) :=
  match ps with
  | PS es => map (fun e => Exp2C CE ls ftenv tenv fenv e
                                 (extrTypPS ftenv tenv fenv ps k e)) es
  end.


















(****************************************************************)



Fixpoint Effect2C (TI TO: Type) (XF: XFun TI TO)
                   (ls: genEnv Id namedDef) (q: TI) :
    CCert.expr :=
  match ti@(VTyp2C TI) with
  | Tvoid => let w := effectTable TI TO XF in EVar (gDef w) (gTyp w)
  | _     => let w := effectTable TI TO XF in  
        Ecall (gDef w) (Prms2C ls (PS [QV q])) (VTyp2C TO)) (* gTyp w *)                
  end
with Exp2C (t: CTag) (ls: genEnv Id namedDef) (e: Exp) : LStat t :=
  match e with
  | Modify TI TO VTI VTO XF q =>
    let f := Effect2C TI TO XF ls q in       
    match t with
    | CE => LE f
    | CS => match_returnCall (VTyp2C TO) f
(*      match (VTyp2C TO) with
            | Tvoid => LS (Sdo f)
            | _ => LS (Sreturn f)              
            end
*)
    end            
  | Lift _ q =>
    let f := match q with
             | Val v => Val2C v
             | QF x  => Id2C x
             end in
    match t with
    | CE => LE f
    | CS => LS (Sreturn f)
    end             
  | BindN e1 e2 =>
    let c1 := (Exp2C t ls e1) in
    let c2 :=  (Exp2C t ls e2) in   
    match t with
    | CE => E_match_And c1 c2  
    | CS => S_match_Seq c1 c2  
    end
  | BindS x e1 e2 => SPack (x, Id2ident x, Exp2C CE ls e1)   
                           (Exp2C t ls e2)
  | BindMS fenv venv e => SUndef t 
  | Apply q ps =>
    let cs := Prms2C ls p in 
    match q with 
    | QF f => let x := getFunName f in
              let g := Fun2C ls f in
              FPack (x, Id2ident x, g) (match_Call t g cs)  
    | FVar x => match_Call t (findE ls x) cs
    end                  
  | IfThenElse e1 e2 e3 =>
    let c1 := Exp2C CE ls e1 in
    let c2 := Exp2C t ls e2 in
    let c3 := Exp2C t ls e3 in 
    match t with
    | CE => E_match_Cond c1 c2 c3
    | CS => S_match_Ifthenelse c1 c2 c3                     
    end
  end                                                  
with Fun2C (ls: genEnv Id namedDef) (f: Fun) : namedDef :=
  match f with
  | FC fenv tenv e0 e1 y n =>
    let cfenv :=
        map (fun x => (fst x, (Id2ident (fst x), Fun2C nil (snd x)))) fenv in
    let cftenv :=
        map (fun x => (Id2ident (fst x), FTyp2C (snd x)))
            (computeFTenv fenv) in
    let cftenv' := (Id2ident y, computeType f) :: cftenv in 
    let ctenv := map (fun x => (Id2ident (fst x), VTyp2C (snd x))) tenv in
    let cf := match n with
              | 0 => mkfunction { computeType f; cc_default; ctenv; cftenv; 
                                  Exp2C CS cfenv ctenv e0 }
              | S _ => mkfunction { computeType f; cc_default; ctenv; cftenv'; 
                                    Exp2C CS cfenv ctenv e1 }
              end
    in { Id2ident y, Gfun cf, computeType f }             
  end     
with Prms2C (ls: genEnv Id namedDef) (ps: Prms) : list (LStat CE) :=
  match ps with
  | PS es => map (Exp2C CE) es
  end.
  
(*
with QFun2C (ls: genEnv Id namedDef) (f: Fun) (b: bool) : LStat b :=
       SUndef b
*)


(*
    let s0 := Exp2C CS cfenv ctenv e0 in
    let s1 := Exp2C CS cfenv ctenv e1 in
    let s2 := Sifthenelse (Ogt n 1) (Ssequence s1
                                    (Sdo (Eassign n (Osub n 1) nat))) 
              Sifthenelse (Oeq n 0) s0      
*)       



with Fun2C (ls: genEnv Id namedDef) (f: Fun) (b: bool) : namedDef :=
  match f with
  | FC fenv tenv e0 e1 x n =>
    let cfenv :=
        map (fun x => (fst x, Id2ident (fst x), Fun2C nil (snd x))) in
    let ctenv := map (fun x => (x, Id2ident (fst x), VTyp2C (snd x))) in
    let s0 := Exp2C CS cfenv ctenv e0 in
    let s1 := Exp2C CS cfenv ctenv e1 in
    let s2 := Sifthenelse (Ogt n 1) (Ssequence s1
                                    (Sdo (Eassign n (Osub n 1) nat))) 
              Sifthenelse (Oeq n 0) s0      
       

with Exp2C (ls: genEnv Id namedDef) (e: Exp) (b: bool) : CCert.statement :=
  match e with
  | Modify TI TO VTI VTO XF q => Effect2C TI TO XF ls q 
  | Lift _ q => match q with
                | Val v => Sreturn (Val2C v)
                | QF x  => Sreturn (Id2C x)
                end                
  | BindN e1 e2 => Ssequence (Exp2C ls e1 false)
                             (Exp2C ls e2 true)
  | BindS x e1 e2 => SPack (x, Id2ident x, Exp2C ls e1 true)   
                           (Sreturn (Exp2C e2))                                   | BindMS fenv venv e => SUndef
                          (* SPack (map IFun2C fenv) (map IVal2C venv)
                                (Sreturn (Exp2C e)) *)                            | Apply q ps =>                                                                   match q with
    | (QF _)   => SUndef
    | (FVar x) => 
      Sreturn (Ecall (findS ls (nameF q)) (Prms2C ps)
    end                  
  | IfThenElse e1 e2 e3 =>  


(********************************************************************)

           
Fixpoint Effect2C (TI TO: Type) (XF: XFun TI TO)
                   (ls: genEnv Id namedDef) (q: TI) :
    CCert.statement :=
  match ti@(VTyp2C TI) with
  | Tvoid => match to@(VTyp2C TO) with 
             | Tvoid =>  Sdo (gDef (effectTable TI TO XF))
             | _     =>  Sreturn (gDef (effectTable TI TO XF))
             end                    
  | _     => match to@(VTyp2C TO) with 
             | Tvoid =>  Sdo (Ecall (gDef (effectTable TI TO XF))
                                    (Prms2C ls (PS [QV q])) (VTyp2C TO))
             | _     =>  Sreturn (Ecall (gDef (effectTable TI TO XF))
                                        (Prms2C ls (PS [QV q])) (VTyp2C TO))
             end                            
  end
with Exp2C (ls: genEnv Id namedDef) (e: Exp) (b: bool) : LStat :=
  match e with
  | Modify TI TO VTI VTO XF q => LS (Effect2C TI TO XF ls q) 
  | Lift _ q => LS (match q with
                    | Val v => Sreturn (Val2C v)
                    | QF x  => Sreturn (Id2C x)
                    end)                
  | BindN e1 e2 => LS_match_Ssequence (Exp2C ls e1 false)
                                      (Exp2C ls e2 true)
  | BindS x e1 e2 => SPack (x, Id2ident x, Exp2C ls e1 true)   
                           (LS_match_Sreturn (Exp2C e2))                          | BindMS fenv venv e => SUndef
                          (* SPack (map IFun2C fenv) (map IVal2C venv)
                                (Sreturn (Exp2C e)) *)                            | Apply q ps =>                                                                     match q with
      | (QF _)   => SUndef
      | (FVar x) => 
          LS_match_Scall (findE ls x) (Prms2C ps)
    end                  
  | IfThenElse e1 e2 e3 => LS_match_Sifthenelse 



with Exp2C (ls: genEnv Id namedDef) (e: Exp) (b: bool) : CCert.statement :=
  match e with
  | Modify TI TO VTI VTO XF q => Effect2C TI TO XF ls q 
  | Lift _ q => match q with
                | Val v => Sreturn (Val2C v)
                | QF x  => Sreturn (Id2C x)
                end                
  | BindN e1 e2 => Ssequence (Exp2C ls e1 false)
                             (Exp2C ls e2 true)
  | BindS x e1 e2 => SPack (x, Id2ident x, Exp2C ls e1 true)   
                           (Sreturn (Exp2C e2))                                   | BindMS fenv venv e => SUndef
                          (* SPack (map IFun2C fenv) (map IVal2C venv)
                                (Sreturn (Exp2C e)) *)                            | Apply q ps =>                                                                   match q with
    | (QF _)   => SUndef
    | (FVar x) => 
      Sreturn (Ecall (findS ls (nameF q)) (Prms2C ps)
    end                  
  | IfThenElse e1 e2 e3 =>  


(********************************************************************)

Definition effectTable (TI TO: Type) (XF: XFun TI TO) : Csyntax.expr.


Fixpoint Effect2C (TI TO: Type) (XF: XFun TI TO) (q: TI) :
    Csyntax.statement :=
  match ti@(VTyp2C TI) with
  | Tvoid => match to@(VTyp2C TO) with 
             | Tvoid =>  Sdo (effectTable TI TO XF)
             | _     =>  Sreturn (effectTable TI TO XF)
             end                    
  | _     => match to@(VTyp2C TO) with 
             | Tvoid =>  Sdo (Ecall (effectTable TI TO XF)
                                    (Prms2C (PS [QV q])) (VTyp2C TO))
             | _     =>  Sreturn (Ecall (effectTable TI TO XF)
                                        (Prms2C (PS [QV q])) (VTyp2C TO))
             end                            
  end
with exp2stmt (b: CCert.statement + CCert.expression) (r: bool) :
       Cert.statement :=
  match b with
  | inl x => x
  | inr x => match r with
             | false => Sdo x
             | true  => Sreturn x               
with Exp2C (e: Exp) : (CCert.statement + CCert.expression) * bool) :=
  match e with
  | Modify TI TO VTI VTO XF q => inl (effect2C TI TO XF q) 
  | Lift _ q => match q with
                | Val v => Val2C v
                | QF x  => Id2C x
                end                
  | BindN e1 e2 => Ssequence (exp2stmt (Exp2C e1) false)
                             (exp2stmt (Exp2C e2) true)
  | BindS x e1 e2 =>
       
       Ssequence (Sassign (Id2C c) (Exp2C e1) (Sreturn (Exp2C e2))                                         


  | BindN e1 e2 => Ssequence (Sdo (Exp2C e1)) (Sreturn (Exp2C e2))
  | BindS x e1 e2 =>
       Ssequence (Sassign (Id2C c) (Exp2C e1) (Sreturn (Exp2C e2))                                         

(*
Inductive Prog : (** Programs *)
       Type := prog (e: Exp)
             | define (x: Id) (f: Fun) (p: Prog).
*)

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
      FunTyping (FC fenv tenv e0 e1 x (QV (cst nat 0))) (FT tenv t)
  | FunS_Typing: forall (ftenv: funTC) (tenv: valTC)
                        (fenv: funEnv) 
            (e0 e1: Exp) (x: Id) (n: nat) (t: VTyp),
      let ftenv' := (x, FT tenv t) :: ftenv in 
      let fenv' := (x, FC fenv tenv e0 e1 x n) :: fenv in 
      MatchEnvsT FunTyping fenv ftenv -> 
      ExpTyping ftenv' tenv fenv' e1 t -> 
      FunTyping (FC fenv tenv e0 e1 x (QV (cst nat n))) (FT tenv t) ->
      FunTyping (FC fenv tenv e0 e1 x (QV (cst nat (S n)))) (FT tenv t)
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
  | Lift_Typing : forall (G: Tag)
                         (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                         (q: QValue) (t: VTyp),
                       QValueTyping tenv q t ->  
                       ExpTyping ftenv tenv fenv (Return G q) t 
  | Seq_Typing : forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                          (e1 e2: Exp) (t1 t2: VTyp), 
                       ExpTyping ftenv tenv fenv e1 t1 ->
                       ExpTyping ftenv tenv fenv e2 t2 ->
                       ExpTyping ftenv tenv fenv (Seq e1 e2) t2
  | BindV_Typing : forall (ftenv: funTC) (tenv: valTC) 
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

(** value typing lemmas from CRelLib *)

Definition ExTDefVal := ExRelValT ValueTyping.

Definition ExTDefValProj1 := ExRelValTProj1 ValueTyping.

Definition updateVEnvLemma := updateEnvLemmaT ValueTyping.

Definition overrideVEnvLemma := overrideEnvLemmaT ValueTyping.

Definition ValTypedByEnv := RelatedByEnvEP2_T ValueTyping.

Definition ValTypedByEnvA := RelatedByEnvEP_T ValueTyping.


(** fun typing lemmas from CRelLib *)

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

*)


  





