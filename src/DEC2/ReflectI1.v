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

Import ListNotations.


Module Reflect (IdT: ModTyp) <: ModTyp.

Module PreReflL := PreRefl IdT.
Export PreReflL.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.


Open Scope type_scope.

(*********************************************************************)


Definition ExpTrans3_def (fenv: funEnv) (k1: FEnvWT fenv) (n: nat) :=   
   fun (ftenv: funTC) (tenv: valTC) (e: Exp) (t: VTyp) 
       (k: ExpTyping ftenv tenv e t) =>   
          FEnvTyping fenv ftenv ->
          valTC_Trans tenv ->
          forall (n1: nat), n1 <= n -> W ->  
                            (sVTyp t * W) * sigT (fun n2 => n2 <= n1).     

Definition PrmsTrans3_def (fenv: funEnv) (k1: FEnvWT fenv) (n: nat) :=   
   fun (ftenv: funTC) (tenv: valTC) (ps: Prms) (pt: PTyp) 
       (k: PrmsTyping ftenv tenv ps pt) =>        
          FEnvTyping fenv ftenv ->
          valTC_Trans tenv ->
          forall (n1: nat), n1 <= n -> W ->  
                            (PTyp_TRN pt * W) * sigT (fun n2 => n2 <= n1). 


Definition Trans_ExpTyping_mut3 (fenv: funEnv) (D: FEnvWT fenv) (n: nat) :=
  ExpTyping_mut (ExpTrans3_def fenv D n) (PrmsTrans3_def fenv D n). 

Definition Trans_PrmsTyping_mut3 (fenv: funEnv) (D: FEnvWT fenv) (n: nat) :=
  PrmsTyping_mut (ExpTrans3_def fenv D n) (PrmsTrans3_def fenv D n).


Lemma ExpTrans_Val (fenv: funEnv) (D: FEnvWT fenv) (n: nat) : 
  forall (ftenv : funTC) (tenv : valTC) (v : Value) 
    (t : VTyp) (v0 : VTyping v t),
  ExpTrans3_def fenv D n ftenv tenv (Val v) t (Val_Typing ftenv tenv v t v0).
 unfold ExpTrans3_def.
 intros.
 inversion v0; subst.
 split.
 exact (sValue v, X0).
 econstructor 1 with (x := n1).
 auto.
Defined.

(*********************************************************************)



Lemma ExpTrans_Var (fenv: funEnv) (D: FEnvWT fenv) (n: nat) :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (t : VTyp) (i : IdTyping tenv x t),
  ExpTrans3_def fenv D n ftenv tenv (Var x) t (Var_Typing ftenv tenv x t i).
     unfold ExpTrans3_def.
     intros.
     eapply ExpDenI2_Var.
     exact i.
     exact X.
     exact X0.
Defined.

Lemma ExpTrans_BindN (fenv: funEnv) (D: FEnvWT fenv) (n: nat) :
  forall (ftenv : funTC) (tenv : valTC) (e1 e2 : Exp) 
    (t1 t2 : VTyp) (e : ExpTyping ftenv tenv e1 t1),
  ExpTrans3_def fenv D n ftenv tenv e1 t1 e ->
  forall e0 : ExpTyping ftenv tenv e2 t2,
  ExpTrans3_def fenv D n ftenv tenv e2 t2 e0 ->
  ExpTrans3_def fenv D n ftenv tenv (BindN e1 e2) t2
    (BindN_Typing ftenv tenv e1 e2 t1 t2 e e0).
     unfold ExpTrans3_def.
     intros.
     rename X2 into X3.
     rename X1 into X2.
     rename H into X1.
     rename H0 into H.
     specialize (X X1 X2 n1 H X3).
     destruct X as [p2 X].
     destruct X as [n2 q2]. 
     destruct p2 as [sv2 s2].
     assert (n2 <= n) as q3.
(*     omega. *)
     eapply le_trans with (m:=n1).
     exact q2.
     exact H.
     specialize (X0 X1 X2 n2 q3 s2).
     destruct X0 as [p3 X0].
     destruct X0 as [n3 q4].
     split.
     exact p3.
     econstructor 1 with (x:=n3).
     (*     omega. *)
     eapply le_trans with (m:=n2).
     exact q4.
     exact q2.
Defined.

Lemma ExpTrans_BindS (fenv: funEnv) (D: FEnvWT fenv) (n: nat) :
  forall (ftenv : funTC) (tenv tenv' : valTC) (x : StaticSemL.Id)
    (e1 e2 : Exp) (t1 t2 : VTyp) (m : option VTyp) 
    (m0 : Maybe t1 m) (e : tenv' = (x, t1) :: tenv)
    (e0 : ExpTyping ftenv tenv e1 t1),
  ExpTrans3_def fenv D n ftenv tenv e1 t1 e0 ->
  forall e3 : ExpTyping ftenv tenv' e2 t2,
  ExpTrans3_def fenv D n ftenv tenv' e2 t2 e3 ->
  ExpTrans3_def fenv D n ftenv tenv (BindS x m e1 e2) t2
                (BindS_Typing ftenv tenv tenv' x e1 e2 t1 t2 m m0 e e0 e3).
     unfold ExpTrans3_def.
     intros.
     rename X2 into X3.
     rename X1 into X2.
     rename H into X1.
     rename H0 into H.
     specialize (X X1 X2 n1 H X3).
     destruct X as [p2 X].
     destruct X as [n2 q2]. 
     destruct p2 as [sv1 s2].
     assert (n2 <= n) as q3.
(*     omega. *)
     eapply le_trans with (m:=n1).
     exact q2.
     exact H.
     inversion e; subst.
     clear H0.     
     unfold valTC_Trans in *.
     specialize (X0 X1 (ext_senv tenv X2 x t1 sv1) n2 q3 s2).
     destruct X0 as [p3 X0].
     destruct X0 as [n3 q4].
     split.
     exact p3.
     econstructor 1 with (x:=n3).
     (*     omega. *)
     eapply le_trans with (m:=n2).
     exact q4.
     exact q2.
Defined.
  

Lemma ExpTrans_BindMS (fenv: funEnv) (D: FEnvWT fenv) (n: nat) :
  forall (ftenv : funTC) (tenv tenv0 tenv1 : valTC) 
    (env0 : valEnv) (e : Exp) (t : VTyp) (e0 : EnvTyping env0 tenv0)
    (e1 : tenv1 = tenv0 ++ tenv) (e2 : ExpTyping ftenv tenv1 e t),
  ExpTrans3_def fenv D n ftenv tenv1 e t e2 ->
  ExpTrans3_def fenv D n ftenv tenv (BindMS env0 e) t
    (BindMS_Typing ftenv tenv tenv0 tenv1 env0 e t e0 e1 e2).
     unfold ExpTrans3_def.
     intros.
     rename X1 into X2.
     rename X0 into X1.
     rename H into X0.
     rename H0 into H.
     specialize (X X0). 
     inversion e1; subst.
     clear H0.
     eapply extend_valTC_Trans with (env0:=env0) (tenv0:=tenv0)
                                    (tenv:= tenv) in e0.
     specialize (X e0 n1 H X2).
     exact X.
     exact X1.
Defined.     
     

Lemma ExpTrans_IfThenElse (fenv: funEnv) (D: FEnvWT fenv) (n: nat) :
  forall (ftenv : funTC) (tenv : valTC) (e1 e2 e3 : Exp) 
    (t : VTyp) (e : ExpTyping ftenv tenv e1 Bool),
  ExpTrans3_def fenv D n ftenv tenv e1 Bool e ->
  forall e0 : ExpTyping ftenv tenv e2 t,
  ExpTrans3_def fenv D n ftenv tenv e2 t e0 ->
  forall e4 : ExpTyping ftenv tenv e3 t,
  ExpTrans3_def fenv D n ftenv tenv e3 t e4 ->
  ExpTrans3_def fenv D n ftenv tenv (IfThenElse e1 e2 e3) t
    (IfThenElse_Typing ftenv tenv e1 e2 e3 t e e0 e4).
     unfold ExpTrans3_def.
     intros.
     rename X3 into X4.
     rename X2 into X3.
     rename H into X2.
     rename H0 into H.
     specialize (X X2 X3 n1 H X4).
     destruct X as [p2 X].
     destruct X as [n2 q2]. 
     destruct p2 as [sv1 s2].
     assert (n2 <= n) as q3.
     (* omega. *)
     eapply le_trans.
     exact q2.
     exact H.
     simpl in sv1.
     destruct sv1.
     specialize (X0 X2 X3 n2 q3 s2).
     destruct X0 as [p3 X0].     
     destruct X0 as [n3 q4].
     split.
     exact p3.
     econstructor 1 with (x:=n3).
     (* omega. *)
     eapply le_trans.
     exact q4.
     exact q2.
     specialize (X1 X2 X3 n2 q3 s2).
     destruct X1 as [p3 X1].     
     destruct X1 as [n3 q4].
     split.
     exact p3.
     econstructor 1 with (x:=n3).
     (* omega. *)
     eapply le_trans.
     exact q4.
     exact q2.
Defined.
     
Lemma ExpTrans_Apply0 : 
  forall (fenv: funEnv) (D: FEnvWT fenv)
         (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (e : Exp) (ps : Prms) (pt : PTyp) (t : VTyp) (p : Pure e)
    (i : IdFTyping ftenv x (FT pt t)) (p0 : PrmsTyping ftenv tenv ps pt),
  PrmsTrans3_def fenv D 0 ftenv tenv ps pt p0 ->
  forall e0 : ExpTyping ftenv tenv e Nat,
  ExpTrans3_def fenv D 0 ftenv tenv e Nat e0 ->
  ExpTrans3_def fenv D 0 ftenv tenv (Apply x ps e) t
                (Apply_Typing ftenv tenv x e ps pt t p i p0 e0).
     unfold ExpTrans3_def, PrmsTrans3_def.
     intros.
     rename X2 into X3.
     rename X1 into X2.
     rename H into X1.
     rename H0 into H.
     specialize (X0 X1 X2 n1 H X3).
     destruct X0 as [p2 X0].
     destruct X0 as [n2 q2]. 
     destruct p2 as [sv1 s2].
     assert (n2 <= 0) as q3.
     omega.
     specialize (X X1 X2 n2 q3 s2).
     destruct X as [p3 X].     
     destruct X as [n3 q4].
     inversion i; subst.
     eapply (ExtRelVal2 funFTyp ftenv fenv x (FT pt t)) in H1.     
     destruct H1 as [f H0 H1].
     destruct f.
     unfold funFTyp in H1.
     destruct v.
     destruct v.
     simpl in *.
     inversion H1; subst.
     split.
     exact (v,(snd p3)).  
     econstructor 1 with (x:=n3).
     omega.
     exact X1.
Defined.

     
Lemma ExpTrans_Call0 : 
  forall (fenv: funEnv) (D: FEnvWT fenv)
         (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  PrmsTrans3_def fenv D 0 ftenv tenv (PS ls) pt p ->
  ExpTrans3_def fenv D 0 ftenv tenv (Call x (PS ls)) t
    (Call_Typing ftenv tenv x ls pt t i p).
     unfold ExpTrans3_def, PrmsTrans3_def.
     intros.
     rename X1 into X2.
     rename X0 into X1.
     rename H into X0.
     rename H0 into H.
     specialize (X X0 X1 n1 H X2).
     destruct X as [p3 X].     
     destruct X as [n3 q4].
     inversion i; subst.
     eapply (ExtRelVal2 funFTyp ftenv fenv x (FT pt t)) in H1.     
     destruct H1 as [f H0 H1].
     destruct f.
     unfold funFTyp in H1.
     destruct v.
     destruct v.
     simpl in *.
     inversion H1; subst.
     split.
     exact (v,(snd p3)).  
     econstructor 1 with (x:=n3).
     omega.
     exact X0.
Defined.

Lemma ExpTrans_Modify (fenv: funEnv) (D: FEnvWT fenv) (n: nat) :
  forall (ftenv : funTC) (tenv : valTC) (t1 t2 : VTyp) 
    (XF : XFun t1 t2) (e : Exp) (e0 : ExpTyping ftenv tenv e t1),
  ExpTrans3_def fenv D n ftenv tenv e t1 e0 ->
  ExpTrans3_def fenv D n ftenv tenv (Modify t1 t2 XF e) t2
    (Modify_Typing ftenv tenv t1 t2 XF e e0).
     unfold ExpTrans3_def.
     intros.
     rename X1 into X2.
     rename X0 into X1.
     rename H into X0.
     rename H0 into H.
     specialize (X X0 X1 n1 H X2).
     destruct X as [p3 X].     
     destruct X as [n3 q4].
     destruct p3 as [sv s3].
     destruct XF.
     set (x_mod0 sv s3) as p.
     subst inpT0.
     subst outT0.
     split.
     exact p.
     econstructor 1 with (x:=n3).
     (* omega. *)
     assumption.
Defined.     


Lemma ExpTrans_PrmsNil (fenv: funEnv) (D: FEnvWT fenv) (n: nat) :
  forall (ftenv : funTC) (tenv : valTC),
    PrmsTrans3_def fenv D n ftenv tenv (PS []) (PT [])
                   (PSNil_Typing ftenv tenv).
     unfold PrmsTrans3_def.
     intros.
     split.
     split.
     constructor.
     exact X0.
     econstructor 1 with (x:=n1).
     auto.
Defined.  


Lemma ExpTrans_Prms (fenv: funEnv) (D: FEnvWT fenv) (n: nat) :
  forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp) 
    (es : list Exp) (ts : list VTyp) (e0 : ExpTyping ftenv tenv e t),
  ExpTrans3_def fenv D n ftenv tenv e t e0 ->
  forall p : PrmsTyping ftenv tenv (PS es) (PT ts),
  PrmsTrans3_def fenv D n ftenv tenv (PS es) (PT ts) p ->
  PrmsTrans3_def fenv D n ftenv tenv (PS (e :: es)) (PT (t :: ts))
                 (PSCons_Typing ftenv tenv e t es ts e0 p).
     unfold ExpTrans3_def, PrmsTrans3_def.
     intros.
     rename X2 into X3.
     rename X1 into X2.
     rename H into X1.
     rename H0 into H.
     specialize (X X1 X2 n1 H X3).
     destruct X as [p2 X].
     destruct X as [n2 q2]. 
     destruct p2 as [sv1 s2].
     assert (n2 <= n) as q3.
     eapply le_trans.
     exact q2.
     exact H.
     (* omega *)
     specialize (X0 X1 X2 n2 q3 s2).
     destruct X0 as [p3 X0].
     destruct p3 as [svs3 s3].
     destruct X0 as [n3 q4].
     split.
     split.
     constructor.
     exact sv1.
     exact svs3.
     exact s3.
     econstructor 1 with (x:=n3).
     (* omega. *)
     eapply le_trans.
     exact q4.
     exact q2.
Defined.     
     
(*****************************************************************)

Lemma ExpTrans_ApplyE (fenv: funEnv) (D: FEnvWT fenv) (n : nat)
 (IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
        ExpTyping ftenv tenv e t ->
        FEnvTyping fenv ftenv ->
        valTC_Trans tenv ->
        forall n1 : nat, n1 <= n -> W -> sVTyp t * W * {n2 : nat & n2 <= n1}) :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (e : Exp) (ps : Prms) (pt : PTyp) (t : VTyp) (p : Pure e)
    (i : IdFTyping ftenv x (FT pt t)) (p0 : PrmsTyping ftenv tenv ps pt),
  PrmsTrans3_def fenv D (S n) ftenv tenv ps pt p0 ->
  forall e0 : ExpTyping ftenv tenv e Nat,
  ExpTrans3_def fenv D (S n) ftenv tenv e Nat e0 ->
  ExpTrans3_def fenv D (S n) ftenv tenv (Apply x ps e) t
    (Apply_Typing ftenv tenv x e ps pt t p i p0 e0).
     unfold ExpTrans3_def, PrmsTrans3_def.
     intros.
     rename X2 into X3.
     rename X1 into X2.
     rename H into X1.
     rename H0 into H.     
     specialize (X0 X1 X2 n1 H X3).
     destruct X0 as [p2 X0].
     destruct X0 as [n2 q2]. 
     destruct p2 as [sv1 s2].
     assert (n2 <= S n) as q3.
     omega.
     specialize (X X1 X2 n2 q3 s2).
     destruct X as [p3 X].
     destruct p3 as [svs2 s3].
     destruct X as [n3 q4].
     
     inversion i; subst.
     eapply (ExtRelVal2 funFTyp ftenv fenv x (FT pt t)) in H1.     
     destruct H1 as [f H0 H1].
     generalize D.
     intro k3.
     unfold FEnvWT in D.
     specialize (D ftenv X1 x f H0).
     unfold FunWT in D.
     destruct f.
     unfold funFTyp in H1.
     destruct v.
     destruct v.
     simpl in *.
     inversion H1; subst.
     clear H1.

     assert (n3 <= S n) as q5.
     omega.
     
     destruct n3.
     assert (0 <= n) as q6.
     omega.
     
     specialize (IHn ftenv tenv0 e1 t D X1 svs2 0 q6 s3).
     destruct IHn as [p4 IH].
     split.
     exact p4.
     destruct IH as [n5 IH].
     econstructor 1 with (x:=n5).
     omega.

     assert (n3 <= n) as q6.
     omega.
     
     specialize (IHn ftenv tenv0 e1 t D X1 svs2 n3 q6 s3).
     destruct IHn as [p4 IH].
     split.
     exact p4.
     destruct IH as [n5 IH].
     econstructor 1 with (x:=n5).
     omega.

     exact X1.
Defined.


Lemma ExpTrans_ApplyXXX (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
     (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
           (v: Value) (e: Exp)
           (t : VTyp) (m: VTyping v t)
      (i2 : findE fenv x = Some (FC tenv0 v e))     
      (IHn : FEnvTyping fenv ftenv ->
          valTC_Trans tenv0 ->
          forall (n0 : nat),
          n0 <= n -> W -> sVTyp t * W * {n1 : nat & n1 <= n0}) :
    forall (e9 : Exp) (ls : list Exp) (pt : PTyp) (p9 : Pure e9)
           (i1 : IdFTyping ftenv x (FT pt t))
           (p : PrmsTyping ftenv tenv (PS ls) pt),
      PrmsTrans3_def fenv D (S n) ftenv tenv (PS ls) pt p ->
   forall m9 : ExpTyping ftenv tenv e9 Nat,
   ExpTrans3_def fenv D (S n) ftenv tenv e9 Nat m9 ->
   ExpTrans3_def fenv D (S n) ftenv tenv (Apply x (PS ls) e9) t
                 (Apply_Typing ftenv tenv x e9 (PS ls) pt t p9 i1 p m9).
    unfold ExpTrans3_def, PrmsTrans3_def.
    intros e9 ls pt p9 i1 p.
    intros X m9 Y H X0 n1 H0 X1.
    specialize (Y H X0 n1 H0 X1).
    
    destruct Y as [pp9 Y].
    destruct pp9 as [n10 s9].
    destruct Y as [n9 q9].
    simpl in *.

    specialize (X H X0 n1 H0 X1).

    destruct X as [p3 X].
    destruct p3 as [svs2 s3].
    destruct X as [n3 q4].
    simpl in *.

    set (f:=FC tenv0 v e).
    set (ft:=FT pt t).
    unfold VTyping in m.
     
    generalize i1.
    intro i3.

    assert (0 <= n1) as qq.
    intuition.
    
    eapply (RelatedByEnv funFTyp fenv ftenv x f ft H i2) in i3.
    
    remember (min n3 n10) as n11.
    
    destruct n11.

    split.
    destruct v.
    destruct v.
    simpl in m.
    inversion m; subst.
    exact (v, s3).
    econstructor 1 with (x:=0).
    auto.
    
(* case S *)
    assert (n3 <= S n) as q02a.
    eapply le_trans.
    exact q4.
    exact H0.
    assert (S n11 <= n3) as q02b.
    rewrite Heqn11.
    intuition.
    assert (S n11 <= S n) as q02.
    eapply le_trans.
    exact q02b.
    exact q02a.
    assert (n11 <= n) as q2.
    eapply (le_inject _ _ q02).

    unfold PTyp_TRN in svs2.
    destruct pt.
    simpl in i3.
    inversion i3; subst.
    
    specialize (IHn H svs2 n11 q2 s3).
    
    destruct IHn as [IH1 IH2].

    split.
    exact IH1.
    destruct IH2 as [n4 IH2].

    econstructor 1 with (x:=n4).
    eapply le_trans.
    exact IH2.
    assert (n11 <= n3).
    eapply (le_decrease _ _ q02b).
    eapply le_trans.
    exact H1.
    exact q4.
Defined.    

Lemma ExpTrans_ApplyX_aux4_0 (fenv: funEnv) (D: FEnvWT fenv) (* n: nat *)
    (ftenv : funTC) (tenv tenv0 : valTC) (x : Id)
    (v: Value) (e: Exp)
    (t : VTyp) (m: valueVTyp v = t)
    (i2 : findE fenv x = Some (FC tenv0 v e))
  (e9 : Exp)
  (ls : list Exp)
  (pt : PTyp)
  (i1 : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (n1 : nat)
  (svs2 : PTyp_TRN pt)
  (s3 : W)
  (n3: nat)
  (q4 : n3 <= n1)
  (m9 : ExpTyping ftenv tenv e9 Nat)
  (n10 : nat)
  (H : FEnvTyping fenv ftenv)
  (X0 : valTC_Trans tenv)
  (X1 : W)
  (i3 : funFTyp (FC tenv0 v e) = FT pt t)
  (Heqn11 : 0 = Init.Nat.min n3 n10)
  :
  sVTyp t * W * {n2 : nat & n2 <= n1}.
    
    split.
    destruct v.
    destruct v.
    simpl in m.
    inversion m; subst.
    exact (v, s3).
    econstructor 1 with (x:=0).
    intuition.
Defined.

Lemma ExpTrans_ApplyX_aux4 (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv tenv0 : valTC) (x : Id)
    (v: Value) (e: Exp)
    (i2 : findE fenv x = Some (FC tenv0 v e))
    (n11 : nat)
    (IHn : sVTyp (valueVTyp v) * W * {n1 : nat & n1 <= n11})
  (e9 : Exp)  
  (ls : list Exp)
  (p : PrmsTyping ftenv tenv (PS ls) (PT (map snd tenv0)))
  (i : IdFTyping ftenv x (FT (PT (map snd tenv0)) (valueVTyp v)))
  (n1 : nat)
  (svs2 : tlist2type (PTyp_ListTrans (PT (map snd tenv0))))
  (s3 : W)
  (n3: nat)
  (q4 : n3 <= n1)
  (m9 : ExpTyping ftenv tenv e9 Nat)
  (n10 : nat)
  (s9 : W)
  (n9 : nat)
  (q9 : n9 <= n1)
  (H : FEnvTyping fenv ftenv)
  (X0 : valTC_Trans tenv)
  (H0 : n1 <= S n)
  (X1 : W)
  (i3 : FT (PT (map snd tenv0)) (projT1 v) =
        FT (PT (map snd tenv0)) (valueVTyp v))
  (Heqn11 : S n11 = Init.Nat.min n3 n10)
  (q02b : S n11 <= n3)
  (H3 : projT1 v = valueVTyp v) :
  sVTyp (projT1 v) * W * {n2 : nat & n2 <= n1}.    
    
    destruct IHn as [IH1 IH2].

    split.
    exact IH1.
    destruct IH2 as [n4 IH2].

    econstructor 1 with (x:=n4).
    eapply le_trans.
    exact IH2.
    assert (n11 <= n3).
    eapply (le_decrease _ _ q02b).
    eapply le_trans.
    exact H1.
    exact q4.
Defined.    

    
Lemma ExpTrans_ApplyX_aux3 (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
    (v: Value) (e: Exp)
    (t : VTyp) (m: valueVTyp v = t)
    (i2 : findE fenv x = Some (FC tenv0 v e))     
  (IHn : FEnvTyping fenv ftenv ->
        valTC_Trans tenv0 ->
        forall n0 : nat, n0 <= n -> W -> sVTyp t * W * {n1 : nat & n1 <= n0})
  (e9 : Exp)
  (ls : list Exp)
  (pt : PTyp)
  (i1 : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (n1 : nat)
  (svs2 : PTyp_TRN pt)
  (s3 : W)
  (n3 : nat)
  (q4 : n3 <= n1)
  (m9 : ExpTyping ftenv tenv e9 Nat)
  (n10 : nat)
  (s9 : W)
  (n9 : nat)
  (q9 : n9 <= n1)
  (H : FEnvTyping fenv ftenv)
  (X0 : valTC_Trans tenv)
  (H0 : n1 <= S n)
  (X1 : W)
  (i3 : funFTyp (FC tenv0 v e) = FT pt t) : 
  sVTyp t * W * {n2 : nat & n2 <= n1}.
    
    remember (min n3 n10) as n11.
    
    destruct n11.

(* case 0 *)
    eapply (ExpTrans_ApplyX_aux4_0 fenv D ftenv tenv tenv0
                                x v e t m i2 e9 ls pt i1 p n1
                                svs2 s3 n3 q4 m9 n10 H X0
                                X1 i3 Heqn11).
     
(* case S *)
    assert (n3 <= S n) as q02a.
    eapply le_trans.
    exact q4.
    exact H0.
    assert (S n11 <= n3) as q02b.
    rewrite Heqn11.
    intuition.
    assert (S n11 <= S n) as q02.
    eapply le_trans.
    exact q02b.
    exact q02a.
    assert (n11 <= n) as q2.
    eapply (le_inject _ _ q02).

    unfold PTyp_TRN in svs2.
    destruct pt.
    simpl in i3.
    inversion i3; subst.
    
    specialize (IHn H svs2 n11 q2 s3).

    eapply (ExpTrans_ApplyX_aux4 fenv D n ftenv tenv tenv0
                                x v e i2 n11 IHn e9 ls p i1 n1
                                svs2 s3 n3 q4 m9 n10 s9 n9 q9 
                                H X0 H0 X1 i3 Heqn11 q02b H3).
Defined.
    


Lemma ExpTrans_ApplyX_aux2 (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
    (v: Value) (e: Exp)
    (t : VTyp) (m: VTyping v t)
    (i2 : findE fenv x = Some (FC tenv0 v e))     
  (IHn : FEnvTyping fenv ftenv ->
        valTC_Trans tenv0 ->
        forall n0 : nat, n0 <= n -> W -> sVTyp t * W * {n1 : nat & n1 <= n0})
  (e9 : Exp)
  (ls : list Exp)
  (pt : PTyp)
  (i1 : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (n1 : nat)
  (svs2 : PTyp_TRN pt)
  (s3 : W)
  (n3 : nat)
  (q4 : n3 <= n1)
  (m9 : ExpTyping ftenv tenv e9 Nat)
  (n10 : nat)
  (s9 : W)
  (n9 : nat)
  (q9 : n9 <= n1)
  (H : FEnvTyping fenv ftenv)
  (X0 : valTC_Trans tenv)
  (H0 : n1 <= S n)
  (X1 : W) :
  sVTyp t * W * {n2 : nat & n2 <= n1}.
    
    set (f:=FC tenv0 v e).
    set (ft:=FT pt t).
    unfold VTyping in m.
     
    generalize i1.
    intro i3.

    assert (0 <= n1) as qq.
    intuition.
    
    eapply (RelatedByEnv funFTyp fenv ftenv x f ft H i2) in i3.

    eapply (ExpTrans_ApplyX_aux3 fenv D n ftenv tenv tenv0
                         x v e t m i2 IHn e9 ls pt i1 p n1 svs2 s3 n3 q4
                                 m9 n10 s9 n9 q9 H X0 H0 X1 i3).
Defined.


Lemma ExpTrans_ApplyX_aux1 (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
    (v: Value) (e: Exp)
    (t : VTyp) (m: VTyping v t)
    (i2 : findE fenv x = Some (FC tenv0 v e))     
  (IHn : FEnvTyping fenv ftenv ->
        valTC_Trans tenv0 ->
        forall n0 : nat, n0 <= n -> W -> sVTyp t * W * {n1 : nat & n1 <= n0})
  (e9: Exp) 
  (ls : list Exp)
  (pt : PTyp)
  (i1 : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (n1 : nat)
  (X : PTyp_TRN pt * W * {n2 : nat & n2 <= n1})
  (m9 : ExpTyping ftenv tenv e9 Nat)
  (n10 : nat)
  (s9 : W)
  (n9 : nat)
  (q9 : n9 <= n1)
  (H : FEnvTyping fenv ftenv)
  (X0 : valTC_Trans tenv)
  (H0 : n1 <= S n)
  (X1 : W) :
  sVTyp t * W * {n2 : nat & n2 <= n1}.
    
    destruct X as [p3 X].
    destruct p3 as [svs2 s3].
    destruct X as [n3 q4].
    simpl in *.

    eapply (ExpTrans_ApplyX_aux2 fenv D n ftenv tenv tenv0
                         x v e t m i2 IHn e9 ls pt i1 p n1 svs2 s3 n3 q4
                                 m9 n10 s9 n9 q9 H X0 H0 X1).
Defined.


Lemma ExpTrans_ApplyX_aux0 (fenv : funEnv)
    (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
    (v: Value) (e: Exp)
    (t : VTyp) (m: VTyping v t)
    (i2 : findE fenv x = Some (FC tenv0 v e))     
  (IHn : FEnvTyping fenv ftenv ->
        valTC_Trans tenv0 ->
        forall n0 : nat, n0 <= n -> W -> sVTyp t * W * {n1 : nat & n1 <= n0})
  (e9: Exp)
  (ls : list Exp)
  (pt : PTyp)
  (i1 : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (X : FEnvTyping fenv ftenv ->
      valTC_Trans tenv ->
      forall n1 : nat,
      n1 <= S n ->
      W -> PTyp_TRN pt * W * {n2 : nat & n2 <= n1})
  (m9 : ExpTyping ftenv tenv e9 Nat)
  (n1 : nat)
  (Y : sVTyp Nat * W * {n2 : nat & n2 <= n1})  
  (H : FEnvTyping fenv ftenv)
  (X0 : valTC_Trans tenv)
  (H0 : n1 <= S n)
  (X1 : W) :
  sVTyp t * W * {n2 : nat & n2 <= n1}.
  
    destruct Y as [pp9 Y].
    destruct pp9 as [n10 s9].
    destruct Y as [n9 q9].
    simpl in *.

    specialize (X H X0 n1 H0 X1).

    eapply (ExpTrans_ApplyX_aux1 fenv D n ftenv tenv tenv0
           x v e t m i2 IHn e9 ls pt i1 p n1 X m9 n10 s9 n9 q9 H X0 H0 X1).
Defined.


Lemma ExpTrans_ApplyX (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
     (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
           (v: Value) (e: Exp)
           (t : VTyp) (m: VTyping v t)
      (i2 : findE fenv x = Some (FC tenv0 v e))     
      (IHn : FEnvTyping fenv ftenv ->
          valTC_Trans tenv0 ->
          forall (n0 : nat),
          n0 <= n -> W -> sVTyp t * W * {n1 : nat & n1 <= n0}) :
    forall (e9 : Exp) (ls : list Exp) (pt : PTyp) (p9 : Pure e9)
           (i1 : IdFTyping ftenv x (FT pt t))
           (p : PrmsTyping ftenv tenv (PS ls) pt),
      PrmsTrans3_def fenv D (S n) ftenv tenv (PS ls) pt p ->
   forall m9 : ExpTyping ftenv tenv e9 Nat,
   ExpTrans3_def fenv D (S n) ftenv tenv e9 Nat m9 ->
   ExpTrans3_def fenv D (S n) ftenv tenv (Apply x (PS ls) e9) t
                 (Apply_Typing ftenv tenv x e9 (PS ls) pt t p9 i1 p m9).
    unfold ExpTrans3_def, PrmsTrans3_def.
    intros e9 ls pt p9 i1 p.
    intros X m9 Y H X0 n1 H0 X1.
    specialize (Y H X0 n1 H0 X1).

    eapply (ExpTrans_ApplyX_aux0 fenv D n ftenv tenv tenv0
           x v e t m i2 IHn e9 ls pt i1 p X m9 n1 Y H X0 H0 X1).
Defined.


(*********************************************************************)

Lemma ExpTrans_CallE_old (fenv: funEnv) (D: FEnvWT fenv) (n : nat)
 (IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
        ExpTyping ftenv tenv e t ->
        FEnvTyping fenv ftenv ->
        valTC_Trans tenv ->
        forall n1 : nat, n1 <= n -> W -> sVTyp t * W * {n2 : nat & n2 <= n1}) :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  PrmsTrans3_def fenv D (S n) ftenv tenv (PS ls) pt p ->
  ExpTrans3_def fenv D (S n) ftenv tenv (Call x (PS ls)) t
    (Call_Typing ftenv tenv x ls pt t i p).
     unfold ExpTrans3_def, PrmsTrans3_def.
     intros.
     rename X1 into X2.
     rename X0 into X1.
     rename H into X0.
     rename H0 into H.
     specialize (X X0 X1 n1 H X2).
     destruct X as [p3 X].
     destruct p3 as [svs2 s3].
     destruct X as [n3 q4].
     
     inversion i; subst.
     eapply (ExtRelVal2 funFTyp ftenv fenv x (FT pt t)) in H1.     
     destruct H1 as [f H0 H1].
     generalize D.
     intro k3.
     unfold FEnvWT in D.
     specialize (D ftenv X0 x f H0).
     unfold FunWT in D.
     destruct f.
     unfold funFTyp in H1.
     destruct v.
     destruct v.
     simpl in *.
     inversion H1; subst.
     clear H1.

     assert (n3 <= S n) as q5.
     omega.
     
     destruct n3.
     assert (0 <= n) as q6.
     omega.
     
     specialize (IHn ftenv tenv0 e t D X0 svs2 0 q6 s3).
     destruct IHn as [p4 IH].
     split.
     exact p4.
     destruct IH as [n5 IH].
     econstructor 1 with (x:=n5).
     omega.

     assert (n3 <= n) as q6.
     omega.
     
     specialize (IHn ftenv tenv0 e t D X0 svs2 n3 q6 s3).
     destruct IHn as [p4 IH].
     split.
     exact p4.
     destruct IH as [n5 IH].
     econstructor 1 with (x:=n5).
     omega.

     exact X0.
Defined.


Lemma ExpTrans_CallX_aux4 (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv tenv0 : valTC) (x : Id)
           (v: Value) (e: Exp)
           (i2 : findE fenv x = Some (FC tenv0 v e))
           (n3 : nat)
  (IHn : sVTyp (valueVTyp v) * W * {n1 : nat & n1 <= n3})           
  (ls : list Exp)
  (p : PrmsTyping ftenv tenv (PS ls) (PT (map snd tenv0)))
  (i : IdFTyping ftenv x (FT (PT (map snd tenv0)) (valueVTyp v)))
  (n1 : nat)
  (svs2 : tlist2type (PTyp_ListTrans (PT (map snd tenv0))))
  (s3 : W)
  (q4 : S n3 <= n1)
  (H : FEnvTyping fenv ftenv)
  (X0 : valTC_Trans tenv)
  (H0 : n1 <= S n)
  (X1 : W)
  (i3 : FT (PT (map snd tenv0)) (projT1 v) =
        FT (PT (map snd tenv0)) (valueVTyp v))
  (q2 : n3 <= n)
  (H3 : projT1 v = valueVTyp v) :
  sVTyp (projT1 v) * W * {n2 : nat & n2 <= n1}.    
    destruct IHn as [IH1 IH2].

    split.
    exact IH1.
    destruct IH2 as [n4 IH2].

    econstructor 1 with (x:=n4).
    eapply le_trans.
    exact IH2.
    eapply (le_decrease _ _ q4).
Defined.    


Lemma ExpTrans_CallX_aux4_0 (fenv: funEnv) (D: FEnvWT fenv) 
    (ftenv : funTC) (tenv tenv0 : valTC) (x : Id)
           (v: Value) (e: Exp)
           (t : VTyp) (m: valueVTyp v = t)
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (ls : list Exp)
  (pt : PTyp)
  (i : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (n1 : nat)
  (svs2 : PTyp_TRN pt)
  (s3 : W)
  (q4 : 0 <= n1)
  (H : FEnvTyping fenv ftenv)
  (X0 : valTC_Trans tenv)
  (X1 : W)
  (i3 : funFTyp (FC tenv0 v e) = FT pt t) :
  sVTyp t * W * {n2 : nat & n2 <= n1}.
    split.
    destruct v.
    destruct v.
    simpl in m.
    inversion m; subst.
    exact (v, s3).
    econstructor 1 with (x:=0).
    auto.
Defined.


Lemma ExpTrans_CallX_aux3 (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
           (v: Value) (e: Exp)
           (t : VTyp) (m: valueVTyp v = t)
      (i2 : findE fenv x = Some (FC tenv0 v e))     
  (IHn : FEnvTyping fenv ftenv ->
        valTC_Trans tenv0 ->
        forall n0 : nat, n0 <= n -> W -> sVTyp t * W * {n1 : nat & n1 <= n0})
  (ls : list Exp)
  (pt : PTyp)
  (i : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (n1 : nat)
  (svs2 : PTyp_TRN pt)
  (s3 : W)
  (n3 : nat)
  (q4 : n3 <= n1)
  (H : FEnvTyping fenv ftenv)
  (X0 : valTC_Trans tenv)
  (H0 : n1 <= S n)
  (X1 : W)
  (i3 : funFTyp (FC tenv0 v e) = FT pt t) : 
  sVTyp t * W * {n2 : nat & n2 <= n1}.
    destruct n3.

(* case 0 *)
    eapply (ExpTrans_CallX_aux4_0 fenv D ftenv tenv tenv0
                                x v e t m i2 ls pt i p n1
                                svs2 s3 q4 H X0 X1 i3).
   
(* case S *)
    assert (S n3 <= S n) as q02.
    eapply le_trans.
    exact q4.
    exact H0.
    assert (n3 <= n) as q2.
    eapply (le_inject _ _ q02).

    unfold PTyp_TRN in svs2.
    destruct pt.
    simpl in i3.
    inversion i3; subst.
    
    specialize (IHn H svs2 n3 q2 s3).
    eapply (ExpTrans_CallX_aux4 fenv D n ftenv tenv tenv0
                                x v e i2 n3 IHn ls p i n1
                                svs2 s3 q4 H X0 H0 X1 i3 q2 H3).
Defined.


Lemma ExpTrans_CallX_aux2 (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
           (v: Value) (e: Exp)
           (t : VTyp) (m: VTyping v t)
      (i2 : findE fenv x = Some (FC tenv0 v e))     
  (IHn : FEnvTyping fenv ftenv ->
        valTC_Trans tenv0 ->
        forall n0 : nat, n0 <= n -> W -> sVTyp t * W * {n1 : nat & n1 <= n0})
  (ls : list Exp)
  (pt : PTyp)
  (i : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (n1 : nat)
  (svs2 : PTyp_TRN pt)
  (s3 : W)
  (n3 : nat)
  (q4 : n3 <= n1)
  (H : FEnvTyping fenv ftenv)
  (X0 : valTC_Trans tenv)
  (H0 : n1 <= S n)
  (X1 : W) :
  sVTyp t * W * {n2 : nat & n2 <= n1}.
    set (f:=FC tenv0 v e).
    set (ft:=FT pt t).
    unfold VTyping in m.
     
    generalize i.
    intro i3.

    eapply (RelatedByEnv funFTyp fenv ftenv x f ft H i2) in i3.
    eapply (ExpTrans_CallX_aux3 fenv D n ftenv tenv tenv0
                                x v e t m i2 IHn ls pt i p n1
                                svs2 s3 n3 q4 H X0 H0 X1 i3).
Defined.



Lemma ExpTrans_CallX_aux1 (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
    (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
           (v: Value) (e: Exp)
           (t : VTyp) (m: VTyping v t)
      (i2 : findE fenv x = Some (FC tenv0 v e))     
  (IHn : FEnvTyping fenv ftenv ->
        valTC_Trans tenv0 ->
        forall n0 : nat, n0 <= n -> W -> sVTyp t * W * {n1 : nat & n1 <= n0})
  (ls : list Exp)
  (pt : PTyp)
  (i : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (n1 : nat)
  (X : PTyp_TRN pt * W * {n2 : nat & n2 <= n1})
  (H : FEnvTyping fenv ftenv)
  (X0 : valTC_Trans tenv)
  (H0 : n1 <= S n)
  (X1 : W) :
  sVTyp t * W * {n2 : nat & n2 <= n1}.
    destruct X as [p3 X].
    destruct p3 as [svs2 s3].
    destruct X as [n3 q4].
    simpl in *.
    eapply (ExpTrans_CallX_aux2 fenv D n ftenv tenv tenv0
                                x v e t m i2 IHn ls pt i p n1
                                svs2 s3 n3 q4 H X0 H0 X1).
Defined.


Lemma ExpTrans_CallX : forall (fenv: funEnv) (D: FEnvWT fenv) (n: nat),
    forall (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
           (v: Value) (e: Exp)
           (t : VTyp) (m: VTyping v t)
      (i2 : findE fenv x = Some (FC tenv0 v e))     
      (IHn : FEnvTyping fenv ftenv ->
          valTC_Trans tenv0 ->
          forall (n0 : nat),
          n0 <= n -> W -> sVTyp t * W * {n1 : nat & n1 <= n0}),
    forall (ls : list Exp) (pt : PTyp) 
           (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  PrmsTrans3_def fenv D (S n) ftenv tenv (PS ls) pt p ->
  ExpTrans3_def fenv D (S n) ftenv tenv (Call x (PS ls)) t
    (Call_Typing ftenv tenv x ls pt t i p).
    unfold ExpTrans3_def, PrmsTrans3_def.
    intros.
    specialize (X H X0 n1 H0 X1).
    eapply (ExpTrans_CallX_aux1 fenv D n ftenv tenv tenv0
           x v e t m i2 IHn ls pt i p n1 X H X0 H0 X1).
Defined.


Lemma ExpTrans_CallX0_aux1 (fenv : funEnv)
  (D : FEnvWT fenv)
  (ftenv : funTC)
  (tenv tenv0 : valTC)
  (x : Id)
  (v : Value)
  (e : Exp)
  (t : VTyp)
  (m : VTyping v t)
  (i2 : findE fenv x = Some (FC tenv0 v e))
  (ls : list Exp)
  (pt : PTyp)
  (i : IdFTyping ftenv x (FT pt t))
  (p : PrmsTyping ftenv tenv (PS ls) pt)
  (n1 : nat)
  (X : PTyp_TRN pt * W * {n2 : nat & n2 <= n1})
  (H : FEnvTyping fenv ftenv)
  (X0 : valTC_Trans tenv)
  (H0 : n1 <= 0)
  (X1 : W) :
  sVTyp t * W * {n2 : nat & n2 <= n1}.

    destruct X as [p3 X].
    destruct p3 as [svs2 s3].
    destruct X as [n3 q4].
    simpl in *.

    set (f:=FC tenv0 v e).
    set (ft:=FT pt t).
    unfold VTyping in m.
     
    generalize i.
    intro i3.

    assert (0 <= n1) as qq.
    intuition.
    
    eapply (RelatedByEnv funFTyp fenv ftenv x f ft H i2) in i3.
    
    eapply (ExpTrans_CallX_aux4_0 fenv D ftenv tenv tenv0
                                x v e t m i2 ls pt i p n1
                                svs2 s3 qq H X0 X1 i3).
Defined.

Lemma ExpTrans_CallX0 : forall (fenv: funEnv) (D: FEnvWT fenv),
    forall (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
           (v: Value) (e: Exp)
           (t : VTyp) (m: VTyping v t)
      (i2 : findE fenv x = Some (FC tenv0 v e)),      
    forall (ls : list Exp) (pt : PTyp) 
           (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  PrmsTrans3_def fenv D 0 ftenv tenv (PS ls) pt p ->
  ExpTrans3_def fenv D 0 ftenv tenv (Call x (PS ls)) t
    (Call_Typing ftenv tenv x ls pt t i p).
    unfold ExpTrans3_def, PrmsTrans3_def.
    intros.
    specialize (X H X0 n1 H0 X1).

    eapply (ExpTrans_CallX0_aux1 fenv D ftenv tenv tenv0 x v e t m i2
                                 ls pt i p n1 X H X0 H0 X1).
Defined.


Lemma Convert_Trans_Call (fenv: funEnv) (D: FEnvWT fenv) (n: nat) :
  (forall (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
           (v: Value) (e: Exp)
           (t : VTyp) (m: VTyping v t)
      (i2 : findE fenv x = Some (FC tenv0 v e))     
      (IHn : FEnvTyping fenv ftenv ->
          valTC_Trans tenv0 ->
          forall (n0 : nat),
          n0 <= n -> W -> sVTyp t * W * {n1 : nat & n1 <= n0}),
    forall (ls : list Exp) (pt : PTyp) 
           (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  PrmsTrans3_def fenv D (S n) ftenv tenv (PS ls) pt p ->
  ExpTrans3_def fenv D (S n) ftenv tenv (Call x (PS ls)) t
                (Call_Typing ftenv tenv x ls pt t i p)) -> 
  (forall (IHn : forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
        ExpTyping ftenv tenv e t ->
        FEnvTyping fenv ftenv ->
        valTC_Trans tenv ->
        forall n1 : nat, n1 <= n -> W -> sVTyp t * W * {n2 : nat & n2 <= n1})
    (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  PrmsTrans3_def fenv D (S n) ftenv tenv (PS ls) pt p ->
  ExpTrans3_def fenv D (S n) ftenv tenv (Call x (PS ls)) t
                (Call_Typing ftenv tenv x ls pt t i p)).
  intros.
  generalize i.
  intro i2.
  unfold IdFTyping in i.
  unfold EnvrAssign in i.

  unfold ExpTrans3_def.
  intros.

  eapply ExtRelVal2 with (f:=funFTyp) (venv:=fenv) in i.
  destruct i as [f m d].
  Focus 2.
  assumption.
  
  generalize D.
  intro D1.
  unfold FEnvWT in D1.
  specialize (D1 ftenv H x f m).
  unfold FunWT in D1.

  destruct f.
  simpl in d.
  inversion d; subst.
  set (t:= projT1 v).
  
  assert ((forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
        ExpTyping ftenv tenv e t ->
        FEnvTyping fenv ftenv ->
        valTC_Trans tenv ->
        forall n1 : nat, n1 <= n -> W -> sVTyp t * W * {n2 : nat & n2 <= n1})
          ->
         (FEnvTyping fenv ftenv ->
       valTC_Trans tenv0 ->
       forall n0 : nat, n0 <= n -> W -> sVTyp t * W * {n1 : nat & n1 <= n0}))
    as IHc.

  intros.
  subst t.
  specialize (X3 ftenv tenv0 e (projT1 v) D1 H X4 n0 H2 X5).
  exact X3.

  specialize (X ftenv tenv tenv0 x v e (projT1 v) eq_refl m (IHc IHn)
                ls (PT (map snd tenv0)) i2 p X0).
  eapply X.
  assumption.
  assumption.
  assumption.
  exact X2.
Defined.

Lemma Convert_Trans_Call0 (fenv: funEnv) (D: FEnvWT fenv) :
  (forall (ftenv : funTC) (tenv tenv0 : valTC) (x : StaticSemL.Id)
           (v: Value) (e: Exp)
           (t : VTyp) (m: VTyping v t)
      (i2 : findE fenv x = Some (FC tenv0 v e)),      
    forall (ls : list Exp) (pt : PTyp) 
           (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  PrmsTrans3_def fenv D 0 ftenv tenv (PS ls) pt p ->
  ExpTrans3_def fenv D 0 ftenv tenv (Call x (PS ls)) t
                (Call_Typing ftenv tenv x ls pt t i p)) ->
  (forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (ls : list Exp) (pt : PTyp) (t : VTyp) (i : IdFTyping ftenv x (FT pt t))
    (p : PrmsTyping ftenv tenv (PS ls) pt),
  PrmsTrans3_def fenv D 0 ftenv tenv (PS ls) pt p ->
  ExpTrans3_def fenv D 0 ftenv tenv (Call x (PS ls)) t
    (Call_Typing ftenv tenv x ls pt t i p)).
  intros.
  generalize i.
  intro i2.
  unfold IdFTyping in i.
  unfold EnvrAssign in i.

  unfold ExpTrans3_def.
  intros.

  eapply ExtRelVal2 with (f:=funFTyp) (venv:=fenv) in i.
  destruct i as [f m d].
  Focus 2.
  assumption.
  
  generalize D.
  intro D1.
  unfold FEnvWT in D1.
  specialize (D1 ftenv H x f m).
  unfold FunWT in D1.

  destruct f.
  simpl in d.
  inversion d; subst.
  set (t:= projT1 v).
  
  intros.
  subst t.

  specialize (X ftenv tenv tenv0 x v e (projT1 v) eq_refl m 
                ls (PT (map snd tenv0)) i2 p X0).
  eapply X.
  assumption.
  assumption.
  assumption.
  exact X2.
Defined.
  


Lemma Prms2ExpIH (fenv: funEnv) (D: FEnvWT fenv) (n : nat)  
 (IHn : forall (ftenv : funTC) (tenv : valTC) (ps : Prms) (pt : PTyp),
        PrmsTyping ftenv tenv ps pt ->
        FEnvTyping fenv ftenv ->
        valTC_Trans tenv ->
        forall n1 : nat,
        n1 <= n -> W -> PTyp_TRN pt * W * {n2 : nat & n2 <= n1}) :
  forall (ftenv : funTC) (tenv : valTC) (e : Exp) (t : VTyp),
  ExpTyping ftenv tenv e t ->
  FEnvTyping fenv ftenv ->
  valTC_Trans tenv ->
  forall n1 : nat, n1 <= n -> W -> sVTyp t * W * {n2 : nat & n2 <= n1}.
Proof.
  intros.
  set (ps := PS [e]).
  set (pt := PT [t]).
  assert (PrmsTyping ftenv tenv  ps pt) as X4.
  constructor.
  assumption.
  constructor.
  specialize  (IHn ftenv tenv ps pt X4 H X0 n1 H0 X1). 
  destruct IHn as [p1 c].
  destruct p1 as [sps w].
  simpl in sps.
  unfold PTyp_TRN in sps.
  simpl in sps.
  exact (fst sps, w, c).
Defined.  


(*********************** main ****************************************)

Program Fixpoint ExpTransB (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
        (ftenv: funTC) (tenv: valTC) (e: Exp) (t: VTyp) 
        (k: ExpTyping ftenv tenv e t) :
               FEnvTyping fenv ftenv ->  
               valTC_Trans tenv ->
          forall (n1: nat), n1 <= n -> W ->
                      (sVTyp t * W) * sigT (fun n2 => n2 <= n1) := _    
with PrmsTransB (fenv: funEnv) (D: FEnvWT fenv) (n: nat)
       (ftenv: funTC) (tenv: valTC) (ps: Prms) (pt: PTyp) 
       (k: PrmsTyping ftenv tenv ps pt) :              
              FEnvTyping fenv ftenv ->
              valTC_Trans tenv ->
          forall (n1: nat), n1 <= n -> W ->
                     (PTyp_TRN pt * W) * sigT (fun n2 => n2 <= n1) := _.        
Next Obligation.
   intros fenv D n.
   induction n.
   eapply (Trans_ExpTyping_mut3 fenv D 0).   
   - eapply (ExpTrans_Val fenv D 0).
   - eapply (ExpTrans_Var fenv D 0).
   - eapply (ExpTrans_BindN fenv D 0).
   - eapply (ExpTrans_BindS fenv D 0).
   - eapply (ExpTrans_BindMS fenv D 0).
   - eapply (ExpTrans_IfThenElse fenv D 0).
   - eapply (ExpTrans_Apply0 fenv D).
   - eapply (Convert_Trans_Call0 fenv D (ExpTrans_CallX0 fenv D)). 
   - eapply (ExpTrans_Modify fenv D 0).
   - eapply (ExpTrans_PrmsNil fenv D 0).
   - eapply (ExpTrans_Prms fenv D 0).
   - eapply (Trans_ExpTyping_mut3 fenv D (S n)).   
     * eapply (ExpTrans_Val fenv D (S n)).
     * eapply (ExpTrans_Var fenv D (S n)).
     * eapply (ExpTrans_BindN fenv D (S n)).
     * eapply (ExpTrans_BindS fenv D (S n)). 
     * eapply (ExpTrans_BindMS fenv D (S n)).
     * eapply (ExpTrans_IfThenElse fenv D (S n)).
     * eapply (ExpTrans_ApplyE fenv D n).
       assumption.
     * eapply (Convert_Trans_Call fenv D n (ExpTrans_CallX fenv D n)).
       assumption.
     * eapply (ExpTrans_Modify fenv D (S n)).
     * eapply (ExpTrans_PrmsNil fenv D (S n)).
     * eapply (ExpTrans_Prms fenv D (S n)). 
Defined.   
       
Next Obligation.
   intros fenv D n.
   induction n.
   eapply (Trans_PrmsTyping_mut3 fenv D 0).   
   - eapply (ExpTrans_Val fenv D 0).
   - eapply (ExpTrans_Var fenv D 0).
   - eapply (ExpTrans_BindN fenv D 0).
   - eapply (ExpTrans_BindS fenv D 0).
   - eapply (ExpTrans_BindMS fenv D 0).
   - eapply (ExpTrans_IfThenElse fenv D 0).
   - eapply (ExpTrans_Apply0 fenv D).
   - eapply (Convert_Trans_Call0 fenv D (ExpTrans_CallX0 fenv D)). 
   - eapply (ExpTrans_Modify fenv D 0).
   - eapply (ExpTrans_PrmsNil fenv D 0).
   - eapply (ExpTrans_Prms fenv D 0).
   - eapply (Trans_PrmsTyping_mut3 fenv D (S n)).   
     * eapply (ExpTrans_Val fenv D (S n)).
     * eapply (ExpTrans_Var fenv D (S n)).
     * eapply (ExpTrans_BindN fenv D (S n)).
     * eapply (ExpTrans_BindS fenv D (S n)). 
     * eapply (ExpTrans_BindMS fenv D (S n)).
     * eapply (ExpTrans_IfThenElse fenv D (S n)).
     * eapply (ExpTrans_ApplyE fenv D n).
       eapply (Prms2ExpIH fenv D).
       assumption.
     * eapply (Convert_Trans_Call fenv D n (ExpTrans_CallX fenv D n)).
       eapply (Prms2ExpIH fenv D).
       assumption.
     * eapply (ExpTrans_Modify fenv D (S n)).
     * eapply (ExpTrans_PrmsNil fenv D (S n)).
     * eapply (ExpTrans_Prms fenv D (S n)). 
Defined.   


Lemma ExpTransA (fenv: funEnv) (D: FEnvWT fenv) (n: nat) :
  forall (ftenv: funTC) (tenv: valTC) (e: Exp) (t: VTyp) 
        (k: ExpTyping ftenv tenv e t),   
               FEnvTyping fenv ftenv ->  
               valTC_Trans tenv ->
          forall (n1: nat), n1 <= n -> W ->
                      (sVTyp t * W) * sigT (fun n2 => n2 <= n1).
Proof.
   induction n.
   eapply (Trans_ExpTyping_mut3 fenv D 0).   
   - eapply (ExpTrans_Val fenv D 0).
   - eapply (ExpTrans_Var fenv D 0).
   - eapply (ExpTrans_BindN fenv D 0).
   - eapply (ExpTrans_BindS fenv D 0).
   - eapply (ExpTrans_BindMS fenv D 0).
   - eapply (ExpTrans_IfThenElse fenv D 0).
   - eapply (ExpTrans_Apply0 fenv D).
   - eapply (Convert_Trans_Call0 fenv D (ExpTrans_CallX0 fenv D)).  
   - eapply (ExpTrans_Modify fenv D 0).
   - eapply (ExpTrans_PrmsNil fenv D 0).
   - eapply (ExpTrans_Prms fenv D 0).
   - eapply (Trans_ExpTyping_mut3 fenv D (S n)).   
     * eapply (ExpTrans_Val fenv D (S n)).
     * eapply (ExpTrans_Var fenv D (S n)).
     * eapply (ExpTrans_BindN fenv D (S n)).
     * eapply (ExpTrans_BindS fenv D (S n)). 
     * eapply (ExpTrans_BindMS fenv D (S n)).
     * eapply (ExpTrans_IfThenElse fenv D (S n)).
     * eapply (ExpTrans_ApplyE fenv D n).
       assumption.
     * eapply (Convert_Trans_Call fenv D n (ExpTrans_CallX fenv D n)).
       assumption.
     * eapply (ExpTrans_Modify fenv D (S n)).
     * eapply (ExpTrans_PrmsNil fenv D (S n)).
     * eapply (ExpTrans_Prms fenv D (S n)). 
Defined.   

Lemma PrmsTransA (fenv: funEnv) (D: FEnvWT fenv) (n: nat) :
  forall (ftenv: funTC) (tenv: valTC) (ps: Prms) (pt: PTyp) 
       (k: PrmsTyping ftenv tenv ps pt),   
              FEnvTyping fenv ftenv ->
              valTC_Trans tenv ->
          forall (n1: nat), n1 <= n -> W ->
                     (PTyp_TRN pt * W) * sigT (fun n2 => n2 <= n1).        
   induction n.
   eapply (Trans_PrmsTyping_mut3 fenv D 0).   
   - eapply (ExpTrans_Val fenv D 0).
   - eapply (ExpTrans_Var fenv D 0).
   - eapply (ExpTrans_BindN fenv D 0).
   - eapply (ExpTrans_BindS fenv D 0).
   - eapply (ExpTrans_BindMS fenv D 0).
   - eapply (ExpTrans_IfThenElse fenv D 0).
   - eapply (ExpTrans_Apply0 fenv D).
   - eapply (Convert_Trans_Call0 fenv D (ExpTrans_CallX0 fenv D)).  
   - eapply (ExpTrans_Modify fenv D 0).
   - eapply (ExpTrans_PrmsNil fenv D 0).
   - eapply (ExpTrans_Prms fenv D 0).
   - eapply (Trans_PrmsTyping_mut3 fenv D (S n)).   
     * eapply (ExpTrans_Val fenv D (S n)).
     * eapply (ExpTrans_Var fenv D (S n)).
     * eapply (ExpTrans_BindN fenv D (S n)).
     * eapply (ExpTrans_BindS fenv D (S n)). 
     * eapply (ExpTrans_BindMS fenv D (S n)).
     * eapply (ExpTrans_IfThenElse fenv D (S n)).
     * eapply (ExpTrans_ApplyE fenv D n).
       eapply (Prms2ExpIH fenv D).
       assumption.
     * eapply (Convert_Trans_Call fenv D n (ExpTrans_CallX fenv D n)).
       eapply (Prms2ExpIH fenv D).
       assumption.
     * eapply (ExpTrans_Modify fenv D (S n)).
     * eapply (ExpTrans_PrmsNil fenv D (S n)).
     * eapply (ExpTrans_Prms fenv D (S n)). 
Defined.   


End Reflect.

