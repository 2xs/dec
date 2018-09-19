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

Import ListNotations.


Module PreRefl (IdT: ModTyp) <: ModTyp.

Module DetermL := Determ IdT.
Export DetermL.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.


Open Scope type_scope.

(* extends the shallow environment *)
Lemma ext_senv (tenv : valTC)
      (X : tlist2type (map sVTyp (map snd tenv))) (x: Id) (t: VTyp)
      (sv : sVTyp t) :
       valTC_Trans ((x, t) :: tenv).
   unfold valTC_Trans.
   simpl.
   constructor.
   exact sv.
   exact X.
Defined.

(* extract values of x from senv *)
Lemma ExpDenotI_Var 
  (ftenv : funTC)
  (tenv : valTC)
  (x : Id)
  (t : VTyp)
  (i :  IdTyping tenv x t) :
  (* sfenv *) tlist2type (map snd (FunTC_ListTrans ftenv)) ->
  (* senv *) valTC_Trans tenv -> MM WW (sVTyp t).
  intros.
  assert (sVTyp t).
  eapply (extract_from_valTC_TransB tenv X0 x).
  auto.
  unfold MM.
  intro X2.
  exact (X1,X2).
Defined.  

(* extract values of x from senv; 
   replaces ExpDenotI_Var *)
Lemma ExpDenI_Var 
  (tenv : valTC)
  (x : Id)
  (t : VTyp)
  (i :  IdTyping tenv x t) :
               (* senv: *) valTC_Trans tenv ->
               MM WW (sVTyp t).
  intros.
  assert (sVTyp t).
  eapply (extract_from_valTC_TransB tenv X x).
  auto.
  unfold MM.
  intro X1.
  exact (X0,X1).
Defined.  

Lemma ExpDenI2_Var 
  (tenv : valTC)
  (x : Id)
  (t : VTyp)
  (i :  IdTyping tenv x t) (n: nat) :
               valTC_Trans tenv ->
               W -> (sVTyp t * W) * (sigT (fun n0 => n0 <= n)).
  intros.
  assert (sVTyp t).
  eapply (extract_from_valTC_TransB tenv X x).
  auto.
  split.
  exact (X1,X0).
  econstructor 1 with (x:=n).
  auto.
Defined.  

Lemma ExpTransAux1_Var 
    (x : Id)
    (v : Value) 
    (t : VTyp) (mB: valueVTyp v = t)
    (n0 : nat) (s0 : W) :
              (sVTyp t * W) * (sigT (fun n => n <= n0)).
  unfold valueVTyp in mB.
  destruct v.
  rewrite <- mB. 
  simpl.
  destruct v.
  split.
  exact (v, s0).
  econstructor 1 with (x:= n0).
  auto.
Defined.

Lemma ExpTransAux2_Var
      (tenv: valTC) (env: valEnv)
      (m: EnvTyping env tenv)
      (x : Id)
      (t : VTyp)
      (i : IdTyping tenv x t) 
      (n0 : nat) (s0 : W) :
              (sVTyp t * W) * (sigT (fun n => n <= n0)).
  eapply (ExpTransAux1_Var x
                           (ExtRelVal2A_1 valueVTyp tenv env x t m i)
                           t           
                           (ExtRelVal2A_4 valueVTyp tenv env x t m i)
                           n0 s0).
Defined.


(*******************************************************************)

Definition ExpTrans1_def :=   
   fun (ftenv: funTC) (tenv: valTC) (e: Exp) (t: VTyp) 
       (k: ExpTyping ftenv tenv e t) => 
     forall (sfenv: nat -> tlist2type (map snd (FunTC_ListTrans ftenv))),  
      (valTC_Trans tenv -> MM WW (sVTyp t)).     

Definition PrmsTrans1_def :=   
   fun (ftenv: funTC) (tenv: valTC) (ps: Prms) (pt: PTyp) 
       (k: PrmsTyping ftenv tenv ps pt) =>        
     forall (sfenv: nat -> tlist2type (map snd (FunTC_ListTrans ftenv))),
      (valTC_Trans tenv -> MM WW (PTyp_Trans pt)).


Definition Trans_ExpTyping_mut1 :=
  ExpTyping_mut ExpTrans1_def PrmsTrans1_def. 

Definition Trans_PrmsTyping_mut1 :=
  PrmsTyping_mut ExpTrans1_def PrmsTrans1_def.

  
Lemma ExpDenotK_Var :
  forall (ftenv : funTC) (tenv : valTC) (x : StaticSemL.Id) 
    (t : VTyp) (i : IdTyping tenv x t),
  ExpTrans1_def ftenv tenv (Var x) t (Var_Typing ftenv tenv x t i).
     unfold ExpTrans1_def.
     intros.
     eapply ExpDenI_Var.
     exact i.
     exact X.
Defined.


Program Fixpoint ExpTrans (ftenv: funTC) (tenv: valTC) (e: Exp) (t: VTyp) 
       (k: ExpTyping ftenv tenv e t) :
  forall (sfenv: nat -> tlist2type (map snd (FunTC_ListTrans ftenv))),      
      (valTC_Trans tenv -> MM WW (sVTyp t)) := _    
with PrmsTrans (ftenv: funTC) (tenv: valTC) (ps: Prms) (pt: PTyp) 
       (k: PrmsTyping ftenv tenv ps pt) :        
  forall (sfenv: nat -> tlist2type (map snd (FunTC_ListTrans ftenv))),       
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
     eapply ExpDenI_Var.
     exact i.
     exact X.
   - unfold ExpTrans1_def.
     intros.
     exact (bind (X sfenv X1) (fun _ => X0 sfenv X1)).
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
     specialize (X0 (ext_senv tenv X1 x t1 sv1)).
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
     set (w2 := (s1, min nn n1)). 
     specialize (X sfenv X1).
     assert (FTyp_Trans2 (FT pt t)).
     eapply extract_from_funTC_Trans with
         (sftenv:=(FunTC_ListTrans ftenv)) (ftenv:=ftenv) (x:=x).
     exact (sfenv (snd w2)).
     inversion i; subst.
     reflexivity.
     reflexivity.
     unfold FTyp_Trans2 in X0.
     unfold FType_mk2 in X0.
     simpl in X0.
     destruct pt.
     unfold PTyp_Trans in X.
     unfold VTList_Trans in X.
     unfold PTyp_ListTrans in X0.
     exact (bind X X0 w2).
   - unfold ExpTrans1_def, PrmsTrans1_def.
     intros.
     unfold MM.
     intro w0.
     specialize (X sfenv X0).
     assert (FTyp_Trans2 (FT pt t)).
     eapply extract_from_funTC_Trans with
         (sftenv:=(FunTC_ListTrans ftenv)) (ftenv:=ftenv) (x:=x).
     exact (sfenv (snd w0)).
     inversion i; subst.
     reflexivity.
     reflexivity.
     unfold FTyp_Trans2 in X1.
     unfold FType_mk2 in X1.
     simpl in X1.
     destruct pt.
     unfold PTyp_Trans in X.
     unfold VTList_Trans in X.
     unfold PTyp_ListTrans in X1.
     exact (bind X X1 w0).
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
     eapply ExpDenI_Var.
     exact i.
     exact X.
   - unfold ExpTrans1_def.
     intros.
     exact (bind (X sfenv X1) (fun _ => X0 sfenv X1)).
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
     specialize (X0 (ext_senv tenv X1 x t1 sv1)).
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
     set (w2 := (s1, min nn n1)). 
     specialize (X sfenv X1).
     assert (FTyp_Trans2 (FT pt t)).
     eapply extract_from_funTC_Trans with
         (sftenv:=(FunTC_ListTrans ftenv)) (ftenv:=ftenv) (x:=x).
     exact (sfenv (snd w2)).
     inversion i; subst.
     reflexivity.
     reflexivity.
     unfold FTyp_Trans2 in X0.
     unfold FType_mk2 in X0.
     simpl in X0.
     destruct pt.
     unfold PTyp_Trans in X.
     unfold VTList_Trans in X.
     unfold PTyp_ListTrans in X0.
     exact (bind X X0 w2).
   - unfold ExpTrans1_def, PrmsTrans1_def.
     intros.
     unfold MM.
     intro w0.
     specialize (X sfenv X0).
     assert (FTyp_Trans2 (FT pt t)).
     eapply extract_from_funTC_Trans with
         (sftenv:=(FunTC_ListTrans ftenv)) (ftenv:=ftenv) (x:=x).
     exact (sfenv (snd w0)).
     inversion i; subst.
     reflexivity.
     reflexivity.
     unfold FTyp_Trans2 in X1.
     unfold FType_mk2 in X1.
     simpl in X1.
     destruct pt.
     unfold PTyp_Trans in X.
     unfold VTList_Trans in X.
     unfold PTyp_ListTrans in X1.
     exact (bind X X1 w0).
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


(**********************************************************************)

(* translation of d-function base case *)
Program Definition preZero0 (f: Fun) :
   (* FunWT1 ftenv f ->*) FunTyp_TRN f := _.

Next Obligation.
  intros.
  destruct f.
  unfold FunTyp_TRN.
  unfold FTyp_TRN2.
  unfold FType_mk2.
  simpl.
  intros.
  exact (ret (sValue v)).
Defined.



Definition preZero (f: Fun) : FunTyp_TRN f :=
match f as f0 return (FunTyp_TRN f0) with
 | FC tenv v e =>
     fun _ : tlist2type (map sVTyp (map snd tenv)) => ret (sValue v)
end.  


(* translation of fenv base case *)
Program Definition ZeroTRN1 (fenv: funEnv) :
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
  split.
  eapply preZero.
  exact IHfenv.
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

(* translation of fenv base case *)
Program Definition ZeroTRN2 (fenv: funEnv) :
  tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) := _.
Next Obligation.
  intro fenv.
  induction fenv.
  intros.
  simpl.
  exact tt.
  intros.
  destruct a.
  simpl in *.
  split.
  eapply preZero.
  exact IHfenv.
Defined.
  

Program Definition ZeroTRN3 (fenv: funEnv) :
  tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) := _.
Next Obligation.
  intros.
  rewrite <- FunEnv_Trans_lemma.
  eapply ZeroTRN1.
Defined.

(* 
NOTE: proved AFTER the translation lemma (ExpTrans). 
In contrast, the extract_from_... lemmas are proven beforehand.
ZeroTRN1 used for the base case; then proved
tlist2type (map snd (FunEnv_ListTrans fenv)) =
  tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv)))
 *)
Program Definition preSucc (fenv: funEnv)        
        (k: FEnvWT fenv) (x: Id) (f: Fun) :
  findE fenv x = Some f -> 
  forall (sfenv: nat -> tlist2type
                   (map snd (FunTC_ListTrans (funEnv2funTC fenv)))), 
  FunTyp_TRN f := _.
Next Obligation.
  intros.
  set (tenv := funValTC f).
  set (e := funSExp f).
  set (t := funVTyp f).
  set (ftenv := funEnv2funTC fenv).
  assert (ExpTyping ftenv tenv e t) as k1.
  unfold FEnvWT in k.
  set (sftenv := FunTC_ListTrans ftenv).
  assert (FEnvTyping fenv ftenv).
  constructor.
  specialize (k ftenv H0 x f H).
  unfold FunWT in k.
  destruct f.
  subst e.
  subst t.
  subst tenv.
  simpl in *.
  exact k.
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
  forall (sfenv: nat -> tlist2type
                   (map snd (FunTC_ListTrans (funEnv2funTC fenv))))
         (x: Id) (f: Fun),
  findE fenv x = Some f ->     
  FunTyp_TRN f := _.
Next Obligation.
  intros.
  eapply (preSucc fenv k x f H sfenv).
Defined.
  

(* 
If each function definition in fenv can be translated, then 
each subset of fenv can be translated. 
Here X stands for the call to preSucc.
Essential the use of noDup (used by in_find_lemma)
*)
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
  intro.
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


Fixpoint FunEnvTRN (fenv: funEnv)        
        (k1: FEnvWT fenv) (k2: noDup fenv) (n: nat) :
  tlist2type (map snd (FunTC_ListTrans (funEnv2funTC fenv))) := match n with
          | 0 => ZeroTRN3 fenv 
          | S m => SuccTRN fenv k1 k2
                           (FunEnvTRN fenv k1 k2 m)
          end.                 

Definition ExpTrans2 (ftenv: funTC) (tenv: valTC)
        (e: Exp) (t: VTyp) 
        (k: ExpTyping ftenv tenv e t) :
  forall (sfenv: nat -> tlist2type (map snd (FunTC_ListTrans ftenv))),
    (valTC_Trans tenv) -> MM WW (sVTyp t) := fun sfenv =>
  ExpTrans ftenv tenv e t k sfenv.     

Definition PrmsTrans2 (ftenv: funTC) (tenv: valTC)
        (ps: Prms) (pt: PTyp) 
        (k: PrmsTyping ftenv tenv ps pt) :
  forall (sfenv: nat -> tlist2type (map snd (FunTC_ListTrans ftenv))),
    (valTC_Trans tenv) -> MM WW (PTyp_Trans pt) := fun sfenv =>
  PrmsTrans ftenv tenv ps pt k sfenv.     

  
Definition ExpEvalTRN (fenv: funEnv)        
           (k1: FEnvWT fenv) (k2: noDup fenv)
           (env: valEnv) (e: Exp) (t: VTyp) 
  (k: ExpTyping (funEnv2funTC fenv) (valEnv2valTC env) e t) :
  MM WW (sVTyp t) := fun w =>
  let senv := ValEnvTRN env in
  let sfenv := FunEnvTRN fenv k1 k2 in
  ExpTrans2 (funEnv2funTC fenv) (valEnv2valTC env) e t k sfenv senv w.

Definition PrmsEvalTRN (fenv: funEnv)        
           (k1: FEnvWT fenv) (k2: noDup fenv)
           (env: valEnv) (ps: Prms) (pt: PTyp) 
  (k: PrmsTyping (funEnv2funTC fenv) (valEnv2valTC env) ps pt) :
  MM WW (PTyp_Trans pt) := fun w =>   
  let senv := ValEnvTRN env in
  let sfenv := FunEnvTRN fenv k1 k2 in
  PrmsTrans2 (funEnv2funTC fenv) (valEnv2valTC env) ps pt k sfenv senv w.



(**************************************************************************)
(**************************************************************************)

(* IMPORTANT *)

Lemma ExtRelVal2A_ok (env: valEnv)
    (x: Id) (t: VTyp) (v: Value) 
    (k1: findE (valEnv2valTC env) x = Some t)
    (k2: findE env x = Some v) :
  v = proj1_of_sigT2 (ExtRelVal2A valueVTyp (valEnv2valTC env) env x t
                                  eq_refl k1).
  induction env.
  inversion k1.
  destruct a.
  simpl in k1, k2.
  simpl.
  unfold ExtRelVal2A.
  unfold proj1_of_sigT2.
  unfold sigT_of_sigT2.
  simpl.
  destruct (IdT.IdEqDec x i).
  inversion k2; subst.
  reflexivity.
  specialize (IHenv k1 k2).
  rewrite IHenv.
  reflexivity.
Defined.

Lemma ExtRelVal2A2_ok (env: valEnv) (tenv: valTC)
    (m: EnvTyping env tenv)  
    (x: Id) (t: VTyp) (v: Value) 
    (k1: findE tenv x = Some t)
    (k2: findE env x = Some v) :
  v = proj1_of_sigT2 (ExtRelVal2A valueVTyp tenv env x t
                                  m k1).
  unfold EnvTyping in m.
  unfold MatchEnvs in m.
  inversion m; subst.
  induction env.
  inversion k2.
  destruct a.
  simpl in k1, k2.
  simpl.
  unfold ExtRelVal2A.
  unfold proj1_of_sigT2.
  unfold sigT_of_sigT2.
  simpl.
  destruct (IdT.IdEqDec x i).
  inversion k2; subst.
  reflexivity.
  specialize (IHenv k1 k2).
  rewrite IHenv.
  reflexivity.
  reflexivity.
Defined.


Lemma ExtRelVal2A_Typ_ok (env: valEnv)
    (x: Id) (t: VTyp) (v: Value) 
    (k1: findE (valEnv2valTC env) x = Some t)
    (k2: findE env x = Some v) :
    sVTyp (projT1
       (proj1_of_sigT2
          (ExtRelVal2A valueVTyp (valEnv2valTC env) env x t eq_refl k1))) =
    (sVTyp (projT1 v)).
  rewrite (ExtRelVal2A_ok env x t v k1 k2).
  reflexivity.
Defined.  

Lemma ExtRelVal2A_TypSym_ok (env: valEnv)
    (x: Id) (t: VTyp) (v: Value) 
    (k1: findE (valEnv2valTC env) x = Some t)
    (k2: findE env x = Some v) :
  (sVTyp (projT1 v)) =
      sVTyp (projT1
       (proj1_of_sigT2
          (ExtRelVal2A valueVTyp (valEnv2valTC env) env x t eq_refl k1))).
  symmetry.
  eapply (ExtRelVal2A_Typ_ok env x t v k1 k2).
Defined.  

Lemma ExtRelVal2A2_Typ_ok (env: valEnv) (tenv: valTC)
    (m: EnvTyping env tenv)  
    (x: Id) (t: VTyp) (v: Value) 
    (k1: findE tenv x = Some t)
    (k2: findE env x = Some v) :
  (sVTyp (projT1 v)) =
      sVTyp (projT1
       (proj1_of_sigT2
          (ExtRelVal2A valueVTyp tenv env x t m k1))).
  rewrite (ExtRelVal2A2_ok env tenv m x t v k1 k2).
  reflexivity.
Defined.  

Lemma ExtRelVal2A2_TypSym_ok (env: valEnv) (tenv: valTC)
    (m: EnvTyping env tenv)  
    (x: Id) (t: VTyp) (v: Value) 
    (k1: findE tenv x = Some t)
    (k2: findE env x = Some v) :
    sVTyp (projT1
       (proj1_of_sigT2
          (ExtRelVal2A valueVTyp tenv env x t m k1))) =
    (sVTyp (projT1 v)).
  rewrite (ExtRelVal2A2_ok env tenv m x t v k1 k2).
  reflexivity.
Defined.  


Lemma ExtRelVal_aux1 (env : list (LangSpecL.Id * Value))
  (x : Id)
  (t : VTyp)
  (v : sVTyp t)
  (k2 : findE env x = Some (existT ValueI t (Cst t v)))
  (k1 : findE (valEnv2valTC env) x = Some t)
  (H : existT ValueI t (Cst t v) =
       (let (a, _, _) := ExtRelVal2B env x t k1 in a))  :
  ExtRelVal2B_Typ_ok env x t (existT ValueI t (Cst t v)) k1 k2 =
  
    eq_ind_r
      (fun v0 : Value =>
       sVTyp (projT1 v0) =
       sVTyp (projT1 (proj1_of_sigT2 (ExtRelVal2B env x t k1)))) eq_refl
      (eq_ind_r
         (fun v0 : Value =>
          v0 =
          (let (a, _, _) :=
             list_rect
               (fun env0 : list (LangSpecL.Id * Value) =>
                findE (valEnv2valTC env0) x = Some t ->
                {v1 : Value & findE env0 x = Some v1 & projT1 v1 = t})
               (fun H0 : None = Some t =>
                False_rect {v1 : Value & None = Some v1 & projT1 v1 = t}
                  (eq_ind None
                     (fun e : option VTyp =>
                      match e with
                      | Some _ => False
                      | None => True
                      end) I (Some t) H0))
               (fun (a : LangSpecL.Id * Value)
                  (env0 : list (LangSpecL.Id * Value))
                  (IHenv : findE (valEnv2valTC env0) x = Some t ->
                           {v1 : Value & findE env0 x = Some v1 &
                           projT1 v1 = t}) =>
                let
                  (i, v1) as p
                   return
                     ((if IdT.IdEqDec x (fst p)
                       then Some (valueVTyp (snd p))
                       else findE (valEnv2valTC env0) x) = 
                      Some t ->
                      {v1 : Value &
                      (let (k', x0) := p in
                       if IdT.IdEqDec x k' then Some x0 else findE env0 x) =
                      Some v1 & projT1 v1 = t}) := a in
                if IdT.IdEqDec x i as s
                 return
                   ((if s
                     then Some (valueVTyp v1)
                     else findE (valEnv2valTC env0) x) = 
                    Some t ->
                    {v2 : Value &
                    (if s then Some v1 else findE env0 x) = Some v2 &
                    projT1 v2 = t})
                then
                 fun H0 : Some (valueVTyp v1) = Some t =>
                 existT2 (fun v2 : Value => Some v1 = Some v2)
                   (fun v2 : Value => projT1 v2 = t) v1 eq_refl
                   (f_equal
                      (fun e0 : option VTyp =>
                       match e0 with
                       | Some v2 => v2
                       | None => let (a0, _) := v1 in a0
                       end) H0)
                else fun H0 : findE (valEnv2valTC env0) x = Some t => IHenv H0)
               env k1 in
           a)) eq_refl
         (ExtRelVal2B_ok env x t (existT ValueI t (Cst t v)) k1 k2)).
  unfold eq_ind_r.
  unfold eq_ind.
  unfold eq_sym at 1.
 
  simpl.
  eapply proof_irrelevance.
Defined.

(* DEPTYP main idea: replace the equality parameter, and work through
by simplifing the equality proof-term *)
Lemma ExtRelVal2B_ok2 (env: valEnv)
    (x: Id) (t: VTyp) (v: Value) 
    (k1: findE (valEnv2valTC env) x = Some t)
    (k2: findE env x = Some v)
    (te: (sVTyp (projT1 v)) = sVTyp (projT1
                            (proj1_of_sigT2 (ExtRelVal2B env x t k1)))) 
  :  sValue (proj1_of_sigT2 (ExtRelVal2B env x t k1)) =
     match te with
          eq_refl => sValue v
     end.
  replace te with (ExtRelVal2B_Typ_ok env x t v k1 k2).
  Focus 2.
  eapply proof_irrelevance.
  clear te.
  assert ( v = proj1_of_sigT2 (ExtRelVal2B env x t k1)).
  eapply ExtRelVal2B_ok.
  exact k2.
  destruct v.
  destruct v.
  assert (x0 = t).
  clear H.
  eapply RelatedByEnv with (f:= valueVTyp) (env1:=env)
                           (v1:= (existT ValueI x0 (Cst x0 v))) in k1.
  simpl in k1.
  exact k1.
  constructor.
  exact k2.
  inversion H0; subst.
  clear H1.
  unfold proj1_of_sigT2 in H.
  simpl in H.
  revert H.
  generalize k1.
  generalize (ExtRelVal2B env x t k1).
  clear k1.
  induction env.
  inversion k2.
  simpl in k2.
  destruct a.

  unfold ExtRelVal2B_Typ_ok.
  simpl.

  destruct (IdT.IdEqDec x i).
  
  inversion e; subst.
  clear H.
  inversion k2; subst.
  dependent destruction k2.
  simpl in *.
  intros.
  unfold sValue.
  unfold sValueI.
  unfold proj1_of_sigT2.
  unfold sigT_of_sigT2.
  simpl.
  reflexivity.

  intros.
  specialize (IHenv k2 X k1 H).

  rewrite IHenv.
  clear IHenv.

  clear X.
  clear n.
  clear i.
  clear v0.

  assert (sValue (existT ValueI t (Cst t v)) = v) as E1. 
  unfold sValue.
  unfold sValueI.
  simpl.
  reflexivity.

  rewrite E1.
  clear E1.

  rewrite ExtRelVal_aux1.
  reflexivity.
  exact H.
Defined.

Lemma depeq_sym {T1 T2: Type} (te: T2 = T1) (x1: T1) (x2: T2)
        (p: x1 = match te with eq_refl => x2 end) :
   x2 = match (eq_sym te) with eq_refl => x1 end. 
    rewrite p.
    unfold eq_sym.
    dependent destruction te.
    reflexivity.
Defined.    


Lemma ExtRelVal2B_ok1 (env: valEnv)
    (x: Id) (t: VTyp) (v: Value) 
    (k1: findE (valEnv2valTC env) x = Some t)
    (k2: findE env x = Some v)
    (te: sVTyp (projT1 (proj1_of_sigT2 (ExtRelVal2B env x t k1))) =
         (sVTyp (projT1 v))) 
  : sValue v = match te with
      eq_refl => sValue (proj1_of_sigT2 (ExtRelVal2B env x t k1))
               end.
  replace te with (eq_sym (ExtRelVal2B_Typ_ok env x t v k1 k2)).
  Focus 2.
  eapply proof_irrelevance.
  eapply depeq_sym.
  eapply ExtRelVal2B_ok2.
  exact k2.
Defined.  


End PreRefl.

