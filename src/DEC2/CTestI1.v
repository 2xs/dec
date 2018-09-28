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

Require Import ModNat1I1.

Add LoadPath "~/lib/CompCert-3.0.1" as compcert. 

Require Import CTransI1.
Require Import String.


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

Module CTest (IdT: ModTyp) <: ModTyp.

Module CTestL := CTrans ModNat1.
Export CTestL.

Definition Id := CTestL.Id.
Definition IdEqDec := CTestL.IdEqDec.
Definition IdEq := CTestL.IdEq.
Definition W := CTestL.W.
Definition BInit := CTestL.BInit.
Definition WP := CTestL.WP.

Open Scope type_scope.


(************ TEST ******************)


Lemma FEnvWT_nil : FEnvWT nil.
  unfold FEnvWT.
  intros.
  inversion H0.
Defined.
  
Lemma noDup_nil : @noDup Id Value nil.
  unfold noDup.
  econstructor.
Defined.  

Definition transTest_nil := TopLevel0 nil nil FEnvWT_nil noDup_nil.

Eval compute in transTest_nil.                                  

(******************************************************************)

Definition exp1 : Exp := (Val (cst Nat (2%nat))).

Lemma ExpTyping_exp1 : ExpTyping nil nil exp1 Nat.
repeat econstructor.
Defined.

Lemma allowed_Nat : Allowed Nat.
repeat econstructor.
Defined.

Lemma ExtCAgree_nil : ExtCAgree nil nil.
econstructor.
Defined.  

Definition test_exp1 := Exp2CC nil nil nil exp1 Nat
                          ExpTyping_exp1 nil ExtCAgree_nil nil.

Eval compute in test_exp1.

Definition val1 := (Vint
             {|
             Int.intval := 1;
             Int.intrange := Make32.Z_mod_modulus_range' 1 |}).

Definition typ1 := (Tint I32 Unsigned
                         {| attr_volatile := false; attr_alignas := None |}).

Definition val1a := (Vint
             {|
             Int.intval := 2;
             Int.intrange := Make32.Z_mod_modulus_range' 2 |}).


Definition cexp1 := Csyntax.Eval val1 typ1.
Definition cexp1a := Csyntax.Eval val1a typ1.

Definition cexp2 := Ecomma cexp1 cexp1a typ1.
                                                                            
Definition exp2 := (BindN (Val (cst Nat (1%nat)))
                                      (Val (cst Nat (2%nat)))).

Lemma ExpTyping_exp2 : ExpTyping nil nil exp2 Nat.
  repeat econstructor.
Defined.

Definition test_exp2 := Exp2CC nil nil nil exp2 Nat
                         ExpTyping_exp2 nil ExtCAgree_nil nil.

Eval compute in test_exp2.

Definition exp3 := (BindN (Val (cst Nat (3%nat))) exp2).

Lemma ExpTyping_exp3 : ExpTyping nil nil exp3 Nat.
  repeat econstructor.
Defined.

Definition test_exp3 := Exp2CC nil nil nil exp3 Nat
                         ExpTyping_exp3 nil ExtCAgree_nil nil.

Eval compute in test_exp3.


Definition fun1 : Fun := FC nil (cst Nat (0%nat)) exp3.

Lemma FEnvWT_fun1 (x: Id) : FEnvWT ([(x, fun1)]).
  unfold FEnvWT, FunWT, fun1.
  intros.
  destruct f.
  simpl in *.
  destruct (ModNat1.IdEqDec x0 x).
  inversion e0; subst.
  inversion H0; subst.
  simpl in *.
  repeat econstructor.
  inversion H0.
Defined.  


Definition cv : string -> Id := id.

Lemma FEnvWT_fun1a : FEnvWT ([(cv "x", fun1)]).
  eapply FEnvWT_fun1.
Defined.  

Lemma noDup_fun1 (x: Id) : noDup ([(x, fun1)]).
  unfold noDup.
  econstructor.
  auto.
  econstructor.
Defined.

Lemma noDup_fun1a : noDup ([(cv "x", fun1)]).
  eapply noDup_fun1.
Defined.  

Definition test_fun1 := TopLevel0 nil ([(cv "x", fun1)])
                                  FEnvWT_fun1a noDup_fun1a.

Eval native_compute in test_fun1.

Definition exp4 := (BindS (cv "y") (Some Nat) exp3
                                              (Var (cv "y"))).

Lemma ExpTyping_exp4 : ExpTyping nil nil exp4 Nat.
  repeat econstructor.
Defined.

Definition test_exp4 := Exp2CC nil nil nil exp4 Nat
                         ExpTyping_exp4 nil ExtCAgree_nil nil.

Eval compute in test_exp4.

Definition exp5 := (BindS (cv "z") (Some Nat) exp4
                                              (BindN (Var (cv "z")) exp4)).

Lemma ExpTyping_exp5 : ExpTyping nil nil exp5 Nat.
  repeat econstructor.
Defined.

Definition test_exp5 := Exp2CC nil nil nil exp5 Nat
                         ExpTyping_exp5 nil ExtCAgree_nil nil.

Eval compute in test_exp5.

Definition exp6 := (BindN (Val (cst Nat (1%nat))) (Val (cst Bool (true)))).

Lemma ExpTyping_exp6 : ExpTyping nil nil exp6 Bool.
  repeat econstructor.
Defined.

Definition test_exp6 := Exp2CC nil nil nil exp6 Bool
                         ExpTyping_exp6 nil ExtCAgree_nil nil.

Eval compute in test_exp6.

Definition exp7 := IfThenElse exp6 exp5 exp4.

Lemma ExpTyping_exp7 : ExpTyping nil nil exp7 Nat.
  repeat econstructor.
Defined.

Definition test_exp7 := Exp2CC nil nil nil exp7 Nat
                         ExpTyping_exp7 nil ExtCAgree_nil nil.

Eval compute in test_exp7.


Definition fun2 : Fun := FC nil (cst Nat (0%nat))
                             (Call (cv "f3") (PS [(Val (cst Nat (4%nat)))])).

Definition fun3 : Fun := FC [(cv "x", Nat)] (cst Nat (0%nat))
                             (Call (cv "f2") (PS [])).

Definition funEnv23 : funEnv := [(cv "f2", fun2); (cv "f3", fun3)].

Definition funTC23 : funTC := [(cv "f2", funFTyp fun2);
                                (cv "f3", funFTyp fun3)].


Lemma noDup_fun23 : noDup funEnv23.
  econstructor.
  simpl.
  intuition.
  inversion H0.
  econstructor.
  intuition.
  econstructor.
Defined.  
  
Lemma FEnvWT_fun23 : FEnvWT funEnv23.
  unfold FEnvWT, FunWT, funEnv23, fun2, fun3.
  intros.
  unfold FEnvTyping in H.
  unfold MatchEnvs in H.
  unfold thicken in *.
  inversion H; subst.  
  destruct f.
  simpl in *.
  clear H1.
  destruct (ModNat1.IdEqDec x (cv "f2")).
  inversion e0; subst.
  inversion H0; subst.
  simpl in *.
  econstructor.
  instantiate (1:=PT[Nat]).
  unfold IdFTyping.
  unfold EnvrAssign.
  simpl.
  reflexivity.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  destruct (ModNat1.IdEqDec x (cv "f3")).
  inversion e0; subst.
  inversion H0; subst.
  econstructor.
  econstructor.
  econstructor.
  inversion H0.
Defined.  


Definition exp8 : Exp := Call (cv "f3") (PS [exp7]).

Lemma ExpTyping_exp8 : ExpTyping funTC23 nil exp8 Nat.
repeat econstructor.
Defined.

Lemma FunWT_exp8 : FunWT (funEnv2funTC funEnv23)
                         (FC nil (cst Nat (0%nat)) exp8).
  repeat econstructor.
Defined.  


Definition test_top8 := TopLevel 100 nil funEnv23 
                                   FEnvWT_fun23 noDup_fun23
                                   (cst Nat (0%nat))
                                   exp8 FunWT_exp8.

Eval compute in test_top8.


End CTest.

  
