(* Paolo Torrini, with Mohamed Sami Cherif 
   Universite' Lille-1 - CRIStAL-CNRS
*)
(* verification of the initVAddrTable invariant, syntax directed version *)

Require Export EnvLibA.
Require Export RelLibA.
Require Export PRelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega Bool Coq.Logic.ProofIrrelevance.
Require Import Coq.Lists.List.

Require Import StaticSemA.
Require Import DynamicSemA.
Require Import TRInductA.
Require Import WeakenA.
Require Import TSoundnessA.
Require Import IdModTypeA.
Require Import IdModPip.
Require Import DetermA.
Require Import AbbrevA.
Require Import HoareA.
Require Import THoareA.
Require Import Lib.
Require Import Pip_state.
Require Import Pip_stateLib.
Require Import Coq.Structures.Equalities.
Require Import Coq.Logic.Eqdep.
Require Import Hoare_getFstShadow.
Require Import Hoare_writeVirtualInv.
Require Import Hoare_initVAddrTable.
Require Import Pip_DependentTypeLemmas.
Require Import Pip_InternalLemmas.
Require Import Pip_Prop.
Import ListNotations.

Module Hoare_Test_SndShadow_SynDir.

Module SndShadowI := Hoare_Test_SndShadow.
Export SndShadowI.

(**************************************************)

Definition initVAddrTableFun (fenv: funEnv)
           (p:page) (n: nat) : Fun :=
        FC fenv
           [("x",Index)]
           (Val (cst unit tt))
           (initVAddrTableAux "initVAddrTable" "x" p)
           "initVAddrTable"
           n.    

Lemma initVAddrTableFun_FunTyping (ftenv: funTC) (fenv: funEnv)
      (k: MatchEnvsT FunTyping fenv ftenv)
      (p:page) (n: nat) :
  FunTyping (initVAddrTableFun fenv p n) (FT [("x",Index)] Unit). 
  induction n.
  econstructor.
  exact k.
  econstructor.
  econstructor.
  reflexivity.
  econstructor.

  econstructor.
  exact k.
  unfold initVAddrTableAux at 2.

  econstructor.
  unfold WriteVirtual'.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  simpl.
  reflexivity.

  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  reflexivity.

  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  reflexivity.

  econstructor.
  econstructor.
  repeat econstructor.

  econstructor.
  reflexivity.
  econstructor.
  assumption.
  assumption.

  econstructor.
  econstructor.
  econstructor.
  econstructor.

  repeat econstructor.
  econstructor.
  econstructor.
  econstructor.
  repeat econstructor.

  econstructor.
  econstructor.
  econstructor.
  simpl.
  reflexivity.

  econstructor.
  econstructor.
  repeat econstructor.
  econstructor.

  reflexivity.
  econstructor.
  assumption.
  assumption.
  econstructor.
  econstructor.
  eassumption.
  instantiate (1:=nil).
  instantiate (1:=nil).
  econstructor.
  exact k.
  simpl.
  auto.
  simpl.
  reflexivity.
  simpl.
  reflexivity.

  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  simpl.
  reflexivity.
  econstructor.
  econstructor.
  repeat econstructor.
  assumption.
Qed.  

         
Definition initVAddrTableR (p:page) (i:index) : Exp := 
Apply
  (QF (initVAddrTableFun nil p tableSize))
  (PS[Val (cst index i)]).


(******* Useful Lemmas *)

Lemma succDWp2 (x:Id) P (fenv: funEnv) (env: valEnv) :
  forall (idx:index), {{fun s => P s  /\ idx < tableSize - 1}}
                        fenv >> (x,(cst index idx))::env >> SuccD x 
  {{fun (idxsuc : Value) (s : state) => P s  /\ idx < tableSize - 1
                /\ idxsuc = cst (option index) (succIndexInternal idx)
                /\ exists i, idxsuc = cst (option index) (Some i)}}.
Proof.
intros.
eapply weakenEval.
eapply succDW.
intros.
simpl.
split.
instantiate (1:=idx).  
intuition.
intros.
intuition.
destruct idx.
exists (CIndex (i + 1)).
f_equal.
unfold succIndexInternal.
case_eq (lt_dec i tableSize).
intros.
auto.
intros.
contradiction.
Qed.


Lemma init_aux1 (table : page)
  (curidx : index)
  (fenv : funEnv)
  (env : valEnv)
  (H : tableSize + curidx >= tableSize) :
  {{fun s : DynamicI.W =>
    forall idx : index,
    idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr
  }}' fenv >> env >> PS [Val (cst index curidx)]
  {{fun (vs : list Value) (s : DynamicI.W) =>
    (forall idx : index,
     idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\
    vs = [cst index curidx] }}'.

unfold THoarePrmsTriple_Eval.
intros.
inversion X;subst.
destruct vs; inversion H6.
destruct vs ; inversion H3 ; subst.
intuition.
inversion X0;subst.
inversion X2.
inversion X2.
Qed.

Lemma init_aux01 (table : page)
  (curidx : index)
  (fenv : funEnv)
  (env : valEnv)
  (idx : index) :
  {{fun s : DynamicI.W =>
    idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr
  }}' fenv >> env >> PS [Val (cst index curidx)]
  {{fun (vs : list Value) (s : DynamicI.W) =>
    (
     idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\
    vs = [cst index curidx] }}'.

unfold THoarePrmsTriple_Eval.
intros.
inversion X; subst.
destruct vs; inversion H5.
destruct vs ; inversion H2 ; subst.
intuition.
inversion X0;subst.
inversion X2.
inversion X2.
Qed.


Lemma init_aux2 (idx: index) :
  idx < CIndex (tableSize - 1) \/ idx = CIndex (tableSize - 1).
      destruct idx. simpl in *. 
      unfold CIndex.
      case_eq (lt_dec (tableSize - 1) tableSize).
      intros. simpl in *.
      assert (i <= tableSize -1).
      omega.
      apply NPeano.Nat.le_lteq in H0.
      destruct H0.
      left. assumption. right.
      subst.
      assert (Hi =  Pip_state.CIndex_obligation_1 (tableSize - 1) l).
      apply proof_irrelevance.
      subst. reflexivity.
      intros.
      intuition.
Qed.      


Lemma init_aux3 (* for the 'false case' *)
 (table : page)
 (curidx : index)
 (fenv : funEnv)
 (env : valEnv)
 (e : Exp)
 (k0 : curidx >= 0)
 (k1 : curidx = CIndex (tableSize - 1)) :  
  {{fun s : DynamicI.W =>
    (forall idx : index,
     idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) 
     /\ readVirtual table curidx (memory s) = Some defaultVAddr  
  }}
    fenv >> env >> Val (cst unit tt) 
  {{fun (_ : Value) (s : DynamicI.W) =>
      forall idx : index, readVirtual table idx (memory s) = Some defaultVAddr
  }}.
intros.
unfold THoareTriple_Eval.
intros.
simpl in *.
assert (idx < CIndex (tableSize - 1) \/ idx = CIndex (tableSize - 1)).
eapply init_aux2.
simpl in *.
inversion X; subst.
Focus 2.
inversion X0. 
destruct H.
destruct H0.
eapply H.
exact H0.
subst.
exact H1.
Qed.


Lemma init_aux5 (table : page)
  (idx : index)
  (curidx : index)
  (fenv : funEnv) :
  {{fun s : DynamicI.W =>
    idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr}} 
  fenv >>
  [("x", cst index curidx)] >> WriteVirtual' table "x" defaultVAddr
  {{fun (_ : Value) (s : state) =>
    (idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\
    readVirtual table curidx (memory s) = Some defaultVAddr}}.
unfold WriteVirtual'.
eapply Modify_VHTT3 with (fenv:= fenv)
                         (env:=[("x", cst index curidx)])
                         (XF:=(xf_writeVirtual' table defaultVAddr))
                         (x:="x").
Unshelve.
Focus 3.
exact curidx.
intros.
simpl.
split.
intros.

unfold readVirtual.
unfold add.
simpl.
assert (Hfalse :
    Lib.beqPairs (table, curidx) (table, idx) beqPage beqIndex = false).
    { apply beqPairsFalse. 
      right.
      apply indexDiffLtb.
      right; assumption. }
rewrite Hfalse at 1.
assert (lookup table idx (Lib.removeDup table curidx (memory s)
                                            beqPage beqIndex)
               beqPage beqIndex =
        Lib.lookup  table idx  (memory s) beqPage beqIndex) as Hmemory.
    { apply removeDupIdentity.
      right. 
      apply indexDiffLtb.
      left; trivial. }
rewrite Hmemory.
apply H in H0.
unfold readVirtual in *.
auto.

unfold writeVirtualInternal.
simpl.
unfold readVirtual.
unfold add.
simpl.
assert (Htrue : Lib.beqPairs (table, curidx) (table, curidx)
                             beqPage beqIndex = true).
    { apply beqPairsTrue.
      intuition. }
rewrite Htrue.
auto.
reflexivity.
Qed.


Lemma init_aux6 (table : page)
  (idx : index)
  (curidx : index)
  (fenv : funEnv) : 
  {{fun s : state =>
    (idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\
    readVirtual table curidx (memory s) = Some defaultVAddr}} 
  fenv >>
  [("x", cst index curidx)] >> LtLtb "x" maxIndex
  {{fun (b : Value) (s : DynamicI.W) =>
    (idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\
    readVirtual table curidx (memory s) = Some defaultVAddr /\
    b = cst bool (Index.ltb curidx maxIndex)}}.
unfold LtLtb.
eapply Modify_VHTT3 with (fenv:= fenv)
                         (env:=[("x", cst index curidx)])
                         (XF:=(xf_Ltb maxIndex))
                         (x:="x").

Unshelve.
Focus 3.
exact curidx.

intros.
destruct H.
split.
intuition.
intuition.
reflexivity.
Qed.


Lemma init_aux7 (table : page)
  (idx : index)
  (curidx : index)
  (fenv : funEnv) :
  {{fun s : DynamicI.W =>
    (idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\
    readVirtual table curidx (memory s) = Some defaultVAddr /\
    cst bool true = cst bool (Index.ltb curidx maxIndex)}}
 fenv >> [("x", cst index curidx)] >> SuccD "x"
  {{(fun (idxsuc : Value) (s : state) =>
    (fun s0 : DynamicI.W =>
     (fun s' : state =>
      (idx < curidx -> readVirtual table idx (memory s') = Some defaultVAddr) /\
      readVirtual table curidx (memory s0) = Some defaultVAddr) s0) s /\
    curidx < tableSize - 1 /\
    idxsuc = cst (option index) (succIndexInternal curidx) /\
    (exists i : index, idxsuc = cst (option index) (Some i)))}}. 
eapply weakenEval.
eapply succDWp2.
simpl;intros; intuition.

unfold maxIndex in H2.
inversion H2.
apply inj_pair2 in H3.
symmetry in H3.
apply indexltbTrue in H3.
unfold CIndex in H3.
destruct (lt_dec (tableSize - 1) tableSize). 
simpl in *.  
assumption.
contradict n.
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
omega.
Qed.

Lemma init_aux8 (table : page)
  (idx : index)
  (curidx : index)
  (fenv : funEnv)
  (v : Value) :
  {{fun s : state =>
    ((idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\
     readVirtual table curidx (memory s) = Some defaultVAddr) /\
    curidx < tableSize - 1 /\
    v = cst (option index) (succIndexInternal curidx) /\
    (exists i : index, v = cst (option index) (Some i))}}
   fenv >>
  [("idx", v);
  ("x", cst index curidx)] >> ExtractIndex "idx"
  {{fun (v0 : Value) (s : DynamicI.W) =>
    (fun (v' : Value) (s0 : W) =>
     ((idx < curidx -> readVirtual table idx (memory s0) = Some defaultVAddr) /\
      readVirtual table curidx (memory s0) = Some defaultVAddr /\
      curidx < tableSize - 1) /\
     v' = cst index (match succIndexInternal curidx with | Some i => i
                                                 | None => index_d end)) v0 s}}.

eapply Hoare_env_subst with (fenv:=fun _ => fenv)
           (env:=fun v => [("idx", v); ("x", cst index curidx)])
           (v2:=cst (option index) (succIndexInternal curidx))
      (P2 := (fun s : state =>
    ((idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\
     readVirtual table curidx (memory s) = Some defaultVAddr) /\
    curidx < tableSize - 1 /\
    (exists i : index,
        cst (option index) (succIndexInternal curidx) =
        cst (option index) (Some i)))).      
intuition.
intuition.
subst.
assumption.

unfold ExtractIndex.

eapply Modify_VHTT3 with (fenv:= fenv)
       (env:= [("idx", cst (option index) (succIndexInternal curidx));
  ("x", cst index curidx)])
                         (XF:=(xf_ExtractIndex))
                         (x:="idx").

Unshelve.
Focus 3.
exact (succIndexInternal curidx).
intros.
destruct H.
destruct H.
destruct H0.
destruct H2.
inversion H2; subst.
repeat apply inj_pair2 in H4.
rewrite H4 in *.

unfold b_eval, b_exec, xf_ExtractIndex, b_mod in *.
simpl in *.

intuition.
reflexivity.
Qed.


Lemma init_aux9 (table : page)
  (idx : index)
  (curidx : index)
  (fenv : funEnv)
  (env : valEnv) :
  {{fun s : DynamicI.W =>
    (idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\
    readVirtual table curidx (memory s) = Some defaultVAddr /\
    cst bool false = cst bool (Index.ltb curidx maxIndex)}} 
  fenv >>
  env >> Val (cst unit tt)
  {{fun (_ : Value) (s : DynamicI.W) =>
    readVirtual table idx (memory s) = Some defaultVAddr}}.

unfold THoareTriple_Eval.
intros.
intuition.
inversion X; subst.
Focus 2.
inversion X0.

clear X.
simpl in *.
inversion H2; subst.
repeat eapply inj_pair2 in H3.
symmetry in H3.
apply indexltbFalse in H3.
apply indexBoundEq in H3.

assert (idx < CIndex (tableSize - 1) \/ idx = CIndex (tableSize - 1)) as H4.
eapply init_aux2.
destruct H4.

subst.
eapply H0.
exact H1.

subst.
assumption.
Qed.
      

Lemma init_aux10 (table : page)
  (idx : index)
  (curidx : index)
  (fenv : funEnv) :
  {{fun s : DynamicI.W =>
    (idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\
    readVirtual table curidx (memory s) = Some defaultVAddr /\
    curidx < tableSize - 1
  }}' fenv >>
  [("y",
   cst index
     match succIndexInternal curidx with
     | Some i => i
     | None => index_d
     end); ("x", cst index curidx)] >> PS [VLift (Var "y")]
  {{fun (vs : list Value) (s : DynamicI.W) =>
    (idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\
    readVirtual table curidx (memory s) = Some defaultVAddr /\
    curidx < tableSize - 1 /\
    vs =
    [cst index
       match succIndexInternal curidx with
       | Some i => i
       | None => index_d
       end] }}'.

unfold VLift.
eapply Prms_VHTT1.

instantiate (1:=fun v s => (
    idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\
   readVirtual table curidx (memory s) = Some defaultVAddr /\
   curidx < tableSize - 1 /\
   v =
   cst index
     match succIndexInternal curidx with
     | Some i => i
     | None => index_d
     end).
unfold THoareTriple_Eval.
intros.
assert ( EClosure
        fenv
        [("y",
         cst index
           match succIndexInternal curidx with
           | Some i => i
           | None => index_d
           end); ("x", cst index curidx)] (Conf Exp s (Return LL (Var "y")))
        (Conf Exp s (Val (cst index
           match succIndexInternal curidx with
           | Some i => i
           | None => index_d
           end))) ) as X2.
econstructor.
econstructor.
econstructor.
econstructor.
reflexivity.
econstructor.
econstructor.
econstructor.
assert ((s' = s) /\ (v = cst index
                  match succIndexInternal curidx with
                  | Some i => i
                  | None => index_d
                  end)).
eapply ExpConfluence.
exact k3.
exact k1.
eauto.
eauto.
eauto.
intuition; subst.
assumption.
assumption.

unfold THoarePrmsTriple_Eval;intros.
intuition.
inversion X; subst.
assumption.
inversion X0.
inversion X; subst.
assumption.
inversion X0.
inversion X; subst.
symmetry in H8.
eapply map_eq_nil in H8.
subst.
auto.
inversion X0.
Qed.


(******* Main Hoare Triple *)

Lemma initVAddrTableNewProperty'
      (table : page) (curidx : index)
      (fenv: funEnv) (env: valEnv) :
{{ fun s => forall idx : index, idx < curidx -> 
                readVirtual table idx (memory s) = Some defaultVAddr }} 
  fenv >> env >> initVAddrTableR table curidx 
{{ fun _ s => forall idx,
                readVirtual table idx (memory s) = Some defaultVAddr }}.
Proof.

eapply THoare_gen.
intro idx.
unfold initVAddrTableR.
assert (tableSize + curidx >= tableSize) as H by omega.
revert fenv env H.
revert curidx.
generalize tableSize at 1 3. 
induction n. simpl. 
(** begin case n=0 *)
intros.
destruct curidx.
simpl in *.
omega.
(** env case n=0 *)
intros; simpl.
assert (curidx < tableSize) as k1.
destruct curidx.
intuition.
(* eapply Apply_VHTT1.*)
HoareTac1.
eapply init_aux01.

simpl in *.
split.
reflexivity.

intro vs.
unfold initVAddrTableAux.
eapply Hoare_val_eq_wk with (fenv:= fun _ => [("initVAddrTable",
                               FC [] [("x", Index)] 
                                 (Val (cst unit tt))
                                 (initVAddrTableAux "initVAddrTable" "x" table)
                                 "initVAddrTable" n)])
                         (env:= mkVEnv [("x", Index)]).
clear vs.
unfold mkVEnv.
simpl.


eapply BindN_VHTT1 with (P1:= fun s => (
     idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\ 
     readVirtual table curidx s.(memory) = Some defaultVAddr).

eapply init_aux5.

(* eapply IfThenElse_VHTT1. *)
HoareTac1.

eapply init_aux6.
simpl.
eapply BindS_VHTT1 with (x:="y").
eapply BindS_VHTT1 with (x:="idx").
eapply init_aux7.

intros; simpl.

eapply init_aux8.

Focus 2.
eapply init_aux9.

intros; simpl.
eapply (Hoare_eq_wk Value) with
    (fenv:= fun _ => [("initVAddrTable",
             FC [] [("x", Index)] (Val (cst unit tt))
               (initVAddrTableAux "initVAddrTable" "x" table) "initVAddrTable"
               n)])
    (env:= fun v => [("y", v); ("x", cst index curidx)])
    (P:= fun s : DynamicI.W =>
    (idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\
    readVirtual table curidx (memory s) = Some defaultVAddr /\
    curidx < tableSize - 1)
    (Q:=fun (_ : Value) (v0 : DynamicI.W) =>
    readVirtual table idx (memory v0) = Some defaultVAddr)
    (vs2:= cst index
      match succIndexInternal curidx with
      | Some i => i
      | None => index_d
      end).
  
eapply QFun_VHTT.
econstructor.

reflexivity.
clear v. 
eapply Apply_VHTT2.

instantiate(1:=fun vs s => (
    idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\
   readVirtual table curidx (memory s) = Some defaultVAddr /\
   curidx < tableSize - 1 /\
   vs =
   [cst index
     match succIndexInternal curidx with
     | Some i => i
     | None => index_d
     end]).

eapply init_aux10.

intros.
simpl in *.
unfold initVAddrTableFun in IHn.

destruct curidx.
simpl in *.

unfold THoareTriple_Eval in *.
intros.
destruct H0.
destruct H1.
destruct H2.
simpl in *.

case_eq (lt_dec i tableSize).
intros; try contradiction.
rewrite H4 in *.
unfold CIndex in *.
case_eq (lt_dec (i + 1) tableSize); intros.
rewrite H5 in *.
simpl in *.
assert (Z : n+(i+1) = S(n+i)) by omega.

specialize (IHn (CIndex(i+1)) [("initVAddrTable",
               FC [] [("x", Index)] (Val (cst unit tt))
                 (initVAddrTableAux "initVAddrTable" "x" table)
                 "initVAddrTable" n)]
               [("y",
        cst index
          {| i := i + 1; Hi := Pip_state.CIndex_obligation_1 (i + 1) l0 |});
       ("x", cst index {| i := i; Hi := Hi |})]).

assert (n + CIndex (i + 1) = S (n + i)) as k4.
unfold CIndex.
rewrite H5.
simpl.
auto.
rewrite k4 in *.
specialize (IHn H).

eapply IHn.
eauto.
eauto.
instantiate (1:=t).
subst.
simpl in *.
unfold CIndex.
rewrite H5.

exact k3.
subst.
unfold CIndex.
rewrite H5.

exact X.

intro.
simpl in *.
assert (Hor : idx = {| i := i; Hi := Hi |} \/ idx < {| i := i; Hi := Hi |}).
    { simpl in *.
      unfold CIndex in H6.
      destruct (lt_dec (i + 1) tableSize).
      subst.
      simpl in *.
      rewrite NPeano.Nat.add_1_r in H6.
      apply lt_n_Sm_le in H6.
      apply le_lt_or_eq in H6.
      destruct H6.
      right. assumption.
      left. subst.
      destruct idx. simpl in *.
      subst. 
      assert (Hi = Hi0).
      apply proof_irrelevance.
      subst. reflexivity. omega. }
destruct Hor.
subst.
eassumption.
apply H0; trivial.
assert (i+1<tableSize) by omega.
contradiction.

intros.
contradiction.
Qed.


End Hoare_Test_SndShadow_SynDir.
