Require Export EnvLibA.
Require Export RelLibA.
Require Export PRelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.
Require Import Bool. 
Require Import Coq.Logic.ProofIrrelevance.

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
Require Import Pip_Prop.
Require Import Pip_DependentTypeLemmas.
Require Import Pip_InternalLemmas.
Require Import Pip_writeVirtualInv_Lemmas.
Require Import Hoare_getFstShadow.
Import ListNotations.

Module Hoare_Test_VirtualInv.

Module VirtualInv := Hoare_Test_FstShadow.
Export VirtualInv.



(**************************************************)

(******* Program *)

(** WriteVirtualInv -page -index -vaddress : writes the vaddress at key (page,index) in memory *)

Definition xf_writeVirtual (p: page) (i: index) (v: vaddr) : XFun unit unit := {|
   b_mod := fun s _ => (writeVirtualInternal p i v s,tt)
|}.

Instance VT_unit : ValTyp unit.

Definition WriteVirtual (p: page) (i: index) (v: vaddr) : Exp :=
  Modify unit unit VT_unit VT_unit (xf_writeVirtual p i v) (QV (cst unit tt)).  


(******* Useful Lemmas *)

Lemma writeVirtualWp  table idx (addr : vaddr)  (P : Value -> state -> Prop) (fenv: funEnv) (env: valEnv) :
{{fun  s => P (cst unit tt) {| currentPartition := currentPartition s;
  memory := add table idx (VA addr) (memory s) beqPage beqIndex |} }} 
fenv >> env >> WriteVirtual table idx addr  {{P}}.
Proof.
unfold THoareTriple_Eval.
intros. 
inversion X;subst.
inversion X0;subst.
repeat apply inj_pair2 in H6.
repeat apply inj_pair2 in H8.
subst.
unfold xf_writeVirtual, b_eval, b_exec, b_mod in *.
simpl in *.
inversion X1;subst.
auto.
inversion X2.
inversion X2.
Qed.

(******* Hoare Triple *)

Lemma writeVirtualInvNewProp (p : page) (i:index) (v:vaddr) (fenv: funEnv) (env: valEnv) :
{{fun _ => True}}
fenv >> env >> WriteVirtual p i v
{{fun _ s => readVirtualInternal p i s.(memory) =  Some v}}.
Proof.
unfold THoareTriple_Eval.
intros.
clear H k3 t k2 k1 tenv ftenv.
inversion X;subst.
inversion X0;subst.
repeat apply inj_pair2 in H5.
apply inj_pair2 in H7.
subst.
unfold b_eval, b_exec, xf_writeVirtual, b_mod in *.
simpl in *.
inversion X1;subst.
unfold writeVirtualInternal.
simpl.
unfold add.
unfold readVirtualInternal.
simpl.
specialize beqPairsTrue with p i p i.
intros.
intuition.
rewrite H.
reflexivity.
inversion X2.
inversion X2.
Qed.

Lemma writeVirtualInv (vaInCurrentPartition vaChild: vaddr)  currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart idxvaInCurPart
vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1
presentDescPhy phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild phyVaChild 
sh2Childphy ptVaChildsh2 level (fenv: funEnv) (env: valEnv) :
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
negb presentDescPhy = false -> 
{{ fun s : state => propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart idxvaInCurPart
vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1
presentDescPhy phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild phyVaChild 
sh2Childphy ptVaChildsh2 level }} 
  fenv >> env >> WriteVirtual ptVaChildsh2 idxvaChild vaInCurrentPartition 
  {{ fun _ s => propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart idxvaInCurPart
vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1
presentDescPhy phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild phyVaChild 
sh2Childphy ptVaChildsh2 level /\ 
readVirtualInternal ptVaChildsh2 idxvaChild s.(memory) = Some vaInCurrentPartition }}.
Proof.
intros.
eapply weakenEval.
eapply writeVirtualWp.
simpl; intros.
split. 
unfold propagatedPropertiesAddVaddr in *.
assert(Hlookup :exists entry, 
 lookup ptVaChildsh2 idxvaChild (memory s) beqPage beqIndex = Some (VA entry)).
{ assert(Hva : isVA ptVaChildsh2 (getIndexOfAddr vaChild fstLevel) s) by intuition.
  unfold isVA in *.
  assert(Hidx :  getIndexOfAddr vaChild fstLevel = idxvaChild) by intuition.
 clear H.
 subst. 
 destruct(lookup ptVaChildsh2 (getIndexOfAddr vaChild fstLevel)
          (memory s) beqPage beqIndex);intros; try now contradict Hva.
 destruct v; try now contradict Hva.
 do 2 f_equal.
 exists v;trivial. }
 destruct Hlookup as (entry & Hlookup).
intuition try assumption.
(** partitionsIsolation **)
+ apply partitionsIsolationUpdateSh2 with entry;trivial.
(** kernelDataIsolation **)
+ apply kernelDataIsolationUpdateSh2 with entry;trivial.
(** verticalSharing **)
+ apply verticalSharingUpdateSh2 with entry;trivial. 
(** consistency **)
+ apply consistencyUpdateSh2 with
    entry vaChild
    currentPart currentShadow descChild idxDescChild ptDescChild
    ptVaInCurPart idxvaInCurPart vainve isnotderiv currentPD
    ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
    phyDescChild pdChildphy ptVaChildpd presentvaChild phyVaChild
    sh2Childphy level;trivial.
  unfold propagatedPropertiesAddVaddr ;intuition.
(** Propagated properties **)
+ rewrite <- nextEntryIsPPUpdateSh2;trivial.
  exact Hlookup.
+ apply isVEUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply entryPDFlagUpdateSh2 with entry;trivial.
+ apply isVEUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply isEntryVAUpdateSh2 with entry;trivial.
+ rewrite <- nextEntryIsPPUpdateSh2;trivial.
  exact Hlookup.
+ apply isPEUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply entryUserFlagUpdateSh2 with entry;trivial.
+ apply entryPresentFlagUpdateSh2 with entry;trivial.
+ apply isPEUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply entryPresentFlagUpdateSh2 with entry;trivial.
+ apply isEntryPageUpdateSh2  with entry;trivial.
+ assert(Hchildren : forall part, getChildren part
     {|
     currentPartition := currentPartition s;
     memory := add ptVaChildsh2 idxvaChild(VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |} = getChildren part s).
  { intros; symmetry; apply getChildrenUpdateSh2 with entry;trivial. } 
  rewrite Hchildren in *;trivial.
+ rewrite <- nextEntryIsPPUpdateSh2;trivial.
  exact Hlookup.
+ apply isPEUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply entryPresentFlagUpdateSh2 with entry;trivial.
+ apply isEntryPageUpdateSh2  with entry;trivial.
+ rewrite <- nextEntryIsPPUpdateSh2;trivial.
  exact Hlookup.
+ apply isVAUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
(** new property **)
+ unfold readVirtualInternal.
  cbn.
  assert (Htrue : beqPairs (ptVaChildsh2, idxvaChild) (ptVaChildsh2, idxvaChild) beqPage
      beqIndex = true). 
  apply beqPairsTrue;split;trivial.
  rewrite Htrue.
  trivial.
Qed.

End Hoare_Test_VirtualInv.
