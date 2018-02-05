(** * Summary 
    This file contains required lemmas to help in proving some properties
    on our dependent types defined into [Model.ADT] *)
Require Import Lib Pip_state Pip_stateLib Pip_Prop List.
Require Import Coq.Logic.ProofIrrelevance Omega Bool.

(** ADT : level **)
Lemma levelEqBEqNatTrue :
forall l l' : level, Level.eqb l l' = true -> l = l' .
 Proof.
 intros l l' H.  
 unfold Level.eqb in H. 
 apply beq_nat_true in H.
 destruct l.
 destruct l'. simpl in *.
 subst.
 assert (Hl = Hl0).
 apply proof_irrelevance. subst. intuition.
Qed.

Lemma levelEqBEqNatFalse : 
forall l ,
Level.eqb l fstLevel = false -> l > fstLevel.
Proof.
intros.
unfold Level.eqb in H.
apply beq_nat_false in H.
unfold fstLevel in *.
unfold CLevel in *.
case_eq (lt_dec 0 nbLevel).
intros.
rewrite H0 in *.
simpl in *. omega.
intros.
assert (0 < nbLevel). 
apply nbLevelNotZero.
contradict H1.
intuition. 
Qed. 

Lemma levelEqBEqNatFalse0 : 
forall l ,
Level.eqb l fstLevel = false -> l > 0.
Proof.
intros.
unfold Level.eqb in H.
apply beq_nat_false in H.
unfold fstLevel in H.
unfold CLevel in H.
case_eq (lt_dec 0 nbLevel).
intros.
rewrite H0 in H.
simpl in *. omega.
intros.
assert (0 < nbLevel). 
apply nbLevelNotZero.
contradict H1.
intuition. 
Qed. 

Lemma levelEqBEqNatTrue0 : 
forall l ,
Level.eqb l fstLevel = true -> l <= 0.
Proof.
intros.
unfold Level.eqb in H.
apply beq_nat_true in H.
unfold fstLevel in H.
unfold CLevel in H.
case_eq (lt_dec 0 nbLevel).
intros.
rewrite H0 in H.
simpl in *. omega.
intros.
assert (0 < nbLevel). 
apply nbLevelNotZero.
contradict H1.
intuition. 
Qed.
 
Lemma levelPredNone nbL:
Level.eqb nbL fstLevel = false ->
Level.pred nbL <> None.
Proof.
intros.
unfold Level.pred.
case_eq(gt_dec nbL 0); intros.
unfold not; intros.
inversion H1.
apply levelEqBEqNatFalse0 in H.
omega.
Qed.

Lemma levelPredLt nbL l :
Level.eqb nbL fstLevel = false ->
Level.pred nbL = Some l -> 
l < nbL. 
Proof.
intros.
unfold Level.pred in *.
case_eq(gt_dec nbL 0); intros.
rewrite H1 in *.
inversion H0.
simpl in *.
omega.
apply levelEqBEqNatFalse0 in H.
omega.
Qed.    

Lemma CLevel0_r :  forall l : level,l - CLevel 0 = l. 
Proof. 
unfold CLevel.
case_eq (lt_dec 0 nbLevel).
intros.
simpl. omega.
intros.
assert (0 < nbLevel).
apply nbLevelNotZero. omega.
Qed.

Lemma CLevelIdentity : forall l : level, CLevel (l - CLevel 0) = l.
Proof.
intros l.
rewrite CLevel0_r. destruct l.
simpl.
unfold CLevel. 
case_eq(lt_dec l nbLevel).
intros. simpl.
assert ( Hl = Pip_state.CLevel_obligation_1 l l0).
apply proof_irrelevance.
subst. reflexivity.
intros.
contradict H. 
omega.
Qed.

Lemma CLevelIdentity1 : forall l : level, CLevel l  = l.
Proof.
intros l.
unfold CLevel. 
case_eq(lt_dec l nbLevel).
intros. simpl.
destruct l.
simpl.
f_equal.
apply proof_irrelevance.
subst.
intros.
destruct l.
simpl in *. 
omega.
Qed.

Lemma CLevelIdentityLe :
forall a , a < nbLevel ->  a <= CLevel a.
Proof.
intros.
unfold CLevel.
case_eq (lt_dec a nbLevel); intros.
simpl; omega.
now contradict H.
Qed.

Lemma levelPredMinus1: forall l l' , Level.eqb l fstLevel = false -> Level.pred l = Some l' -> l' = CLevel (l - 1).
Proof.
intros. 
unfold Level.pred  in *.
assert (l > 0).
{ apply levelEqBEqNatFalse0.
  assumption. }
case_eq (gt_dec l 0).
* intros.
  rewrite H2 in H0.
  inversion H0.
  unfold CLevel.
  case_eq (lt_dec (l - 1) nbLevel).
  intros. subst.   
  assert (Pip_state.CLevel_obligation_1 (l - 1) l0  = Pip_stateLib.Level.pred_obligation_1 l g ).
  apply proof_irrelevance. 
  rewrite H4. reflexivity.
  intros.
  destruct l.
  subst. 
  simpl in *.
  contradict H3.
  omega.
* intros.
  contradict H1.
  assumption.
Qed.

Lemma levelEqNat : 
forall a b , a < nbLevel -> b < nbLevel -> CLevel a = CLevel b -> a = b.
Proof.
intros a b Ha Hb Hab.
 unfold CLevel in *.
 case_eq (lt_dec a nbLevel );intros g Ha'.
 + rewrite Ha' in Hab.
   case_eq (lt_dec b nbLevel);intros p Hb'.
   - rewrite Hb' in Hab.
     inversion Hab. intuition.
   - omega.
 + omega.  
Qed.

Lemma level_gt : 
forall x x0, x - x0 < nbLevel ->  CLevel (x - x0) > 0 -> x > x0.
Proof.
intros.
unfold CLevel in *.
case_eq (lt_dec (x - x0) nbLevel ).
intros. rewrite H1 in H0.
simpl in *. omega.
intros. contradict H1. omega.       
Qed. 

Lemma getNbLevelLe : 
forall nbL, 
Some nbL = getNbLevel -> 
nbL <= CLevel (nbLevel - 1).
Proof.
intros.
unfold getNbLevel in *.
destruct (gt_dec nbLevel 0).
inversion H. 
unfold CLevel.
case_eq (lt_dec (nbLevel - 1) nbLevel); intros.
simpl.
omega.
omega.
assert (0 < nbLevel) by apply nbLevelNotZero.
omega.
Qed.

Lemma getNbLevelEq : 
forall nbL, 
Some nbL = getNbLevel -> 
nbL = CLevel (nbLevel - 1).
Proof.
intros.
unfold getNbLevel in *.
destruct (gt_dec nbLevel 0).
inversion H.
destruct nbL.
simpl in *.
 
unfold CLevel.
case_eq (lt_dec (nbLevel - 1) nbLevel); intros.
inversion H.
subst.
f_equal.
auto.
assert (0 < nbLevel) by apply nbLevelNotZero.
omega.
Qed.

Lemma nbLevelEq :
nbLevel - 1 = CLevel (nbLevel - 1).
Proof.
unfold CLevel.
case_eq(lt_dec (nbLevel - 1) nbLevel); intros.
simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
omega.
Qed.

Lemma fstLevelLe :
forall l: level ,
fstLevel <= l.
Proof.
unfold fstLevel.
unfold CLevel.
intros.
case_eq( lt_dec 0 nbLevel);intros.
simpl;omega.
assert(0 <nbLevel) by apply nbLevelNotZero.
omega.
Qed.
 
Lemma getNbLevelLt nbL:
getNbLevel = Some nbL -> nbL < nbLevel.
Proof.
intros.
unfold  getNbLevel in *.
destruct (gt_dec nbLevel 0).
inversion H.
destruct CLevel.
simpl;trivial.
now contradict H.
Qed.

Lemma notFstLevel (level1 : level) : 
 0 < level1 -> 
Level.eqb level1 fstLevel = false.
Proof. 
unfold Level.eqb.
intros.
apply NPeano.Nat.eqb_neq.
unfold fstLevel. 
unfold CLevel.
case_eq (lt_dec 0 nbLevel);intros. 
simpl.
omega.
assert(0<nbLevel) by apply nbLevelNotZero.
omega.
Qed.

(**** ADT : page **)
Lemma isDefaultPageFalse : forall p,   (defaultPage =? pa p) = false -> pa p <> defaultPage .
Proof.
intros. 
apply beq_nat_false in H.
unfold not. intros.
contradict H. symmetry.
unfold defaultPage in *.
unfold CPage in *.
case_eq (lt_dec 0 nbPage).
intros.
rewrite H in H0.
rewrite H0. trivial.
intros.
rewrite H in H0. rewrite H0. intuition.
Qed.

Lemma isDefaultPageTrue : forall p,   (defaultPage =? pa p) = true -> pa p = defaultPage .
Proof.
intros. 
apply beq_nat_true in H. symmetry.
unfold defaultPage in *.
unfold CPage in *.
case_eq (lt_dec 0 nbPage).
intros.
rewrite H0 in H.
symmetry.
simpl in *.
destruct p.
simpl in *. 
subst.
destruct pa.
simpl in *.
subst.
assert (Hp = Pip_state.CPage_obligation_1 0 l ).
apply proof_irrelevance.
subst.
intuition.
intros.
rewrite H0 in H.
subst.
simpl in *.
destruct p.
simpl in *. 
subst.
destruct pa.
simpl in *.
subst.
destruct page_d.
simpl in *.
assert (Hp = Hp0).
apply proof_irrelevance.
subst.
intuition.
Qed.

Lemma pageDecOrNot :
forall p1 p2 : page, p1 = p2 \/ p1<>p2.
Proof.
destruct p1;simpl in *;subst;destruct p2;simpl in *;subst.
assert (Heq :p=p0 \/ p<> p0) by omega.
destruct Heq as [Heq|Heq].
subst.
left;f_equal;apply proof_irrelevance.
right. unfold not;intros.
inversion H.
subst.
now contradict Heq.
Qed.

(** ADT : index **)
Lemma indexEqFalse : 
forall a b : nat , a < tableSize -> b < tableSize -> a <> b -> CIndex a <> CIndex b.
Proof.
intros.
unfold CIndex.
case_eq (lt_dec a tableSize).
+ intros.
  case_eq (lt_dec b tableSize).
  - intros.
    unfold not in *.
    intros.
    apply H1.
    inversion H4.
    intuition.
  - intros. contradict H0. assumption.
+ intros. contradict H. intuition.
Qed. 

Lemma indexltbTrue : 
forall i1 i2 : index , 
Index.ltb i1 i2 = true -> i1 < i2.
Proof. intros. unfold Index.ltb in H. 
apply NPeano.Nat.ltb_lt in H.
assumption.
Qed. 

Lemma indexltbFalse : 
forall i1 i2 : index , 
Index.ltb i1 i2 = false -> i1 >= i2.
Proof.
intros.
unfold Index.ltb in *. 
apply not_lt.
apply NPeano.Nat.ltb_nlt in H.
omega.  
Qed. 

Lemma indexBoundEq : 
forall i : index , i>= CIndex (tableSize - 1) -> i =  CIndex (tableSize - 1). 
Proof.
intros.
unfold CIndex in *.
destruct (lt_dec (tableSize - 1) tableSize).
simpl in *.
destruct i.
simpl in *. 
subst.
assert(i = tableSize - 1). omega. 
subst. 
assert (Hi = Pip_state.CIndex_obligation_1 (tableSize - 1) l ).
apply proof_irrelevance.
subst. trivial.
contradict n.
assert (0 < tableSize).
assert (tableSize > tableSizeLowerBound). 
apply tableSizeBigEnough.
unfold  tableSizeLowerBound in * . omega. omega. 
Qed.

Lemma indexDiffLtb :
forall i1 i2 : index, i2 < i1 \/ i1 < i2 <-> i2 <> i1.
Proof.
intros.
split;destruct i1, i2;
simpl in *.
 unfold not;
intros;
inversion H0; omega.
intros.
apply nat_total_order.
unfold not in *; intros; subst.
apply H; f_equal.
apply proof_irrelevance.
Qed.

Lemma indexEqId : 
forall i : index, CIndex i = i. 
Proof.
intros.
unfold CIndex.
destruct i.
simpl.
case_eq(lt_dec i tableSize); intros.
assert(Pip_state.CIndex_obligation_1 i l = Hi) by apply proof_irrelevance.
subst. reflexivity.
now contradict Hi.
Qed.

Lemma indexMaxEqFalseLt : 
forall idx : index, idx <> CIndex (tableSize - 1) -> idx < tableSize - 1.
Proof.
intros.
unfold CIndex in *.
case_eq (lt_dec (tableSize - 1) tableSize).
intros .
rewrite H0 in *.
destruct idx.
simpl in *.
apply not_ge.
unfold not.
intros.
contradict H.
assert (i = tableSize - 1).
omega.
subst.
f_equal.
apply proof_irrelevance.
intros.
assert(tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
omega.
Qed.

Lemma indexMaxEqFalseLt1 : 
forall idx : index, idx <> CIndex (tableSize - 1) -> idx < CIndex (tableSize - 1).
Proof.
intros.
unfold CIndex in *.
case_eq (lt_dec (tableSize - 1) tableSize).
intros .
rewrite H0 in *.
destruct idx.
simpl in *.
apply not_ge.
unfold not.
intros.
contradict H.
assert (i = tableSize - 1).
omega.
subst.
f_equal.
apply proof_irrelevance.
intros.
assert(tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
omega.
Qed.

Lemma noteqIndex a b:
a < tableSizeLowerBound -> b < tableSizeLowerBound -> a<>b ->  
CIndex a <> CIndex b.
Proof.
intros. 
apply indexEqFalse;
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
omega.  apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
omega. apply tableSizeBigEnough. omega.
Qed.

Lemma indexEqbTrue : 
forall idx1 idx2 : index, true = Index.eqb idx1 idx2 -> 
idx1 = idx2.
Proof.
unfold Index.eqb in *.
intros.
symmetry in H.
apply beq_nat_true in H.
destruct idx1; destruct idx2.
simpl in *.
subst.
f_equal.
apply proof_irrelevance.
Qed.

Lemma indexLtZero : 
forall idx : index, idx < CIndex 0 -> False.
Proof.
intros.
unfold CIndex in *.
case_eq (lt_dec 0 tableSize); intros; rewrite H0 in *.
destruct idx. simpl in *.
omega.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
omega.
Qed.

Lemma indexSEqbZeroOdd : 
forall curidx idxsucc, 
true = Index.eqb curidx (CIndex 0) -> 
succIndexInternal curidx = Some idxsucc -> 
Nat.Odd idxsucc.
Proof.
intros.
apply indexEqbTrue in H.
subst.
unfold succIndexInternal in *.
unfold CIndex in H0.
case_eq (lt_dec 0 tableSize); intros; rewrite H in *.
simpl in *.
rewrite H in H0.
inversion H0.
case_eq (lt_dec 1 tableSize).
intros.
simpl.
unfold Nat.Odd.
exists 0.
reflexivity.
intros.
subst.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
omega.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
omega.
Qed.

Lemma indexZeroNotOdd : 
forall idx idxsucc : index,
idx < idxsucc -> 
succIndexInternal (CIndex 0) = Some idxsucc ->
~ Nat.Odd idx.
Proof.
intros.
unfold succIndexInternal in *.
unfold CIndex in H0.
case_eq (lt_dec 0 tableSize).
intros.
rewrite H1 in H0.
rewrite H1 in H0.
inversion H0.
case_eq (lt_dec 1 tableSize).
intros.
rewrite H2 in H3.
destruct idxsucc.
inversion H3.
subst.
clear H0 H3.
simpl in *.
inversion H.
rewrite H3.
unfold Nat.Odd.
simpl.
unfold not.
intros.
inversion H0.
omega.
omega.
intros.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
omega.
intros.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
omega.
Qed.
 
 Lemma indexSEqbZeroLt : 
forall  idxsucc idx : index, 
succIndexInternal (CIndex 0)  = Some idxsucc -> 
idx < idxsucc -> 
idx = CIndex 0.
Proof.
intros.
unfold succIndexInternal in *.
unfold CIndex in H. 
case_eq (lt_dec 0 tableSize); intros.
rewrite H1 in H.
rewrite H1 in H.
simpl in *.
inversion H.
case_eq (lt_dec 1 tableSize); intros.
rewrite H2 in H3.
destruct idxsucc.
inversion H3.
simpl in *.
subst.
inversion H0.
unfold CIndex.
case_eq (lt_dec idx tableSize); intros.
destruct idx.
simpl.
f_equal.
apply proof_irrelevance.
omega.
omega.
rewrite H2 in H3.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
unfold tableSizeLowerBound in H4.
omega.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
unfold tableSizeLowerBound in H2.
omega.
Qed.

(*
Lemma indexSuccGt : 
Lemma indexSuccGt : 
forall idx curidx iIndex : index,
StateLib.Index.succ curidx = Some iIndex -> 
idx < curidx -> 
idx <> iIndex.
Proof.
intros.
unfold Index.succ in *.
case_eq (lt_dec(curidx + 1) tableSize); intros; rewrite H1 in *.
simpl in *.
destruct idx.
simpl in *.
destruct iIndex.
inversion H.
unfold not; intros.
inversion H2.
subst.
omega.
now contradict H.
Qed.

Lemma indexSuccEqFalse: 
forall  curidx iIndex : index,
StateLib.Index.succ curidx = Some iIndex -> 
 curidx <> iIndex.
Proof.
intros.
unfold Index.succ in *.
case_eq (lt_dec(curidx + 1) tableSize); intros; rewrite H0 in *.
simpl in *.
destruct iIndex.
inversion H.
subst.
clear H.
unfold not; intros.
destruct curidx.
simpl in *.
inversion H.
omega.
now contradict H.
Qed.


Lemma indexSuccEqFalse: 
forall  curidx iIndex : index,
succIndexInternal curidx = Some iIndex -> 
 curidx <> iIndex.
Proof.
intros.
unfold succIndexInternal in *.
case_eq (lt_dec(curidx + 1) tableSize); intros; rewrite H0 in *.
simpl in *.
destruct iIndex.
inversion H.
subst.
clear H.
unfold not; intros.
destruct curidx.
simpl in *.
inversion H.
omega.
now contradict H.
Qed.

Lemma indexSuccSuccOddOr (curidx iIndex nextidx idx : index): 
succIndexInternal curidx = Some iIndex ->
succIndexInternal iIndex = Some nextidx -> 
Nat.Odd curidx -> 
Nat.Odd idx -> 
idx < nextidx -> 
idx = curidx \/ idx < curidx.
Proof.
intros.
unfold succIndexInternal in *.
      destruct (lt_dec (curidx + 1) tableSize); try now contradict H.
      inversion H; clear H.
      destruct (lt_dec (iIndex + 1) tableSize); try now contradict H0.
      inversion H0; clear H0.
      destruct nextidx.
      inversion H4; clear H4.
      destruct iIndex.
      simpl in *.
      subst.
      inversion H5; clear H5.
      destruct curidx.
      simpl in *.
      destruct idx.
      simpl in *.
      rewrite <- H0 in H3.
      clear H0 Hi l0 l Hi0 .
      assert (i1 = i \/ i1 < i).
      unfold Nat.Odd in *.
      destruct H1 ; destruct H2.
      
      omega.
      destruct H.
      left.
      subst.
      f_equal.
      apply proof_irrelevance.
      right; trivial.
Qed.
      
Lemma indexSuccSuccEvenOr (curidx iIndex nextidx idx : index): 
succIndexInternal curidx = Some iIndex ->
succIndexInternal iIndex = Some nextidx -> 
Nat.Even curidx -> 
Nat.Even idx -> 
idx < nextidx -> 
idx = curidx \/ idx < curidx.
Proof.
intros.
unfold succIndexInternal in *.
      destruct (lt_dec (curidx + 1) tableSize); try now contradict H.
      inversion H; clear H.
      destruct (lt_dec (iIndex + 1) tableSize); try now contradict H0.
      inversion H0; clear H0.
      destruct nextidx.
      inversion H4; clear H4.
      destruct iIndex.
      simpl in *.
      subst.
      inversion H5; clear H5.
      destruct curidx.
      simpl in *.
      destruct idx.
      simpl in *.
      rewrite <- H0 in H3.
      clear H0 Hi l0 l Hi0 .
      assert (i1 = i \/ i1 < i).
      destruct H1 ; destruct H2.
      omega.
      destruct H.
      left.
      subst.
      f_equal.
      apply proof_irrelevance.
      right; trivial.
Qed.

Lemma indexSuccSuccEvenOddLt (curidx iIndex nextidx idx : index): 
succIndexInternal curidx = Some iIndex ->
succIndexInternal iIndex = Some nextidx -> 
Nat.Even idx -> 
Nat.Odd curidx -> 
idx < nextidx -> 
idx < iIndex -> 
idx < curidx.
Proof.
intros.
unfold succIndexInternal in *.
      destruct (lt_dec (curidx + 1) tableSize); try now contradict H.
      inversion H; clear H.
      destruct (lt_dec (iIndex + 1) tableSize); try now contradict H0.
      inversion H0; clear H0.
      destruct nextidx.
      inversion H5; clear H5.
      destruct iIndex.
      simpl in *.
      subst.
      inversion H6; clear H6.
      destruct curidx.
      simpl in *.
      destruct idx.
      simpl in *.
      destruct H1; destruct H2.
      subst.
      
      omega.
Qed.


Lemma indexNotEqSuccNotEq (idx1 idx2 : index): 
idx1 < tableSize -1 -> 
idx2 < tableSize -1 -> 
idx1 <> idx2 -> 
succIndexInternal idx2 <> succIndexInternal idx1.
Proof.
intros.
unfold succIndexInternal.
case_eq (lt_dec (idx2 + 1) tableSize); intros; try omega.  
case_eq (lt_dec (idx1 + 1) tableSize); intros; try omega.
destruct idx1; destruct idx2; simpl in *.
unfold not; intros Hfalse.
inversion Hfalse.
assert (i0 = i) by omega.
subst.
contradict H1.
f_equal.
apply proof_irrelevance.
Qed.

(** ADT : vaddr **)
Lemma lengthVAddrNotZero (va : vaddr) : fstLevel < (length va -1).
Proof. 
 unfold fstLevel.  destruct va.
 simpl. rewrite Hva. unfold CLevel. case_eq (lt_dec 0 nbLevel).
 simpl. intros. omega.
 intros. destruct level_d. simpl. omega. 
 Qed.

Lemma CLevelMinusEq0 : 
forall (a : level) b , CLevel (a -  b) = CLevel 0 ->   a = CLevel b \/ a < b. 
Proof.
intros.
unfold CLevel in *.  
case_eq (lt_dec (a - b) nbLevel );
intros lab Hab; rewrite Hab in *.
case_eq(lt_dec 0 nbLevel);
intros l0 H0;
rewrite H0 in*.
inversion H.
case_eq (lt_dec b nbLevel);
intros lb Hb.
simpl in *.
apply NPeano.Nat.sub_0_le in H2.
apply le_lt_or_eq in H2.
destruct H2. 
right; assumption.
left.
destruct a.
simpl in *.
subst.
assert (Hl =  Pip_state.CLevel_obligation_1 b lb ) by 
apply proof_irrelevance.
subst. reflexivity.
right; destruct a; simpl in *; omega.
assert (0 < nbLevel) by apply nbLevelNotZero.
now contradict H1.
destruct a. simpl in *.
omega.
Qed.
*)

(** beqPairs **)
Lemma beqPairsTrue : 
forall table1 idx1 table2 idx2 , table1 = table2 /\ idx1 = idx2 <->   
beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex = true.
Proof.
intros.
unfold beqPairs.
cbn.  
unfold beqPage , beqIndex .
split.
* case_eq (table1 =? table2) ; case_eq(idx1 =? idx2);intuition.
  apply beq_nat_false in H.  
  destruct idx1 , idx2. simpl in *. inversion H3. omega.  
  apply beq_nat_false in H0.
  destruct table1, table2. simpl in *.
  inversion H2. omega.
  destruct ((false && false)%bool). trivial.
  apply beq_nat_false in H0.
  destruct table1, table2. simpl in *.
  inversion H2. omega.
* intros. 
  case_eq (table1 =? table2) ; case_eq(idx1 =? idx2);intuition.
  apply beq_nat_true in H1; trivial.
  destruct table1, table2; simpl in *; subst; f_equal; apply proof_irrelevance. 
  destruct idx1 , idx2; simpl in *.
  apply beq_nat_true in H0; subst; f_equal; apply proof_irrelevance.
  apply beq_nat_true in H1; trivial.
  destruct table1, table2; simpl in *; subst; f_equal; apply proof_irrelevance.
  rewrite H0 in H.
  rewrite H1 in H. 
  case_eq ((true && false)%bool); intros.
  apply Bool.andb_true_iff in H2.
  now contradict H2.
  rewrite H2 in H; now contradict H.
  rewrite H0 in H.
  rewrite H1 in H. 
  case_eq ((false && true)%bool); intros.
  apply Bool.andb_true_iff in H2.
  now contradict H2.
  rewrite H2 in H; now contradict H.
  apply beq_nat_true in H0.
  destruct idx1 , idx2; simpl in *;subst; f_equal; apply proof_irrelevance. 
  rewrite H0 in H.
  rewrite H1 in H. 
  case_eq ((false && false)%bool); intros.
  apply Bool.andb_true_iff in H2.
  now contradict H2.  
  rewrite H2 in H; now contradict H.
  rewrite H0 in H.
  rewrite H1 in H. 
  case_eq ((false && false)%bool); intros.
  apply Bool.andb_true_iff in H2.
  now contradict H2.  
  rewrite H2 in H; now contradict H.
Qed.

Lemma beqPairsFalse : 
forall table1 idx1 table2 idx2 , 
table1 <> table2 \/ idx1 <> idx2 <-> 
beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex = false.
Proof.
intros.
unfold beqPairs.
cbn.  
unfold beqPage , beqIndex .
intuition.
case_eq (table1 =? table2) ; case_eq(idx1 =? idx2);intuition.
contradict H0.
apply beq_nat_true in H1.
destruct table1, table2. simpl in *. subst.
assert (Hp = Hp0).
apply proof_irrelevance. subst. trivial. 
assert((idx1 =? idx2) = false).
apply Nat.eqb_neq. unfold not.
intros.
destruct idx1; destruct idx2.
simpl in *.
subst.
apply H0.
f_equal.
apply proof_irrelevance.
rewrite H.
case_eq ((table1 =? table2) && false).
intros.
apply andb_true_iff in H1.
intuition.
trivial.
case_eq (table1 =? table2) ; case_eq(idx1 =? idx2);intuition.
+ rewrite H1 in H.
  rewrite H0 in H.
  intuition.
+ apply beq_nat_false in H0.
  right.
  intros. 
  destruct idx1; destruct idx2.
  simpl in *.
  inversion H2.
  subst.
  now contradict H0.
+ apply beq_nat_false in H1.
  left.
  intros. 
  destruct table1; destruct table2.
  simpl in *.
  inversion H2.
  subst.
  now contradict H1.
+ apply beq_nat_false in H1.
  left.
  intros. 
  destruct table1; destruct table2.
  simpl in *.
  inversion H2.
  subst.
  now contradict H1.
Qed.

 Lemma idxPRsucNotEqidxPPR : PRidx < tableSize - 1 -> 
    exists succidx1 : index, succIndexInternal PRidx = Some succidx1 /\ (succidx1 = PPRidx -> False).
    Proof. 
    unfold succIndexInternal.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    f_equal.
    destruct PRidx.
    case_eq (lt_dec i tableSize); intros.
    f_equal.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros.
    
    assert(Hi : {| i := PRidx + 1; Hi := Pip_state.CIndex_obligation_1 (PRidx + 1) l0 |} = PPRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold PRidx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 0 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract omega.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    abstract omega.
    Qed. 
     Lemma idxPPRsuccNotEqidxPR : PPRidx < tableSize - 1 -> 
    exists succidx2 : index, succIndexInternal PPRidx = Some succidx2 /\ (succidx2 = PRidx -> False).
    Proof.  
    unfold succIndexInternal.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    destruct PPRidx.
    case_eq (lt_dec i tableSize); intros.
    f_equal.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.    
    assert(Hi : {| i := PPRidx + 1; Hi := Pip_state.CIndex_obligation_1 (PPRidx + 1) l0 |} = PRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold PPRidx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 10 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract omega.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    abstract omega.
    Qed.
 
Lemma idxPRidxPPRNotEq : PRidx <> PPRidx.
    Proof.  
      unfold PRidx. unfold PPRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega.
      apply tableSizeBigEnough.
      abstract omega. Qed. 

    Lemma idxPPRsuccNotEqidxPD : PPRidx < tableSize - 1 -> 
    exists succidx2 : index, succIndexInternal PPRidx = Some succidx2 /\ (succidx2 = PDidx -> False).
    Proof. 
    unfold succIndexInternal.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    destruct PPRidx.
    case_eq (lt_dec i tableSize); intros.
    f_equal.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.
    
    assert(Hi : {| i := PPRidx + 1; Hi := Pip_state.CIndex_obligation_1 (PPRidx + 1) l0 |} = PDidx)
    by trivial.
    contradict Hi.
    subst.
    unfold PPRidx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 10 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    abstract omega.
    abstract omega.
    Qed.

Lemma idxPPRidxPDNotEq : PPRidx <> PDidx.
    Proof. 
      unfold PPRidx. unfold PDidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega. apply tableSizeBigEnough. abstract omega. Qed. 
    Lemma idxPDsucNotEqidxPPR :  PDidx < tableSize - 1 -> 
    exists succidx1 : index, succIndexInternal PDidx = Some succidx1 /\ (succidx1 = PPRidx -> False).
    Proof. 
    unfold succIndexInternal.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    destruct PDidx.
    case_eq (lt_dec i tableSize); intros.
    f_equal.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.
    assert(Hi : {| i := PDidx + 1; Hi := Pip_state.CIndex_obligation_1 (PDidx + 1) l0 |} = PPRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold PDidx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 2 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract omega.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    abstract omega.
    Qed.

 Lemma idxPDidxPPRNotEq : PDidx <> PPRidx.
    Proof. 
      unfold PRidx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega.
      apply tableSizeBigEnough.
      abstract omega. Qed.

 Lemma idxPPRidxSh1NotEq : PPRidx <> sh1idx.
    Proof. 
      unfold PPRidx. unfold sh1idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega. apply tableSizeBigEnough. abstract omega. Qed.
   
    Lemma idxPPRsuccNotEqidxSh1 : PPRidx < tableSize - 1 -> 
    exists succidx2 : index, succIndexInternal PPRidx = Some succidx2 /\ (succidx2 = sh1idx -> False).
    Proof. 
    unfold succIndexInternal.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    destruct PPRidx.
    case_eq (lt_dec i tableSize); intros.
    f_equal.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.
    
    assert(Hi : {| i := PPRidx + 1; Hi := Pip_state.CIndex_obligation_1 (PPRidx + 1) l0 |} = sh1idx)
    by trivial.
    contradict Hi.
    subst.
    unfold PPRidx. unfold sh1idx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 10 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    abstract omega.
    abstract omega.
    Qed. 

    Lemma idxSh1succNotEqidxPPR : sh1idx < tableSize - 1 ->
    exists succidx1 : index, succIndexInternal sh1idx = Some succidx1 /\ (succidx1 = PPRidx -> False).
    Proof. 
    unfold succIndexInternal.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    destruct sh1idx.
    case_eq (lt_dec i tableSize); intros.
    f_equal.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    
    assert(Hi : {| i := sh1idx + 1; Hi := Pip_state.CIndex_obligation_1 (sh1idx + 1) l0 |} = PPRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 4 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract omega.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    abstract omega.
    Qed.

Lemma idxSh1idxPPRnotEq : sh1idx <> PPRidx.
    Proof.  
      unfold sh1idx. unfold PPRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega.
      apply tableSizeBigEnough.
      abstract omega. Qed.

(*

    Lemma idxPPRsuccNotEqidxSh2 : PPRidx < tableSize - 1 -> 
    exists succidx2 : index, succIndexInternal PPRidx = Some succidx2 /\ (succidx2 = sh2idx -> False).
    Proof. 
    unfold succIndexInternal.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    destruct sh1idx.
    case_eq (lt_dec i tableSize); intros.
    f_equal.
    omega.
    unfold CIndex.
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract omega.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.    
    assert(Hi : {| i := PPRidx + 1; Hi := Pip_state.CIndex_obligation_1 (PPRidx + 1) l0 |} = sh2idx)
    by trivial.
    contradict Hi.
    subst.
    unfold PPRidx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 10 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    abstract omega.
    abstract omega.
    Qed. 

Lemma idxPPRidxSh2NotEq : PPRidx <> sh2idx. Proof. 
      unfold PPRidx. unfold sh2idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega.
      apply tableSizeBigEnough.
      abstract omega. Qed.
    Lemma idxSh2succNotEqidxPPR : sh2idx < tableSize - 1 -> 
    exists succidx1 : index, succIndexInternal sh2idx = Some succidx1 /\ (succidx1 = PPRidx -> False).
    Proof.  
    unfold succIndexInternal.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    destruct sh2idx.
    case_eq (lt_dec i tableSize); intros.
    f_equal.
    omega.
    unfold CIndex.
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.  
    contradict H2.
    subst.
    unfold sh2idx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 6 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract omega.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    abstract omega.
    Qed. 

Lemma idxSh2idxPPRnotEq : sh2idx <> PPRidx.
    Proof.  
      unfold sh1idx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega.
      apply tableSizeBigEnough.
      abstract omega. Qed.

    Lemma idxPPRsuccNotEqidxSh3 : PPRidx < tableSize - 1 -> 
    exists succidx2 : index, succIndexInternal PPRidx = Some succidx2 /\ (succidx2 = sh3idx -> False).
    Proof. 
    unfold succIndexInternal.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract omega.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.
    
     assert(Hi : {| i := PPRidx + 1; Hi := Pip_state.CIndex_obligation_1 (PPRidx + 1) l0 |} = sh3idx)
    by trivial.
    contradict Hi.
    subst.
    unfold PPRidx. unfold sh3idx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 10 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    abstract omega.
    abstract omega.
    Qed. 

    Lemma idxSh3succNotEqPPRidx : sh3idx < tableSize - 1 -> 
    exists succidx1 : index, succIndexInternal sh3idx = Some succidx1 /\ (succidx1 = PPRidx -> False).
    Proof.
    unfold succIndexInternal.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract omega.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
     assert(Hi : {| i := sh3idx + 1; Hi := Pip_state.CIndex_obligation_1 (sh3idx + 1) l0 |} = PPRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 8 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract omega.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    abstract omega.
    Qed. 

 Lemma idxPPRidxSh3NotEq : PPRidx <> sh3idx.
    Proof.  
      unfold PPRidx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega.
       apply tableSizeBigEnough. abstract omega. Qed.

    Lemma idxSh3succNotEqPRidx : sh3idx < tableSize - 1 -> 
    exists succidx2 : index, succIndexInternal sh3idx = Some succidx2 /\ (succidx2 = PRidx -> False).
    Proof. 
    unfold succIndexInternal.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract omega.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
    
     assert(Hi : {| i := sh3idx + 1; Hi := Pip_state.CIndex_obligation_1 (sh3idx + 1) l0 |} = PRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 8 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract omega.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    abstract omega.
    Qed.

    Lemma idxPRsuccNotEqidxSh3 : PRidx < tableSize - 1 -> exists succidx1 : index, succIndexInternal PRidx = Some succidx1 /\ (succidx1 = sh3idx -> False).
    Proof.  
    unfold succIndexInternal.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract omega.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros.
    assert(Hi : {| i := PRidx + 1; Hi := Pip_state.CIndex_obligation_1 (PRidx + 1) l0 |} = sh3idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 0 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract omega.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    abstract omega.
    Qed.

    Lemma  idxPRidxSh3NotEq : PRidx <> sh3idx.
    Proof.  
    (* *)
      unfold PRidx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega. apply tableSizeBigEnough. abstract omega. Qed.  

    Lemma idxSh3succNotEqidxPDidx : sh3idx < tableSize - 1 -> 
    exists succidx2 : index, succIndexInternal sh3idx = Some succidx2 /\ (succidx2 = PDidx -> False).
    Proof.  
    unfold succIndexInternal.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract omega.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
     assert(Hi : {| i := sh3idx + 1; Hi := Pip_state.CIndex_obligation_1 (sh3idx + 1) l0 |} = PDidx)
    by trivial.
    contradict Hi.
    subst.
    unfold PDidx. unfold sh3idx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 8 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    abstract omega.
    abstract omega.
    Qed.


    Lemma idxPDsucNotEqidxSh3 : PDidx < tableSize - 1 -> 
    exists succidx1 : index, succIndexInternal PDidx = Some succidx1 /\ (succidx1 = sh3idx -> False).
    Proof. 
    unfold succIndexInternal.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract omega.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.
    
     assert(Hi : {| i := PDidx + 1; Hi := Pip_state.CIndex_obligation_1 (PDidx + 1) l0 |} = sh3idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 2 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract omega.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract omega.
    abstract omega.
    Qed.

    Lemma idxPDidxSh3notEq : PDidx <> sh3idx.
    Proof. 
(*    
 *)      unfold PDidx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract omega. apply tableSizeBigEnough. abstract omega.
      Qed. 

    Lemma idxSh3succNotEqidxSh1 : 
    sh3idx < tableSize - 1 -> 
     exists succidx2 : index, succIndexInternal sh3idx = Some succidx2 /\ (succidx2 = sh1idx -> False).
     Proof. 
    unfold succIndexInternal.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
    
     assert(Hi : {| i := sh3idx + 1; Hi := Pip_state.CIndex_obligation_1 (sh3idx + 1) l0 |} = sh1idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold sh1idx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 8 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    Qed.
    Lemma sh1idxSh3idxNotEq : sh1idx < tableSize - 1 ->
    exists succidx1 : index, succIndexInternal sh1idx = Some succidx1 /\ (succidx1 = sh3idx -> False).
    Proof. 
    unfold succIndexInternal.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    
     assert(Hi : {| i := sh1idx + 1; Hi := Pip_state.CIndex_obligation_1 (sh1idx + 1) l0 |} = sh3idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold sh3idx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 4 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    omega.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    Qed.
    Lemma idxSh1idxSh3notEq :  sh1idx <> sh3idx.
     Proof. 
      unfold sh1idx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega.
      Qed. 

    Lemma idxSh3succNotEqidxSh2 : sh3idx < tableSize - 1 ->
    exists succidx2 : index, succIndexInternal sh3idx = Some succidx2 /\ (succidx2 = sh2idx -> False).
    Proof.  
    unfold succIndexInternal.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
    assert(Hi : {| i := sh3idx + 1; Hi := Pip_state.CIndex_obligation_1 (sh3idx + 1) l0 |} = sh2idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 8 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    Qed.

    Lemma idxSh2succNotEqidxSh3 : sh2idx < tableSize - 1 ->
    exists succidx1 : index, succIndexInternal sh2idx = Some succidx1 /\ (succidx1 = sh3idx -> False).
    Proof. 
    unfold succIndexInternal.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
     assert(Hi : {| i := sh2idx + 1; Hi := Pip_state.CIndex_obligation_1 (sh2idx + 1) l0 |} = sh3idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 6 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    omega.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    Qed.
 
    Lemma idxSh2idxSh3notEq : sh2idx <> sh3idx .
    Proof.  
      unfold sh2idx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. 
     Qed.
     
   Lemma  idxSh2succNotEqidxPR : sh2idx < tableSize - 1 -> 
   exists succidx2 : index, succIndexInternal sh2idx = Some succidx2 /\ (succidx2 = PRidx -> False).
   Proof.
    unfold succIndexInternal.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
    
     assert(Hi : {| i := sh2idx + 1; Hi := Pip_state.CIndex_obligation_1 (sh2idx + 1) l0 |} = PRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh2idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 6 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    omega.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    Qed.   
    
        Lemma idxPRsuccNotEqidxSh2 : PRidx < tableSize - 1 -> 
    exists succidx1 : index, succIndexInternal PRidx = Some succidx1 /\ (succidx1 = sh2idx -> False). 
    Proof.
    unfold succIndexInternal.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros.
    
     assert(Hi : {| i := PRidx + 1; Hi := Pip_state.CIndex_obligation_1 (PRidx + 1) l0 |} = sh2idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh2idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 0 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    omega.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    Qed.
        Lemma idxPRidxSh2NotEq : PRidx <> sh2idx.
    Proof.
      unfold PRidx. unfold sh2idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega.
      Qed.   

          Lemma idxSh2succNotEqidxPD : sh2idx < tableSize - 1 -> 
     exists succidx2 : index, succIndexInternal sh2idx = Some succidx2 /\ (succidx2 = PDidx -> False).
     Proof. 
    unfold succIndexInternal.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
    assert(Hi : {| i := sh2idx + 1; Hi := Pip_state.CIndex_obligation_1 (sh2idx + 1) l0 |} = PDidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh2idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 6 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    omega.

    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    
    omega.
    Qed.

        Lemma idxPDsucNotEqidxSh2 : 
    PDidx < tableSize - 1 -> 
    exists succidx1 : index, succIndexInternal PDidx = Some succidx1 /\ (succidx1 = sh2idx -> False).
    Proof.
    unfold succIndexInternal.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.
   
   
    assert(Hi : {| i := PDidx + 1; Hi := Pip_state.CIndex_obligation_1 (PDidx + 1) l0 |} = sh2idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh2idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 2 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    omega.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    Qed. 

 
    Lemma idxPDidxSh2notEq : PDidx <> sh2idx .
    Proof.  
      unfold PDidx. unfold sh2idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. Qed.

          Lemma idxSh2succNotEqidxSh1 : 
    sh2idx < tableSize - 1 -> 
    exists succidx2 : index, succIndexInternal sh2idx = Some succidx2 /\ (succidx2 = sh1idx -> False).
    Proof.
    unfold succIndexInternal.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
      assert(Hi : {| i := sh2idx + 1; Hi := Pip_state.CIndex_obligation_1 (sh2idx + 1) l0 |} = sh1idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 6 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    Qed.

  
      Lemma idxSh1succNotEqidxSh2 : 
    sh1idx < tableSize - 1 -> 
    exists succidx1 : index, succIndexInternal sh1idx = Some succidx1 /\ (succidx1 = sh2idx -> False).
    Proof.  
    unfold succIndexInternal.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    
     assert(Hi : {| i := sh1idx + 1; Hi := Pip_state.CIndex_obligation_1 (sh1idx + 1) l0 |} = sh2idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 4 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    omega.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    Qed.	


      
    Lemma idxSh1succNotEqidxPR : 
    sh1idx < tableSize - 1 -> 
    exists succidx2 : index, succIndexInternal sh1idx = Some succidx2 /\ (succidx2 = PRidx -> False).
    Proof.
    unfold succIndexInternal.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    assert(Hi : {| i := sh1idx + 1; Hi := Pip_state.CIndex_obligation_1 (sh1idx + 1) l0 |} = PRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 0 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    omega.
    omega.
    
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    Qed.
        Lemma idxPRsuccNotEqidxSh1 :
    PRidx + 1 < tableSize -> 
(*     PRidx + 1< tableSize - 1 ->  *)
    exists succidx1 : index, succIndexInternal PRidx = Some succidx1 /\ (succidx1 = sh1idx -> False).
    Proof. 
    unfold succIndexInternal.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros.
    assert(Hi : {| i := PRidx + 1; Hi := Pip_state.CIndex_obligation_1 (PRidx + 1) l0 |} = sh1idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 0 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    omega.
    omega.

    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    Qed.
Lemma idxPRidxSh1NotEq : PRidx <> sh1idx.
    Proof. 
      unfold PRidx. unfold sh1idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega.
      Qed.
      
          Lemma idxSh1succNotEqidxPD : 
    sh1idx + 1 < tableSize -> 
    exists succidx2 : index, succIndexInternal sh1idx = Some succidx2 /\ (succidx2 = PDidx -> False).
    Proof.  
    unfold succIndexInternal.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    assert(Hi : {| i := sh1idx + 1; Hi := Pip_state.CIndex_obligation_1 (sh1idx + 1) l0 |} = PDidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 4 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    omega.
(*     omega.
    
    
    contradict H13.
    subst.
    unfold PDidx. unfold sh1idx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros.
    inversion H14.
    unfold CIndex in H16.
    case_eq(lt_dec 4 tableSize); intros; rewrite H15 in *.
    inversion H16. *)
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    Qed. 
    
        Lemma  idxPDsucNotEqidxSh1 : 
    PDidx + 1 < tableSize -> 
    exists succidx1 : index, succIndexInternal PDidx = Some succidx1 /\ (succidx1 = sh1idx -> False).
    Proof. 
    unfold succIndexInternal.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    destruct PDidx.
    case_eq (lt_dec i tableSize); intros.
    f_equal.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.
    assert(Hi : {| i := PDidx + 1; Hi := Pip_state.CIndex_obligation_1 (PDidx + 1) l0 |} = sh1idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 2 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    omega.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    Qed.


      
          Lemma idxPDsucNotEqidxPR : 
    PDidx + 1 < tableSize -> 
     exists succidx2 : index, succIndexInternal PDidx = Some succidx2 /\ (succidx2 = PRidx -> False).
     Proof.
    unfold succIndexInternal.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.
    
    assert(Hii : {| i := PDidx + 1; Hi := Pip_state.CIndex_obligation_1 (PDidx + 1) l0 |} = PRidx)

by trivial.
    contradict Hii.
    subst.
    unfold PDidx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros Hi.
    inversion Hi.
    assert(Hii : CIndex 2 + 1 = 0) by trivial.
    unfold CIndex in Hii.
    case_eq(lt_dec 0 tableSize); intros Hi1 Hi2;  rewrite Hi2 in *.
    inversion Hi.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    omega.
    Qed.
    
        Lemma idxPRsucNotEqidxPD : 
    PRidx + 1 < tableSize -> 
    exists succidx1 : index, succIndexInternal PRidx = Some succidx1 /\ (succidx1 = PDidx -> False).
    Proof. 
    unfold succIndexInternal.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros * Hc2.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros * Hc3 Hc4.
    contradict Hc4.
    subst.
    unfold PDidx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros * Hc5.
    unfold not; intros Hc6.
    inversion Hc6 as [Hc7].
    unfold CIndex in Hc7.
    case_eq(lt_dec 0 tableSize); intros * Hc8; rewrite Hc8 in *.
    inversion Hc6.
    simpl in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    subst.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    
    omega.
    Qed.

        Lemma idxPRidxPDNotEq : PRidx <> PDidx.
    Proof.  
      unfold PDidx. unfold PRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega.
      Qed.
*)
