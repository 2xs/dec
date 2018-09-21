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

Require Import BinNat.
Require Import Integers.

Require VectorDef.

(*
Add LoadPath "/home/ptorrx/lib/CompCert-3.0.1" as compcert.
Add LoadPath "/home/ptorrx/lib/CompCert-3.0.1/cfrontend" as compcert.cfrontend.
Add LoadPath "/home/ptorrx/lib/CompCert-3.0.1/common" as compcert.common.

Require Import compcert.common.AST.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Csyntax.
*)

Import ListNotations.
Import Integers.

(* Import Values. *)

Module CHeadAux (IdT: ModTyp) <: ModTyp.

Module InterpretL := Interpret IdT.
Export InterpretL.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

(****************************************************************)

(* produces numbered list, pairing list elems with natural numbers plus 2 *)
Fixpoint enumBListX {A: Type} (n: nat) (ls: list A) : list (nat * A) :=
  match ls with
  | nil => nil
  | x :: xs => ((length xs + n + 2)%nat, x) :: enumBListX n xs
  end.                            

Definition enumBList {A: Type} (ls: list A) : list (nat * A) :=
  enumBListX 0 ls.

(* pairs numbered list with its length *)
Definition enumEListA {A: Type} (n: nat) (ls: list A) :
  list (nat * A) * nat :=
  (enumBList ls, length ls).

(* not used - pairs list with its lenght *)
Definition enumEList {A: Type} (ls: list A) : list A * nat :=
  (ls, length ls).

(* triple swap: swap first two components of a triple *)
Definition swapTriple {A B C: Type} (x : (A * (B * C))) : (B * (A * C)) :=
  let a := fst x in
  let b := fst (snd x) in
  let c := snd (snd x) in
               (b, (a, c)). 

(* maps triple swap on a list, recursive def *)
Fixpoint swapTListA {A B C: Type} (ls : list (A * (B * C))) :
  list (B * (A * C)) :=
  match ls with
  | nil => nil
  | x :: xs => let a := fst x in
               let b := fst (snd x) in
               let c := snd (snd x) in
               (b, (a, c)) :: swapTListA xs
  end.

(* swapped numbered list: maps triple swap on the numbered list *)
Definition swapTList22X {K V: Type} (n: nat) (ls : list (K * V)) :
  list (K * (nat * V)) := map swapTriple (enumBListX n ls).

Definition swapTList22 {K V: Type} (ls : list (K * V)) :
  list (K * (nat * V)) := swapTList22X 0 ls.


(**************************************************************)

(* converting naturals to a binary representation *)

(* not good *)
Fixpoint nat2blistB (n p : nat) (ls : list nat) : list nat :=  
  match p with
  | 0 => ls
  | S q => let pp := 2 ^ p in
           let m1 := n / pp in
           let m2 := Nat.modulo n pp in 
    (m1 :: (nat2blistB m2 q ls))
  end.                       

(* decomposes n by dividing for powers of 2 up to p *)
Fixpoint nat2blist (n p : nat) : list nat :=  
  match p with
  | 0 => [n]
  | S q => let pp := 2 ^ p in
           let m1 := n / pp in
           let m2 := Nat.modulo n pp in 
    (m1 :: (nat2blist m2 q))
  end.                       

(* binary naturals: gives the binary representation of n as a list of
naturals (actually only 1 and 0) *)
Definition nat2blistA (n: nat) : list nat :=
  nat2blist n (Nat.log2 n).

(* Eval compute in (Nat.log2 19). *)
(* Eval compute in (nat2blistA 15). *)

(* increases a positive, by adding either 0 or 1 as least significant
digit *)
Definition pos_add1 (p: positive) (n: nat) : positive :=
  match n with
  | 0 => xO p
  | S _ => xI p
  end.            

(* converts a binary natural into a positive *)
Definition blist2positive (ls : list nat) : positive :=
  match ls with
  | nil => xH
  | (x::xs) => fold_left pos_add1 xs xH
  end.                       

(* converts a natural into a positive *)
Definition nat2positive (n: nat) : positive :=
  blist2positive (nat2blistA n).

(* Eval compute in (nat2positive 13). *)

(* converts a swap numbered list into an extended C environment *)
Definition swapTList33 {K V: Type} (ls : list (K * (nat * V))) :
  list (K * (positive * V)) := 
  map (fun pp => let p1 := fst pp in let p2 := fst (snd pp) in
                                     let p3 := snd (snd pp) in
                                     (p1, (nat2positive p2, p3))) ls.  


Import BinPos.

Open Scope positive_scope.

Fixpoint Pmaximum (ls : list positive) : positive :=
  match ls with
  | nil => xH
  | x :: xs => Pmax x (Pmaximum xs)
  end.                  


End CHeadAux.