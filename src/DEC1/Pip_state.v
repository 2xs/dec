(* Narjes Jomaa and David Nowak, 
   Pip code refactored by Mohamed Sami Cherif *)
(**PIP STATE *)
Require Import List Bool Arith Omega Lib.
Import List.ListNotations.

Axiom tableSize nbLevel nbPage: nat.
Axiom nbLevelNotZero: nbLevel > 0.
Axiom nbPageNotZero: nbPage > 0.
Axiom tableSizeIsEven : Nat.Even tableSize.
Definition tableSizeLowerBound := 14.  
Axiom tableSizeBigEnough : tableSize > tableSizeLowerBound. 

Record index := {
  i :> nat ;
  Hi : i < tableSize }.

Record page := { 
  p :> nat;
  Hp : p < nbPage }.

Definition paddr := (page * index)%type.

Record vaddr := {
  va :> list index ;
  Hva : length va = nbLevel + 1}.

Record level := {
  l :> nat ;
  Hl : l < nbLevel }.

Record count := {
  c :> nat ;
  Hnb : c <= (3*nbLevel) + 1  ;
 }.

Parameter index_d : index.
Parameter page_d : page.
Parameter level_d : level.

Require Import Coq.Program.Tactics.

Program Definition CIndex  (p : nat) : index := 
if (lt_dec p tableSize) then 
Build_index p _ else index_d.


Program Definition CPage (p : nat) : page := 
if (lt_dec p nbPage) then Build_page p _ else  page_d.

Program Definition CVaddr (l: list index) : vaddr := 
if ( Nat.eq_dec (length l)  (nbLevel+1))  
  then Build_vaddr l _
  else Build_vaddr (repeat (CIndex 0) (nbLevel+1)) _.


Program Definition CLevel ( a :nat) : level := 
if lt_dec a nbLevel then  Build_level a _ 
else level_d .

(* BEGIN NOT SIMULATION *)

Next Obligation.
apply repeat_length.
Qed. 

(* END NOT SIMULATION *)

Record Pentry : Type:=
{read :bool;
 write : bool ;
 exec : bool;
 present : bool;
 user    : bool;
 pa      : page
}.

Record Ventry : Type:=
{
 pd : bool;
 vad : vaddr
}.

Inductive value : Type:= 
|PE : Pentry -> value
|VE : Ventry -> value
|PP : page -> value
|VA : vaddr -> value
|I  : index -> value.  


Record state : Type := {
 currentPartition : page;
 memory : list (paddr * value)
}.

Definition multiplexer := CPage 1.

(** Fix virtual addresses positions into the partition descriptor
    of the partition (+1 to get the physical page position) *)
Definition PRidx := CIndex 0.   (* descriptor *)
Definition PDidx := CIndex 2.   (* page directory *)
Definition sh1idx := CIndex 4.  (* shadow1 *) 
Definition sh2idx := CIndex 6.  (* shadow2 *)
Definition sh3idx := CIndex 8.  (* configuration pages list*)
Definition PPRidx := CIndex 10. (* parent (virtual address is null) *)

Definition beqIndex (a b : index) : bool := a =? b.
Definition beqPage (a b : page) : bool := a =? b.
Definition beqVAddr (a b : vaddr) : bool := eqList a b beqIndex.

(** default values *)
Definition defaultIndex := CIndex 0.
Definition defaultVAddr := CVaddr (repeat (CIndex 0) nbLevel).
Definition defaultPage := CPage 0.

(** Define first level number *)
Definition fstLevel :=  CLevel 0.

(** Define the entry position of the kernel mapping into the first indirection 
    of partitions *)
Definition Kidx := CIndex 1.





