Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import StaticSemA.
Require Import IdModTypeA.
Require Import ModNat1A.
Require Import AbbrevA.
Require Import Eqdep FunctionalExtensionality Coq.Program.Tactics.

Import ListNotations.
Open Scope string_scope.

Module Convert2.

Module LM := Abbrev ModNat1.
Export LM.

Definition Id := LM.Id.
Definition IdEqDec := LM.IdEqDec.
Definition IdEq := LM.IdEq.
Definition W := LM.W.
Definition Loc_PI := LM.Loc_PI.
Definition BInit := LM.BInit.
Definition WP := LM.WP.


(************************************************************************)

(* syntax from Pip *)

Definition state : Type := nat.

Inductive result (A : Type) : Type :=
| val : A -> result A
| undef : nat -> state-> result A.


Definition LLI (A :Type) : Type := state -> result (A * state).


Arguments val [ A ].
Arguments undef [ A ]. 

Definition ret {A : Type} (a : A) : LLI A :=
  fun s => val (a , s) .

Definition bind {A B : Type} (m : LLI A)(f : A -> LLI B) : LLI B :=  
fun s => match m s with
    | val (a, s') => f a s'
    | undef a s' => undef a s'
    end.

Definition put (s : state) : LLI unit :=
  fun _ => val (tt, s).

Definition get : LLI state :=
  fun s => val (s, s).

Definition undefined {A : Type} (code : nat ): LLI A :=
  fun s => undef code s.

Definition run {A : Type} (m : LLI A) (s : state)  : option A :=
match m s with 
   |undef _ _=> None 
   | val (a, _) => Some a
   end.
 
Notation "'perform' x ':=' m 'in' e" := (bind m (fun x => e))
    (at level 60, x ident, m at level 200, e at level 60,
     format "'[v' '[' 'perform'  x  ':='  m  'in' ']' '/' '[' e ']' ']'") 
                                         : state_scope.

Notation "m1 ;; m2" := (bind m1 (fun _ => m2))
            (at level 60, right associativity) : state_scope.


Definition page := nat.

Definition next (x : LLI nat) := bind x (fun x => ret (S x)).

Open Scope state_scope.

(**********************************************************************)

(* shallow representation of recursive function using 'iterate' *)

Fixpoint iterate {A B : Type} (f0 : A -> LLI B)
                                (f1: (A -> LLI B) -> (A -> LLI B))
                                (n: nat) (a: A) : LLI B :=
  match n with
    | 0 => f0 a
    | S n' => f1 (iterate f0 f1 n') a 
  end.                    


(* example 1 *)

Fixpoint fact (n: nat) : nat :=
  match n with 0 => 1 | (S m) => (S m) * fact m end.

Definition fact0 := fun n:nat => 1. 

Definition fact1 := fun (f: nat -> nat) (n: nat) =>
                      match n with 0 => 1 | (S m) => (S m) * f m end.

Definition factM0 := fun n:nat => ret 1. 

Definition factM1 := fun (f: nat -> LLI nat) (n: nat) =>
                       match n with 0 => ret 1 | (S m) =>
                              bind (f m) (fun x => ret (x * (S m))) end.

Definition factM (n: nat) := iterate factM0 factM1 n n.   

(* example 2 *)

Fixpoint lengthN (ls: list nat) : nat :=
  match ls with [] => 0 | h::tl => 1 + lengthN tl end.   

Definition lengthN0 := fun ls: list nat => 0.

Definition lengthN1 := fun (f: list nat -> nat) (ls: list nat) =>  
           match ls with [] => 0 | h::tl => 1 + f tl end. 

Definition lengthNM0 := fun ls: list nat => ret 0.

Definition lengthNM1 := fun (f: list nat -> LLI nat) (ls: list nat) =>  
                          match ls with [] => ret 0 | h::tl =>
                              bind (f tl) (fun x => ret (x + 1)) end. 

Definition lengthNM (n: nat) (ls: list nat) :=
                          iterate lengthNM0 lengthNM1 n ls.   

(* example 3 *)

Fixpoint dummyRec2 timeout (arg : nat) : LLI nat :=
  match timeout with
  | 0 => ret arg
  | S timeout1 =>
    bind (ret (S arg)) (dummyRec2 timeout1)
  end.       


Definition dummyRecI0 := fun n:nat => ret n. 

Definition dummyRecI1 := fun (f: nat -> LLI nat) (n: nat) =>
                                        bind (ret (S n)) f.

Definition dummyRecI timeout (arg : nat) : LLI nat :=
  iterate dummyRecI0 dummyRecI1 timeout arg.

Lemma dummyEq (timeout arg : nat) :
  dummyRec2 timeout arg = dummyRecI timeout arg. 
  revert arg.
  induction timeout.
  auto.
  intros.
  simpl.
  simpl.
  unfold bind.
  simpl.
  eapply functional_extensionality_dep.
  rewrite IHtimeout.
  intros.
  reflexivity.
Qed.  

(************************************************************************)

(* Pip function definition *)

(* original definition *)
Fixpoint dummyRec timeout (arg : nat) : LLI nat :=
  match timeout with
  | 0 => ret arg
  | S timeout1 =>
    perform n := next (ret arg) in
    dummyRec timeout1 n
  end.

(* desugared definition *)
Fixpoint dummyRec1 timeout (arg : nat) : LLI nat :=
  match timeout with
  | 0 => ret arg
  | S timeout1 =>
    bind (ret (S arg)) (dummyRec1 timeout1)
  end.       

(**************************************************************************)

(* translation *)


Definition dummyRecD0 (x: Id) : Exp := VLift (Var x).

Definition dummyRecD1 (x: Id) (y: Id) (n: nat) : Exp :=
      BindS x (Val (cst nat (S n))) (Apply (FVar y) (PS [VLift (Var x)])). 

Definition dummyRecD (arg timeout: nat) : Fun := FC
                                nil
                                [("arg", Nat)]
                                (dummyRecD0 "arg")
                                (dummyRecD1 "arg" "dummyRec" arg)
                                "dummyRec"
                                timeout.

(* alternatives *)

(* 1 *)
Definition dummyRecD0x (n: nat) : Exp := Val (cst nat n).

Definition dummyRecD1x (y: Id) (n: nat) : Exp :=
      Apply (FVar y) (PS [(Val (cst nat (S n)))]). 

Definition dummyRecDx (arg timeout: nat) : Fun := FC
                                nil
                                [("arg", Nat)]
                                (dummyRecD0x arg)
                                (dummyRecD1x "dummyRec" arg)
                                "dummyRec"
                                timeout.

Definition dummyRecDxx (arg: nat) : Fun := FC
                                nil
                                [("arg", Nat)]
                                (dummyRecD0x arg)
                                (dummyRecD1x "dummyRec" arg)
                                "dummyRec"
                                arg.

(* 2 *)

Definition dummyRecD0v (n: ValueI nat) : Exp := Val (existT ValueI nat n).

Definition dummyRecD1v (y: Id) (n: ValueI nat) : Exp :=
  match n with Cst _ v => 
      Apply (FVar y) (PS [(Val (cst nat (S v)))]) end. 

Definition dummyRecDv (arg: ValueI nat) (timeout: nat) : Fun := FC
                                nil
                                [("arg", Nat)]
                                (dummyRecD0v arg)
                                (dummyRecD1v "dummyRec" arg)
                                "dummyRec"
                                timeout.

Definition dummyRecDvv (arg: ValueI nat) : Fun := FC
                                nil
                                [("arg", Nat)]
                                (dummyRecD0v arg)
                                (dummyRecD1v "dummyRec" arg)
                                "dummyRec"
                                (ValueI2T nat arg).


(************************************************************************)

(* Essayons de convertir la fonction suivante, de type : page -> LLI page *)
(* Definition getPd partition := *)
(*   perform idxPD := getPDidx in *)
(*   perform idx := MALInternal.Index.succ idxPD in *)
(*   readPhysical partition idx. *)

(* sample manual translation from Pip *)

Definition PartitionType := vtyp nat. 
Definition IdxType := vtyp nat. 

(*** to be implemented using Modify *)
Variable IndexSuccImpl : QValue -> Exp.
Variable ReadPhysicalImpl : QValue -> QValue -> Exp.
(***)

Definition IndexSucc : Fun := FC
                             nil 
                             [("i_arg", IdxType)]
                             (ReadPhysicalImpl (Var "p_arg")
                                               (Var "i_arg"))
                             (Val (cst nat 0))
                             ("ReadPhysical")
                             0.

Definition ReadPhysical : Fun := FC
                             nil
                             [("p_arg", PartitionType);("i_arg", IdxType)]
                             (ReadPhysicalImpl (Var "p_arg")
                                               (Var "i_arg"))
                             (Val (cst nat 0))
                             "ReadPhysical"
                             0.

Definition PerformIdxInReadPhysical : Exp :=
  BindS "idxPD"
        (VLift (Var "getPDix"))
        (BindS "idx"
               (Apply (FVar "IndexSucc")
                      (PS [(VLift (Var "idxPD"))]))
               (Apply (QF ReadPhysical)
                      (PS [(VLift (Var "partition"));
                           (VLift (Var "idx"))]))).

Definition getPd : Fun := FC
       [("ReadPhysical", ReadPhysical); ("IndexSucc", IndexSucc)]         
       [("partition", PartitionType)] 
       PerformIdxInReadPhysical
       (Val (cst nat 0))
       "getPd"
       0.


(**********************************************************************)

(* simpler example - typing a recursive function *)

Definition dRecD0 (x: Id): Exp := Return LL (Var x).

Definition dRecD1 (x rec: Id): Exp :=
  Apply (FVar rec) (PS [Return LL (Var x)]).

Definition dRecD (timeout: nat) : Fun := FC nil
                                      [("arg", Nat)]
                                      (dRecD0 "arg")
                                      (dRecD1 "arg" "dRecD")
                                      "dRecD"
                                      timeout.

Definition dRecFT : FTyp := FT [("arg", Nat)] Nat.

Definition dRecPT : PTyp := PT [Nat].

Definition dApp : Exp :=
  Apply (QF (dRecD 2)) (PS [Val (cst nat 2)]).


Definition expTypingTest (e: Exp) (t: VTyp): Type :=
  ExpTyping emptyE emptyE emptyE e t.


Definition expTypingTestA (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
           (e: Exp) (t: VTyp): Type :=
  ExpTyping ftenv tenv fenv e t.


Lemma expTypingTestDAppA (ftenv: funTC) (tenv: valTC) (fenv: funEnv) 
  (k1: MatchEnvsT FunTyping fenv ftenv) :
  expTypingTestA ftenv tenv fenv dApp Nat.
  unfold expTypingTestA.
  unfold dApp.
  econstructor.

  (* pt = env2ptyp fps *)
  instantiate (2:= dRecPT).
  instantiate (1:= [("arg",Nat)]).
  auto.
  
  apply k1.

  (* QFunTyping 2 *)
  constructor.
  econstructor.
  econstructor.

  (* dRecD1  1 *)
  econstructor.

  (* pt = env2ptyp fps *)
  instantiate (2:= dRecPT).
  instantiate (1:= [("arg",Nat)]).
  auto.
  
  constructor.
  
  (* FunTyping 1 *)
  econstructor.
  econstructor.

  (* dRecD1  0 *)
  econstructor.

  (* pt = env2ptyp fps *)  
  instantiate (2:= dRecPT).
  instantiate (1:= [("arg",Nat)]).
  auto.  

  econstructor.
  
  (* FunTyping 0 *)
  econstructor.
     
  econstructor.
  repeat constructor.
     
  constructor.

  (* QFunTyping 0 *)
  econstructor.
  econstructor.

  instantiate (1:=dRecD 0).
  econstructor.
  repeat econstructor.
  repeat econstructor.
  instantiate (1:=emptyE).
  econstructor.
  instantiate (1:=emptyE).
  econstructor.
  repeat econstructor.

  (* update 0 *)
  simpl.
  unfold updateE.
  unfold dRecD.
  auto.
  auto. 

  (* PrmsTyping *)
  econstructor.
  constructor.
  constructor.
  repeat constructor.  
  constructor.
  
  (* FunTyping 0 *) 
  econstructor.
     
  econstructor.
  repeat constructor.
     
  constructor.

  (* QFunTyping 1 *)
  econstructor.
  econstructor 1 with (ls1:=nil) (ls3:=nil) (ls2:=nil) (ls4:=nil).
  instantiate (1:=dRecD 1).
  econstructor.
  econstructor.
  econstructor.
  instantiate (1:=[("arg", Nat)]).
  reflexivity.
  
  econstructor.
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
  instantiate (1:=dRecD 0).

  econstructor 1 with (ls1:=nil) (ls3:=nil) (ls2:=nil) (ls4:=nil).
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
  simpl.
  reflexivity.

  econstructor.
  simpl.
  reflexivity.  
  
  (* PrmsTyping *)
  econstructor.
  constructor.
  constructor.
  repeat constructor.  
  constructor.

  (* FunTyping 0 *) 
  econstructor.
     
  econstructor.
  repeat constructor.

  constructor. 
  econstructor.
  simpl.
  reflexivity.

  (* PrmsTyping *)
  econstructor.
  constructor.
  constructor.
  repeat constructor.  

  (* FunTyping 1 *)
  econstructor.
 
  econstructor.

  (* dRecD1  *)
  econstructor.

  (* pt = env2ptyp fps *)
  instantiate (2:= dRecPT).
  instantiate (1:= [("arg",Nat)]).
  auto.
  
  repeat constructor.

  econstructor.
  econstructor.
  repeat constructor.

  econstructor.
  econstructor.

  instantiate (1:=dRecD 0).
  econstructor.
  econstructor.
  repeat constructor.

  instantiate (1:=nil).  
  econstructor.
  instantiate (1:=nil).
  econstructor.
  
  constructor.

  repeat constructor.
  repeat constructor.

  (* PrmsTyping *)
  econstructor.
  constructor.
  constructor.
  repeat constructor.  
  constructor.

  (* FunTyping 0 *) 
  econstructor.
     
  econstructor.
  repeat constructor.

  constructor.
  repeat constructor.
Defined.  


(*
Definition succIndexInternal (idx: index) : Exp :=
  BindS i (extract1 idx) (BindS P (extract2 idx))
        (IfThenElse (Lt_dec i) (apply DSome 
                                   (Apply IndexSucc (Var i))) DNone) .
*)

(*
Definition plusR_X (n:nat) := QF (FC emptyE [("i",Nat)]
       (VLift (Var "i"))
       (SuccR_X (Apply (FVar "plusR") (PS [VLift (Var "i")])))
       "plusR" n).

Definition plusX := FC emptyE [("i",Nat),("j",Nat)]
    (Val 0)
    (IfThenElse (EEqual 0 "j")
                (VLift (Var "i"))
                (Apply (FVar "plusR") (PS [VLift (Var "i"), PredR "j"]))).
*)

End Convert2.

(*

(* il faudrait bien commencer par définir l’ensemble des identifiants possibles ?
   est-ce que tricher avec un type comme string serait faisable ? *)
Inductive Id : Type := partition | idxPD | idx.
(* Mais je n’arrive pas à créer de valeur de type TPipStatic20.Id, qui
   est le type attendu, est-ce normal ? *)

(* comment se fait qu’About Fun n’indique pas de dépendance à un type Id ? *)
Definition corps : Exp.
Admitted.

Definition getPdFun : Fun := FC nil nil corps corps partition 0.
  (* FC : pas d’autre choix de toute façon *)
  (* [] : pas d’environnements, si ? que pourraient-ils contenir ? *)
  (* [] : des constantes, comme par exemple la valeur de N ? *)
  (* corps *)
  (* corps : ici, il n’est pas nécessaire de faire une différence entre les cas 0 et 1, si ? *)
  (* partition : c’est bien l’argument ? *)
  (* 0. *)

 *)

