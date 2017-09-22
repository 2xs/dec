(* DEC 1.0 language specification.
   Paolo Torrini and David Nowak, 
   Universite' Lille-1 - CRIStAL-CNRS
*)

Require Import List.

Import ListNotations.


(** * DEC 1.0 auxiliary library *)

(** Auxiliary definitions and type classes *) 

(* *)

(** Decidable equality class *)

Class DEq (K: Type) : Type := {
   dEq : forall x y: K, {x = y} + {x <> y}
}.  


(** Admissible value type class *)

Class ValTyp (T: Type) : Prop. 

    
(** Pip state class *)  

Class PState (W: Type) : Type := {

   loc_pi : forall (T: Type) (p1 p2: ValTyp T), p1 = p2;

   b_init : W ;
}.

(************************************************************************)

(** Environment type *)

Definition Envr (K V: Type) : Type := list (K * V).

Definition emptyE {K V: Type}: Envr K V := nil.

Definition overrideE {K V: Type}  
    (f1 f2: Envr K V) : Envr K V := app f1 f2.

Definition updateE {K V: Type} (g: Envr K V) (z: K) (t: V) :
    Envr K V := cons (z, t) g.

Definition singleE {K V: Type} (z: K) (t: V) : 
   Envr K V := cons (z, t) emptyE. 

Fixpoint findE {K V: Type} {h: DEq K} (m: Envr K V) (k: K) : option V :=
  match m with
     | nil => None
     | cons (k', x) ls => match (dEq k k') with
                            | left _ => Some x
                            | right _ => findE ls k
                            end               
    end.

Inductive disjoint {K V: Type} {h: DEq K} (m1 m2: Envr K V) : Prop :=
   disjoint1 : (forall x: K, or (findE m1 x = None) (findE m2 x = None)) -> 
                   disjoint m1 m2.

Inductive includeEnv {K V: Type} {h: DEq K} (m1 m2: Envr K V) : Prop :=
  includeEnv1 : (forall x: K, or (findE m1 x = None)
                                 (findE m1 x = findE m2 x)) -> 
                   includeEnv m1 m2.

Inductive findEP {K V: Type} {h: DEq K} (m: Envr K V) (k: K) : V -> Prop :=
  FindEP : forall x: V, findE m k = Some x -> findEP m k x.

Inductive findEP2 {K V: Type} {h: DEq K} (m: Envr K V) (k: K) : V -> Prop :=
  FindEP2 : forall (v: V) (m0 m1: Envr K V),
            m = overrideE m0 (updateE m1 k v) ->  
            findE m0 k = None ->  
            findEP2 m k v.

Inductive findET {K V: Type} {h: DEq K} (m: Envr K V) (k: K) : V -> Type :=
  FindET : forall x: V, findE m k = Some x -> findET m k x.


Fixpoint interleave {V1 V2: Type} (ls1 : list V1) (ls2: list V2) :
                                                    list (V1 * V2) :=
  match ls1 with
    | nil => nil 
    | cons x ts1 => match ls2 with
               | nil => nil          
               | cons y ts2 => cons (x,y) (interleave ts1 ts2)
               end                                   
  end.


(************************************************************************)

(** Relations on environments and lists *)

Inductive MatchEnvsT {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type) : 
          Envr K V1 -> Envr K V2 -> Type :=
| MatchEnvs_NilT : MatchEnvsT rel nil nil
| MatchEnvs_ConsT : forall ls1 ls2 k v1 v2,
                     rel v1 v2 ->
                     MatchEnvsT rel ls1 ls2 ->
                     MatchEnvsT rel ((k,v1)::ls1) ((k,v2)::ls2).

Inductive MatchEnvs2BT {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type)  
          (k: K) (v1: V1) (v2: V2) : Envr K V1 -> Envr K V2 -> Type :=
| MatchEnvs2B_splitT : forall ls5 ls6 ls1 ls2 ls3 ls4,
                     rel v1 v2 ->
                     MatchEnvsT rel ls1 ls2 ->
                     MatchEnvsT rel ls3 ls4 ->
                     findE ls2 k = None -> 
                     ls5 = ls1 ++ ((k,v1)::ls3) ->
                     ls6 = ls2 ++ ((k,v2)::ls4) ->
            MatchEnvs2BT rel k v1 v2 ls5 ls6.                         

Inductive ForallT {A: Type} (P: A -> Type): list A -> Type :=
      | Forall_nilT : ForallT P nil
      | Forall_consT : forall x l, P x -> ForallT P l -> ForallT P (x::l).

Inductive Forall2T {A B : Type} (R: A -> B -> Type): 
    list A -> list B -> Type := 
  | Forall2_nilT : Forall2T R nil nil
  | Forall2_consT : forall x y l l',
      R x y -> Forall2T R l l' -> Forall2T R (x::l) (y::l').


