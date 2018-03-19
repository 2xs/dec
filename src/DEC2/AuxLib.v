(* DEC 2.0 language specification.
   Paolo Torrini, 
   Universite' Lille-1 - CRIStAL-CNRS
*)

Require Import List.

Import ListNotations.


(** * DEC 2.0 auxiliary library *)

(** Auxiliary definitions and type classes *) 

(* *)

(** Decidable equality class *)

Class DEq (K: Type) : Type := {
   dEq : forall x y: K, {x = y} + {x <> y}
}.  

    
(***********************************************************************)

Fixpoint tlist2type (ts: list Type) : Type :=
  match ts with
    | nil => unit
    | (t::ts') => t * tlist2type ts'
  end.                               


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


(************************************************************************)
(* NEW *)

(*
Inductive FAssign {K V: Type} 
                   (f: K -> V) (k: K) (t: V) : Type :=
| FAssignC : t = f k -> FAssign f k t.
*)

Inductive Forall3T {A B C : Type} (R: A -> B -> C -> Type): 
    list A -> list B -> list C -> Type := 
  | Forall3_nilT : Forall3T R nil nil nil
  | Forall3_consT : forall x y z l1 l2 l3,
                      R x y z -> Forall3T R l1 l2 l3 ->
                      Forall3T R (x::l1) (y::l2) (z::l3).


Inductive EnvrAssign {K V: Type} {h: DEq K} :
      Envr K V -> K -> V -> Type :=
   | EnvrAssignC : forall (env: Envr K V) (x: K) (t: V), 
                    findE env x = Some t -> 
                    EnvrAssign env x t.

Inductive EnvrDAssign {K V1 V2: Type} {h: DEq K} (f: V2 -> V1) :
      Envr K V2 -> K -> V1 -> Type :=
   | EnvrDAssignC : forall (env: Envr K V2) (x: K) (t1: V1), 
                   forall (t2: V2), 
                     findE env x = Some t2 ->
                     t1 = f t2 -> 
                     EnvrDAssign f env x t1.


(*************************************************************************)
(******************* PROOFS **********************************************)

(** lemmas on find *)

(* find_simpl *)
Lemma find_simpl0 {K V: Type} {h: DEq K}
      (env: Envr K V) (x: K) (v: V) :
  findE ((x, v) :: env) x = Some v.
  simpl.
  destruct (dEq x x).
  auto.
  intuition n.
Defined.  

(* find_persists1 *)
Lemma find_simpl1 {K V: Type} {h: DEq K}
      (env1 env2: Envr K V) (x y: K) (v: V) :
  findE env1 y = findE env2 y ->
  findE ((x, v) :: env1) y = findE ((x, v) :: env2) y. 
Proof.
  intros.
  simpl.
  destruct (dEq y x).
  auto.
  auto.
Defined.  

(* find_persists2 *)
Lemma find_simpl2 {K V: Type} {h: DEq K}
      (env: Envr K V) (x y: K) (v: V) :
  findE ((x, v) :: env) y = None ->
  findE env y = None.
  simpl.
  intros.
  destruct (dEq y x) in H.
  inversion H.
  auto.
Defined.  

(* find_persists3 *)
Lemma find_simpl3 {K V: Type} {h: DEq K}
      (env: Envr K V) (x y: K) (v: V) :
  findE ((x, v) :: env) y = None ->
  x <> y.
  simpl.
  intros.
  destruct (dEq y x) in H.
  inversion H.
  auto.
Defined.  

(* find_persists4 *)
Lemma find_simpl4 {K V: Type} {h: DEq K}
      (env: Envr K V) (x y: K) (v: V) :
  x <> y -> findE ((x, v) :: env) y = findE env y. 
  intros.
  simpl.
  destruct (dEq y x).
  rewrite e in H.
  intuition.
  auto.
Defined.

(* overrideRedux1 *)
Lemma override_simpl1 {K V: Type} {h: DEq K}
      (env1 env2: Envr K V) (x: K) (v: V) :
  findE env1 x = Some v -> findE (env1 ++ env2) x = findE env1 x.
Proof.
  induction env1.
  intros.
  simpl in H.
  inversion H.
  destruct a.
  simpl.
  destruct (dEq x k).
  auto.
  auto.
Defined.

(* overrideRedux2 *)
Lemma override_simpl2 {K V: Type} {h: DEq K}
      (env1 env2: Envr K V) (x: K) :
  findE env1 x = None -> findE (env1 ++ env2) x = findE env2 x.
Proof.
  induction env1.
  intros.
  rewrite app_nil_l.
  auto.
  destruct a.
  intros.
  set (G := (findE ((k, v) :: env1) x = None)).
  assert G.
  auto.
  assert G.
  auto.
  apply find_simpl2 in H0.
  apply find_simpl3 in H1.
  set (J := (findE env1 x = None)).
  assert J.
  auto.
  rewrite <- app_comm_cons.
  apply IHenv1 in H2.  
  eapply find_simpl4 in H1.
  erewrite H1.
  apply IHenv1 in H0.
  auto.
Defined.

(* findEexApp *)
Lemma override_simpl3 {K V: Type} {h: DEq K} (env env0: Envr K V) (x: K):
    findE env0 x = None -> findE env x = findE (env0 ++ env) x. 
intros.
induction env.
simpl.
rewrite app_nil_r.
symmetry.
assumption.
destruct a.
revert IHenv.
simpl.
revert H.
induction env0.
simpl.
intros.
reflexivity.
destruct a.
simpl.
destruct (dEq x k0).
intros.
inversion H.
intros.
destruct (dEq x k).
apply IHenv0.
assumption.
assumption.
apply IHenv0.
assumption.
assumption.
Defined.

(* findEextCons *)
Lemma update_simpl1 {K V: Type} {h: DEq K} (env: Envr K V) (x y: K) (v: V):
    x <> y -> findE env x = findE ((y, v) :: env) x. 
intros.
induction env.
simpl.
destruct (dEq x y).
rewrite e in H.
intuition.
reflexivity.
simpl.
destruct a.
simpl in IHenv.
revert IHenv.
destruct (dEq x y).
rewrite e in H.
intuition H.
intros.
reflexivity.
Defined.


Lemma findE_Some {K V: Type} {h: DEq K} (ls: Envr K V) (x: K) (v: V) :
           findE ls x = Some v ->
                   exists ls1 ls2, findE ls1 x = None /\
                                   ls = ls1 ++ ((x,v) :: ls2).  
Proof.
  intros.
  induction ls.
  simpl in H.
  inversion H.
  inversion H; subst.
  destruct a.
  destruct (dEq x k) in H1.
  inversion H1; subst.
  exists nil.
  exists ls.
  split.
  simpl.
  auto.
  simpl.
  auto.
  specialize (IHls H1).
  destruct IHls as [ls1 H0].
  destruct H0 as [ls2 H0].
  destruct H0.
  exists ((k,v0)::ls1).
  exists ls2.
  split.
  simpl.
  destruct (dEq x k).
  intuition.
  auto.
  simpl.
  rewrite <- H2.
  auto.
Defined.  

(**************************************************************************)

(** lemmas on environment relations (for EnvTyping, FEnvTyping) *) 

Definition thicken (K: Type) {V1 V2: Type} (f: V1 -> V2) :
           (K * V1) -> (K * V2) :=
  fun p => (fst p, f (snd p)).


Definition MatchEnvs (K: Type) {V1 V2: Type} (f: V1 -> V2)
           (env1: Envr K V1) (env2: Envr K V2) :=
  env2 = map (thicken K f) env1.
           

Lemma emptyEnvLemma (K: Type) {V1 V2: Type} (f: V1 -> V2) :
    MatchEnvs K f nil nil.  
Proof.
  unfold MatchEnvs in *.
  unfold thicken in *.
  simpl.
  reflexivity.
Defined.


Lemma updateEnvLemma {K V1 V2: Type} (f: V1 -> V2)
              (env1: Envr K V1) (env2: Envr K V2) (x: K)
              (v1: V1) (v2: V2) :
    MatchEnvs K f env1 env2 ->
    f v1 = v2 -> 
    MatchEnvs K f ((x, v1)::env1) ((x, v2)::env2).  
Proof.
  intros.
  unfold MatchEnvs in *.
  unfold thicken in *.
  simpl.
  rewrite H0.
  rewrite H.
  reflexivity.
Defined.  


Lemma overrideEnvLemma {K V1 V2: Type} (f: V1 -> V2): 
     forall (env1A env1B: Envr K V1) (env2A env2B: Envr K V2), 
  MatchEnvs K f env1A env2A ->
  MatchEnvs K f env1B env2B -> 
  MatchEnvs K f (env1A ++ env1B) (env2A ++ env2B).  
Proof.
  intros.
  unfold MatchEnvs in *.
  unfold thicken in *.
  rewrite H.
  rewrite H0.
  rewrite map_app.
  reflexivity.
Defined.  
  

Lemma RelatedByEnv {K V1 V2: Type} {h: DEq K} (f: V1 -> V2) 
                     (env1: Envr K V1) (env2: Envr K V2) (x: K)
                     (v1: V1) (v2: V2)
  : MatchEnvs K f env1 env2 ->
    findE env1 x = (Some v1) -> findE env2 x = (Some v2) -> f v1 = v2.
Proof.
  revert env2.
  induction env1.
  intros.
  simpl in H0.
  inversion H0.
  intros.
  unfold MatchEnvs in *.
  unfold thicken in *.
  destruct a.
  destruct env2.
  simpl in H1.
  inversion H1.
  destruct p.
  inversion H; subst.
  simpl in *.
  destruct (dEq x k).
  inversion H0; subst.
  inversion H1; subst.
  reflexivity.
  eapply IHenv1.
  reflexivity.
  assumption.
  assumption.
Defined.  
  

Lemma ExtRelVal2 {K V1 V2: Type} {h: DEq K} (f: V1 -> V2)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2): 
    MatchEnvs K f venv tenv ->
    findE tenv x = Some t ->
    sigT2 (fun v: V1 => findE venv x = Some v) (fun v: V1 => f v = t). 
Proof.
  unfold MatchEnvs.
  unfold thicken.
  intros.
  inversion H; subst.
  induction venv.
  simpl in *.
  inversion H0.
  destruct a.
  simpl in *.
  destruct (dEq x k).
  inversion H0; subst.
  constructor 1 with (x:=v).
  reflexivity.
  reflexivity.
  eapply IHvenv.
  reflexivity.
  assumption.
Defined.  
   
 
Lemma ExtRelVal1 {K V1 V2: Type} {h: DEq K} (f: V1 -> V2)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (v: V1): 
    MatchEnvs K f venv tenv ->
    findE venv x = Some v ->
    sigT2 (fun t: V2 => findE tenv x = Some t) (fun t: V2 => f v = t). 
Proof.
  unfold MatchEnvs.
  unfold thicken.
  intros.
  inversion H; subst.
  constructor 1 with (x:= f v).
  induction venv.
  simpl in *.
  inversion H0.
  destruct a.
  simpl in *.
  destruct (dEq x k).
  inversion H0; subst.
  reflexivity.
  eapply IHvenv.
  assumption.
  reflexivity.
  reflexivity.
Defined.  
  

Lemma ExRelValNone {K V1 V2: Type} {h: DEq K} (f: V1 -> V2)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) :  
    MatchEnvs K f venv tenv ->
    findE tenv x = None ->
    findE venv x = None.
Proof.
  unfold MatchEnvs.
  unfold thicken.
  intros.
  inversion H; subst.
  induction venv.
  simpl in *.
  reflexivity.
  destruct a.
  simpl in *.
  destruct (dEq x k).
  inversion H0.
  eapply IHvenv.
  reflexivity.
  assumption.
Defined.  
  
