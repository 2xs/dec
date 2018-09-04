(* DEC 2.0 language specification.
   Paolo Torrini, 
   Universite' de Lille - CRIStAL-CNRS
*)

(* coq_makefile *.v -o Makefile -Q . "" *)

Require Import List. 
Require Export Equality.
Require Import Eqdep.
Require Import PeanoNat.
Require Import Omega.

Import ListNotations.


(** * DEC 2.0 auxiliary library *)

(** Auxiliary definitions and type classes *) 

(** Decidable equality class *)

Class DEq (K: Type) : Type := {
   dEq : forall x y: K, {x = y} + {x <> y}
}.  

(***********************************************************************)

(* lemmas about lists *)

Lemma map_eq_nil {A B: Type} (f: A -> B): forall l, map f l = [] -> l = [].
  intros.
  induction l.
  reflexivity.
  inversion H.
Defined.  

Lemma app_nil_l {A: Type} : forall l:list A, [] ++ l = l.
  intros.
  simpl.
  reflexivity.
Defined.

Lemma app_nil_r {A: Type} : forall l:list A, l ++ [] = l.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl in *.
  rewrite IHl.
  reflexivity.
Defined.

Lemma app_comm_cons {A: Type} :
  forall (x y:list A) (a:A), a :: (x ++ y) = (a :: x) ++ y.
  intros.
  simpl.
  reflexivity.
Defined.

Lemma map_length {A B: Type} (f: A -> B): forall l,
    length (map f l) = length l.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Defined.

Lemma length_zero_iff_nil {A: Type} (l : list A):
    length l = 0 <-> l = [].
  constructor.
  induction l.
  intro.
  reflexivity.
  intros.
  inversion H.
  induction l.
  auto.
  intros.
  inversion H.
Defined.

Lemma app_assoc {A: Type} : forall l m n:list A, l ++ m ++ n = (l ++ m) ++ n.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Defined.


Lemma map_id : forall (A :Type) (l : list A),
    map (fun x => x) l = l.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Defined.
  
Lemma map_map : forall (A B C:Type)(f:A->B)(g:B->C) l,
  map g (map f l) = map (fun x => g (f x)) l.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Defined.  

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


(*************************************************************************)

Definition EnvrAssign {K V: Type} {h: DEq K} :
      Envr K V -> K -> V -> Prop :=
        fun (env: Envr K V) (x: K) (t: V) => 
                    findE env x = Some t.

Definition EnvrDAssign {K V1 V2: Type} {h: DEq K} (f: V2 -> V1) :
      Envr K V2 -> K -> V1 -> Prop :=
   fun (env: Envr K V2) (x: K) (t1: V1) =>
                   forall (t2: V2), 
                     (findE env x = Some t2) * (t1 = f t2).


(************************************************************************)

(** Relations on environments and lists *)

Inductive MatchEnvsT {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type) : 
          Envr K V1 -> Envr K V2 -> Type :=
| MatchEnvs_NilT : MatchEnvsT rel nil nil
| MatchEnvs_ConsT : forall ls1 ls2 k v1 v2,
                     rel v1 v2 ->
                     MatchEnvsT rel ls1 ls2 ->
                     MatchEnvsT rel ((k,v1)::ls1) ((k,v2)::ls2).

Inductive ForallT {A: Type} (P: A -> Type): list A -> Type :=
      | Forall_nilT : ForallT P nil
      | Forall_consT : forall x l, P x -> ForallT P l -> ForallT P (x::l).

Inductive Forall2T {A B : Type} (R: A -> B -> Type): 
    list A -> list B -> Type := 
  | Forall2_nilT : Forall2T R nil nil
  | Forall2_consT : forall x y l l',
      R x y -> Forall2T R l l' -> Forall2T R (x::l) (y::l').


(************************************************************************)

(* proof irrelevance lemmas *)

Lemma ForallT_PI {A: Type} (P: A -> Type) (ls: list A)
      (e1 e2: ForallT P ls) :
  (forall (x: A) (p1 p2: P x), p1 = p2) ->  
  e1 = e2.
  dependent induction e1.
  dependent destruction e2.
  intros.
  reflexivity.
  dependent destruction e2.
  intros.
  specialize (IHe1 e2 H).
  specialize (H x p p0).
  inversion H; subst.
  reflexivity.
Defined.  

Lemma Forall2T_PI {A B : Type} (R: A -> B -> Type)
      (ls1: list A) (ls2: list B) 
      (e1 e2: Forall2T R ls1 ls2) :  
  (forall (x: A) (y: B) (p1 p2: R x y), p1 = p2) -> e1 = e2.
  dependent induction e1.
  dependent destruction e2.
  intros.
  reflexivity.
  dependent destruction e2.
  intros.
  specialize (IHe1 e2 H).
  specialize (H x y r r0).
  inversion H; subst.
  reflexivity.
Defined.  

(************************************************************************)

(* more relations *)

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

Inductive Forall3T {A B C : Type} (R: A -> B -> C -> Type): 
    list A -> list B -> list C -> Type := 
  | Forall3_nilT : Forall3T R nil nil nil
  | Forall3_consT : forall x y z l1 l2 l3,
                      R x y z -> Forall3T R l1 l2 l3 ->
                      Forall3T R (x::l1) (y::l2) (z::l3).


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
           (env1: Envr K V1) (env2: Envr K V2) : Prop :=
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

(*******************************************************************)

(** lemmas on interleave *)

Lemma listLengthAux1 {A B: Type} (ls1 : list A) (ls2 : list B) :
      (length ls1 = length ls2) -> ls2 = map snd (interleave ls1 ls2).
Proof.
  revert ls1.
  induction ls2.
  intros.  
  assert (interleave ls1 nil = @nil (prod A B)).
  induction ls1.
  simpl.
  auto.  
  simpl.
  auto.
  rewrite H0.
  simpl.
  auto.
  simpl.
  destruct ls1.
  simpl.
  intros.
  inversion H.
  simpl.
  intros.
  inversion H; subst.
  eapply IHls2 in H1.
  rewrite <- H1.
  auto.
Defined.  


(** lemmas on Forall2T *)

Lemma prmsTypingAux1_T {A T V: Type} (R: V -> T -> Type)
        (fps : list (A * T)) (vls : list V)
        (h2: length fps = length vls):
  Forall2T R vls (map snd fps) ->
  Forall2T R (map snd (interleave (map fst fps) vls))
               (map snd fps).
Proof.
  assert (length (map fst fps) = length vls).
  symmetry.
  rewrite <- h2.
  rewrite map_length.
  reflexivity.
  intros.
  generalize H.
  intros.
  eapply listLengthAux1 in H0.
  rewrite <- H0.
  auto.
Defined.


Lemma prmsTypingAux2_T {A T V: Type} {h: DEq A} (R: V -> T -> Type)
      (fps : list (A * T)) (vls : list V) 
      (h2: length fps = length vls):
  (Forall2T R (map snd (interleave (map fst fps) vls))
                (map snd fps)) ->
  (MatchEnvsT R (interleave (map fst fps) vls) fps).        
Proof.
  assert (length (map fst fps) = length vls).
  symmetry.
  rewrite <- h2.
  rewrite map_length.
  reflexivity.
  eapply listLengthAux1 in H.
  rewrite <- H.
  intro.
  dependent induction X.
  simpl in h2.
  eapply length_zero_iff_nil in h2.
  inversion h2; subst.
  simpl.
  constructor.
  destruct fps.
  simpl in h2.
  inversion h2.
  simpl.
  simpl in h2.
  inversion h2; subst.
  simpl in H.
  inversion H; subst.
  simpl in x.
  inversion x; subst.
  destruct p.
  simpl in r.
  simpl.
  econstructor.
  assumption.
  rewrite <- H2.
  eapply IHX.
  auto.
  auto.
  auto.
Defined.  

Lemma sameBehSameLength_T {A B: Type} (R : A -> B -> Type)
        (ls1: list A) (ls2: list B) : Forall2T R ls1 ls2 ->
            length ls1 = length ls2.                            
Proof.
  intros.
  induction X.
  reflexivity. 
  simpl.
  auto.
Defined.  

(***********************************************************************)

(* lemmas on min *)

Lemma min_idem1 (n0 n1: nat) : min n0 n1 <= n0.   
    dependent induction n0.
    simpl.
    auto.
    simpl.
    destruct n1.
    omega.
    specialize (IHn0 n1).
    omega.
Defined.

Lemma min_zero (n: nat) : n <= 0 -> n = 0.
  induction n.
  auto.
  intros.
  intuition.
Defined.
  
Lemma min_eq (n0 n1: nat) : min n0 n1 <= min n1 n0.
  dependent induction n0.
  simpl.
  omega.
  simpl.
  destruct n1.
  omega.
  simpl.
  specialize (IHn0 n1).
  omega.
Defined.

Lemma min_idem2 (n0 n1: nat) : min n0 n1 <= n1.
  rewrite min_eq.
  eapply min_idem1.
Defined.

(** lemmas on projections *)

Definition snd_sigT_of_sigT2 {A : Type} {P Q : A -> Type} (X : sigT2 P Q) :
   sigT Q
  := existT Q
            (let (a, _, _) := X in a)
            (let (x, _, q) as s return (Q (let (a, _, _) := s in a)) := X in q).

Definition proj1_of_sigT2 {A : Type} {P Q : A -> Type} (X : sigT2 P Q) : A :=
           (projT1 (sigT_of_sigT2 X)).

Definition fst_sigT_of_sigT2 {A : Type} {P Q : A -> Type} (X : sigT2 P Q) :
   sigT P
  := existT P
            (let (a, _, _) := X in a)
            (let (x, p, _) as s return (P (let (a, _, _) := s in a)) := X in p).


(* lemmas about <= *)

Lemma le_inject (n1 n2: nat) : S n1 <= S n2 -> n1 <= n2.
  intuition.
Defined.  

Lemma le_decrease (n1 n2: nat) : S n1 <= n2 -> n1 <= n2.
  intuition.
Defined.
      
(**************************************************************)

(* used in the translation *)

Definition noDup {K V: Type} (ls: list (K * V)) :=
  NoDup (map fst ls).

Lemma noDup_prop {K V: Type} (ls: list (K * V)) (x: K) (v: V) :
  noDup ((x,v)::ls) -> noDup ls.
  unfold noDup.
  intros.
  simpl in *.
  inversion H; subst.
  exact H3.
Defined.

Lemma someMember {K V: Type} {h: DEq K} (ls: list (K * V)) (x: K) (v: V) :
  findE ls x = Some v ->
  In x (map fst ls).
  induction ls.
  intros.
  simpl in H.
  inversion H.
  intros.
  destruct a.
  simpl in *.
  destruct (dEq x k) in H.
  left.
  symmetry.
  exact e.
  right.
  eapply IHls.
  exact H.
Defined.  

Lemma distThendiff {A: Type} (ls: list A) (x x0: A) :      
  ~ In x ls -> In x0 ls -> x0 <> x.
  induction ls.
  intros.
  simpl in H0.
  intuition H0.
  intros.
  simpl in H.
  simpl in H0.
  intuition.
  inversion H1; subst.
  eapply H0 in H4.
  auto.
Defined.


Fixpoint suffix {A: Type} (ls1 ls2: list A) : Prop :=
  match ls1 with
  | nil => True
  | _ => match ls2 with
         | nil => False
         | c::cs => (ls1 = ls2) \/ suffix ls1 cs
         end
  end.             
 

Lemma in_pairs_lemma {K V: Type} (ls: list (K * V))
        (k: K) (v: V) : In (k, v) ls -> (In k (map fst ls)).
  induction ls.
  simpl.
  auto.
  destruct a.
  simpl in *.
  intro.
  destruct H.
  inversion H; subst.
  left.
  auto.
  right.
  eapply IHls.
  exact H.
Defined.  


Lemma in_find_lemma {K V: Type} {h: DEq K} (ls: list (K * V)) (x: K) (v: V) :
    In (x,v) ls -> noDup ls -> findE ls x = Some v.
  intros.
  induction ls.
  inversion H.
  destruct a.
  simpl in *.
  destruct (dEq x k).
  destruct H.
  inversion H; subst.
  auto.
  inversion e; subst.
  unfold noDup in H0.
  inversion H0; subst.
  simpl in *.
  eapply in_pairs_lemma in H.
  intuition.
  destruct H.
  inversion H; subst.
  intuition n.
  specialize (IHls H).
  eapply IHls.
  eapply noDup_prop.
  exact H0.
Defined.  

(********************************************************************)

Lemma pairLeftEq {T1 T2: Type} :
  forall (a b:T1) (c:T2), a = b -> (a,c) = (b,c).
  intros.
  rewrite H.
  reflexivity.
Defined.    


Lemma ExchangeD {A B: Type} {C: A -> Type} :
    (forall x:A, B -> C x) ->
    (B -> forall x:A, C x).
  intros.
  auto.
Defined.  


Lemma Exchange13 {A B: Type} (g: B -> Type)
      (f: A -> forall y:B, g y -> Type) :
    (forall (x:A) (y:B) (z:g y), f x y z) ->
    (forall (y:B) (z:g y) (x:A), f x y z).
      intros.
      auto.
Defined.    


Lemma lengthSnd {A B: Type} (ls: list (A * B)) :
  length (map snd ls) = length ls.   
  induction ls.
  simpl.
  auto.
  simpl in *.
  rewrite IHls.
  auto.
Defined.  


Lemma eq_sym_lemma {A: Type} (x y: A) : (x = y) -> (x = y) = (y = x).
  intros.
  rewrite H.
  auto.
Defined.  

