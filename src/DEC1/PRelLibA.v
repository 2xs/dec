Require Import Coq.Lists.List.
Require Import Omega.
Require Import Coq.Logic.ProofIrrelevance.

Require Export EnvLibA.

Import ListNotations.


Lemma valTyp_irrelevance : forall (T: Type) (p1 p2: ValTyp T), p1 = p2.
intros.
eapply proof_irrelevance.  
Qed.

(*********************************************************************)

Inductive MatchEnvs {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop) : 
          Envr K V1 -> Envr K V2 -> Prop :=
| MatchEnvs_Nil : MatchEnvs rel nil nil
| MatchEnvs_Cons : forall ls1 ls2 k v1 v2,
                     rel v1 v2 ->
                     MatchEnvs rel ls1 ls2 ->
                     MatchEnvs rel ((k,v1)::ls1) ((k,v2)::ls2).

(*********************************************************************)

(** lemmas on MatchEnvs *)

Lemma consEnvLemma {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop)
              (env1: Envr K V1) (env2: Envr K V2) (x: K)
                      (v1: V1) (v2: V2):
    MatchEnvs rel env1 env2 ->
    rel v1 v2 -> 
    MatchEnvs rel ((x, v1)::env1) ((x, v2)::env2).  
Proof.
  intros.
  constructor.
  assumption.
  assumption.
Defined.


Lemma updateEnvLemma {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop)
              (env1: Envr K V1) (env2: Envr K V2) (x: K)
                      (v1: V1) (v2: V2):
    MatchEnvs rel env1 env2 ->
    rel v1 v2 -> 
    MatchEnvs rel (updateE env1 x v1) (updateE env2 x v2).  
Proof.
  unfold updateE.
  eapply consEnvLemma. 
Defined.


Lemma app_cons_assoc {A: Type} (x: A) (ls1 ls2: list A):
       (x :: ls1) ++ ls2 = x :: (ls1 ++ ls2).
Proof.
simpl.
reflexivity.
Defined.


Lemma appEnvLemma {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop): 
     forall (env1A env1B: Envr K V1) (env2A env2B: Envr K V2), 
  MatchEnvs rel env1A env2A ->
  MatchEnvs rel env1B env2B -> 
  MatchEnvs rel (env1A ++ env1B) (env2A ++ env2B).  
Proof.
  induction env1A.
  intros. 
  induction env2A.
  simpl.
  assumption.
  inversion H.  
  induction env2A.
  intros.
  inversion H.  
  intros.
  simpl.
  destruct a.
  destruct a0.
  destruct (dEq k k0).
  Focus 2.
  inversion H; subst.  
  intuition n.
  destruct e.
  inversion H; subst.
  constructor.
  assumption.
  apply IHenv1A. 
  assumption.
  assumption.
Defined.  


Lemma overrideEnvLemma {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop): 
     forall (env1A env1B: Envr K V1) (env2A env2B: Envr K V2), 
  MatchEnvs rel env1A env2A ->
  MatchEnvs rel env1B env2B -> 
  MatchEnvs rel (env1A ++ env1B) (env2A ++ env2B).  
Proof.
  eapply appEnvLemma.
Defined.


Lemma RelatedByEnvEP {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop) 
                     (env1: Envr K V1) (env2: Envr K V2) (x: K)
                     (v1: V1) (v2: V2)
         : MatchEnvs rel env1 env2 -> findEP env1 x v1 ->
           findEP env2 x v2 -> rel v1 v2.
Proof.
  intros.
  inversion H0; subst.
  inversion H1; subst.
  induction H. 
  inversion H2.
  inversion H3; subst.
  inversion H2; subst.
  destruct (dEq x k).
  inversion H6; subst.
  inversion H7; subst.
  assumption.
  apply IHMatchEnvs.
  constructor.
  assumption.
  constructor.  
  assumption.
  assumption.
  assumption.
Defined.



Lemma RelatedByEnvEP2 {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop) 
                     (env1: Envr K V1) (env2: Envr K V2) (x: K)
                     (v1: V1) (v2: V2)
         : MatchEnvs rel env1 env2 -> findEP2 env1 x v1 ->
           findEP2 env2 x v2 -> rel v1 v2.
intros.
apply findEP2toEP in H0.
apply findEP2toEP in H1.
eapply RelatedByEnvEP.
eassumption.
eassumption.
assumption.
Defined.


Lemma ExRelVal {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2): 
    MatchEnvs R venv tenv ->
    findEP tenv x t ->
    exists v: V1, findEP venv x v /\ R v t. 
Proof.
  intros.
  induction H; subst.
  inversion H0.
  inversion H.
  inversion H0; subst.
  inversion H2; subst.
  rename v2 into t2.
  destruct (dEq x k). 
  inversion H4; subst.
  exists v1.
  split.
  constructor.
  simpl.
  destruct (dEq k k).
  auto.
  intuition n.
  assumption.
  assert (findEP ls2 x t).
  constructor.
  auto.
  eapply IHMatchEnvs in H3.
  destruct H3.
  destruct H3.
  exists x0.
  split.
  constructor.  
  simpl.
  destruct (dEq x k).
  rewrite e in n.
  intuition n.
  inversion H3; subst.
  assumption.
  assumption.
Defined.


Lemma ExRelValRev {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (v: V1): 
    MatchEnvs R venv tenv ->
    findEP venv x v ->
    exists t: V2, findEP tenv x t /\ R v t. 
Proof.
  intros.
  induction H; subst.
  inversion H0.
  inversion H.
  inversion H0; subst.
  inversion H2; subst.
  rename v2 into t1.
  destruct (dEq x k). 
  inversion H4; subst.
  exists t1.
  split.
  constructor.
  simpl.
  destruct (dEq k k).
  auto.
  intuition n.
  assumption.
  assert (findEP ls1 x v).
  constructor.
  auto.
  eapply IHMatchEnvs in H3.
  destruct H3.
  destruct H3.
  exists x0.
  split.
  constructor.  
  simpl.
  destruct (dEq x k).
  rewrite e in n.
  intuition n.
  inversion H3; subst.
  assumption.
  assumption.
Defined.


Lemma ExRelValNone {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2): 
    MatchEnvs R venv tenv ->
    findE tenv x = None ->
    findE venv x = None.
Proof.
  intros.
  induction H; subst.
  simpl.
  reflexivity.
  inversion H0; subst.
  simpl.
  destruct (dEq x k).
  inversion H3.
  apply IHMatchEnvs.
  assumption.
Defined.  


Lemma ExRelValProj1 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2): 
    MatchEnvs R venv tenv ->
    findEP tenv x t ->
    exists v: V1, findEP venv x v.
Proof.
  intros.
  eapply ExRelVal in H. 
  destruct H.
  destruct H.
  eexists.
  eauto.
  eauto.
Defined.
  
(*******************************************************************)

Inductive MatchEnvs2 {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop) : 
          Envr K V1 -> Envr K V2 -> Prop :=
| MatchEnvs2_Nil : MatchEnvs2 rel nil nil
| MatchEnvs2_Cons : forall ls5 ls6 ls1 ls2 ls3 ls4 k v1 v2,
                     rel v1 v2 ->
                     MatchEnvs rel ls1 ls2 ->
                     MatchEnvs rel ls3 ls4 ->
                     findE ls2 k = None ->
                     ls5 = ls1 ++ ((k,v1)::ls3) ->
                     ls6 = ls2 ++ ((k,v2)::ls4) ->
            MatchEnvs2 rel ls5 ls6.                         

(********************************************************************)

(** lemmas on MatchEnvs2 *)

Lemma MatchEnvs1to2 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)  
          (env1: Envr K V1) (env2: Envr K V2) :
  MatchEnvs R env1 env2 -> MatchEnvs2 R env1 env2. 
intros.
inversion H; subst.  
constructor.
eapply MatchEnvs2_Cons.
eassumption.
eapply MatchEnvs_Nil.
eapply H1.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
Defined.


Lemma MatchEnvs2to1 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)  
          (env1: Envr K V1) (env2: Envr K V2) :
  MatchEnvs2 R env1 env2 -> MatchEnvs R env1 env2.
  intros.
  inversion H; subst.
  constructor.
  destruct ls1.
  destruct ls2.
  simpl.
  constructor.
  assumption.
  assumption.
  inversion H1.
  destruct ls2.
  inversion H1.
  rewrite <- app_comm_cons.
  rewrite <- app_comm_cons.
  destruct p.  
  destruct p0.
  inversion H1; subst.
  eapply MatchEnvs_Cons.
  assumption.

  eapply appEnvLemma.   
  assumption.
  eapply consEnvLemma.
  assumption.
  assumption.
Defined.

(***********************************************************************)

Inductive MatchEnvs2B {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop)  
          (k: K) (v1: V1) (v2: V2) : Envr K V1 -> Envr K V2 -> Prop :=
| MatchEnvs2B_split : forall ls5 ls6 ls1 ls2 ls3 ls4,
                     rel v1 v2 ->
                     MatchEnvs rel ls1 ls2 ->
                     MatchEnvs rel ls3 ls4 ->
                     findE ls2 k = None -> 
                     ls5 = ls1 ++ ((k,v1)::ls3) ->
                     ls6 = ls2 ++ ((k,v2)::ls4) ->
            MatchEnvs2B rel k v1 v2 ls5 ls6.                         


(**********************************************************************)

(** lemmas on MatchEnvs2B *)

Lemma MatchEnvsB2A {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)  
      (env1: Envr K V1) (env2: Envr K V2)
      (k: K) (v1: V1) (v2: V2):
  MatchEnvs2B R k v1 v2 env1 env2 -> MatchEnvs2 R env1 env2.
intros.
inversion H; subst.
econstructor.
eassumption.
exact H1.
exact H2.
eassumption.
reflexivity.
reflexivity.
Defined.

(*********************************************************************)

Inductive EnvPos {K V: Type} {h: DEq K} :
             Envr K V -> K -> option nat -> Prop :=
| EnvPos_Nil : forall k: K, EnvPos emptyE k None
| EnvPos_Same : forall (env: Envr K V) (k: K) (v: V),
                    EnvPos ((k,v)::env) k (Some 0)
| EnvPos_Diff : forall (env: Envr K V) (k1 k2: K)
                         (n: nat) (v: V),
                    k1 <> k2 ->
                    EnvPos env k1 (Some n) -> 
                    EnvPos ((k2,v)::env) k1 (Some (n+1)).            


Inductive EnvPrefix {K V: Type} {h: DEq K} :
             Envr K V -> K -> Envr K V -> Prop :=
| EnvPrefix_Nil : forall k: K, EnvPrefix emptyE k emptyE
| EnvPrefix_Same : forall (env: Envr K V) (k: K) (v: V),
                    EnvPrefix ((k,v)::env) k emptyE
| EnvPrefix_Diff : forall (env1 env2: Envr K V) (k1 k2: K)
                          (v: V),
                    k1 <> k2 ->
                    EnvPrefix env1 k1 env2 -> 
                    EnvPrefix ((k2,v)::env1) k1 ((k2,v)::env2).            


Inductive EnvSuffix {K V: Type} {h: DEq K} :
             Envr K V -> K -> Envr K V -> Prop :=
| EnvSuffix_Nil : forall k: K, EnvSuffix emptyE k emptyE
| EnvSuffix_Same : forall (env: Envr K V) (k: K) (v: V),
                    EnvSuffix ((k,v)::env) k env
| EnvSuffix_Diff : forall (env1 env2: Envr K V) (k1 k2: K)
                         (v: V),
                    k1 <> k2 ->
                    EnvSuffix env1 k1 env2 -> 
                    EnvSuffix ((k2,v)::env1) k1 env2.            


(********************************************************************)

(** lemmas for EnvPos, EnvPrefix and EnvSuffix *)

Lemma MatchEnvsPos {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
                    (env1: Envr K V1) (env2: Envr K V2) :
  MatchEnvs R env1 env2 ->
  forall (k: K) (n1 n2: option nat),
    EnvPos env1 k n1 ->
    EnvPos env2 k n2 ->
    n1 = n2.
Proof.
  intros.
  dependent induction H.
  inversion H0; subst.
  inversion H1; subst.
  reflexivity.
  inversion H1; subst.
  inversion H2; subst.
  reflexivity.
  intuition H8.
  inversion H2; subst.
  inversion H1; subst.
  omega.
  intuition H7.
  specialize (IHMatchEnvs k0 (Some n) (Some n0) H9 H11).
  inversion IHMatchEnvs; subst.
  reflexivity.
Defined.  


Lemma MatchEnvsPrefix {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
                    (env1: Envr K V1) (env2: Envr K V2) : 
  MatchEnvs R env1 env2 ->
  forall k env3 env4,
    EnvPrefix env1 k env3 ->
    EnvPrefix env2 k env4 ->
    MatchEnvs R env3 env4.
Proof.
  intros.
  dependent induction H.
  inversion H0; subst.
  inversion H1; subst.
  constructor.
  inversion H1; subst.
  inversion H2; subst.
  constructor.
  intuition H8.
  inversion H2; subst.
  intuition H8.
  constructor.
  assumption.
  apply (IHMatchEnvs k0).
  assumption.
  assumption.
Defined. 
  
  
Lemma MatchEnvsSuffix {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
                    (env1: Envr K V1) (env2: Envr K V2) : 
  MatchEnvs R env1 env2 ->
  forall k env3 env4,
    EnvSuffix env1 k env3 ->
    EnvSuffix env2 k env4 ->
    MatchEnvs R env3 env4.
Proof.
  intros.
  dependent induction H.
  inversion H0; subst.
  inversion H1; subst.
  constructor.
  inversion H1; subst.
  inversion H2; subst.
  assumption.
  intuition H8.
  inversion H2; subst.
  intuition H8.
  apply (IHMatchEnvs k0).
  assumption.  
  assumption.
Defined.


Lemma IsEnvPrefix {K V: Type} {h: DEq K} 
                   (env: Envr K V) (k: K) : 
  forall ls1 ls2 v,
    env = ls1 ++ ((k,v)::ls2) ->
    findE ls1 k = None ->
    EnvPrefix env k ls1.
Proof.
  intros.
  revert H H0.
  revert k v ls2 env.
  induction ls1.
  intros.
  simpl in H.
  rewrite H.
  constructor.
  intros.
  rewrite <- app_comm_cons in H.
  induction env.
  inversion H.
  inversion H; subst.
  destruct a. 
  constructor.
  inversion H0; subst.
  destruct (dEq k k0).
  inversion H2.
  assumption.
  eapply find_simpl2 in H0.
  eapply IHls1 in H0.
  eassumption.
  reflexivity.
Defined.  
  

Lemma IsEnvSuffix {K V: Type} {h: DEq K} 
                   (env: Envr K V) (k: K) : 
  forall ls1 ls2 v,
    env = ls1 ++ ((k,v)::ls2) ->
    findE ls1 k = None ->
    EnvSuffix env k ls2.
Proof.
  intros.
  revert H H0.
  revert k v ls2 env.
  induction ls1.
  intros.
  simpl in H.
  rewrite H.
  constructor.
  intros.
  rewrite <- app_comm_cons in H.
  induction env.
  inversion H.
  inversion H; subst.
  destruct a. 
  constructor.
  inversion H0; subst.
  destruct (dEq k k0).
  inversion H2.
  assumption.
  eapply find_simpl2 in H0.
  eapply IHls1 in H0.
  eassumption.
  reflexivity.
Defined.

(***************************************************************)

(** more lemmas on MatchEnvs *)

Lemma MatchEnvsApp {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
                    (env1: Envr K V1) (env2: Envr K V2) : 
  MatchEnvs R env1 env2 ->
  forall ls1 ls2 ls3 ls4 k v1 v2,
    env1 = ls1 ++ ((k,v1)::ls3) ->
    env2 = ls2 ++ ((k,v2)::ls4) ->
    findE ls1 k = None -> 
    findE ls2 k = None -> 
    R v1 v2 /\ MatchEnvs R ls1 ls2 /\ MatchEnvs R ls3 ls4.
Proof.
  intros.
  assert (env1 = ls1 ++ (k, v1) :: ls3) as E1.
  auto.
  assert (env2 = ls2 ++ (k, v2) :: ls4) as E2.
  auto.
  eapply IsEnvPrefix in E1.
  eapply IsEnvPrefix in E2.
  intros.
  assert (env1 = ls1 ++ (k, v1) :: ls3) as F1.
  auto.
  assert (env2 = ls2 ++ (k, v2) :: ls4) as F2.
  auto.
  eapply IsEnvSuffix in F1.
  eapply IsEnvSuffix in F2.
  intros.
  assert (env1 = ls1 ++ (k, v1) :: ls3) as G1.
  auto.
  assert (env2 = ls2 ++ (k, v2) :: ls4) as G2.
  auto.
  eapply IsEnvEl in G1.
  eapply IsEnvEl in G2.
  split.
  eapply RelatedByEnvEP.
  eapply H.
  eapply G1.
  apply G2.
  split.
  eapply MatchEnvsPrefix.
  eapply H.
  eapply E1.
  apply E2.
  eapply MatchEnvsSuffix.
  eapply H.
  eapply F1.
  apply F2.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
Defined.  


Lemma MatchEnvsApp1 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
                    (env1: Envr K V1) (env2: Envr K V2) : 
  MatchEnvs R env1 env2 ->
  forall ls1 ls2 ls3 ls4 k v1 v2,
    env1 = ls1 ++ ((k,v1)::ls3) ->
    env2 = ls2 ++ ((k,v2)::ls4) ->
    findE ls1 k = None -> 
    findE ls2 k = None -> 
    R v1 v2.
Proof.
eapply MatchEnvsApp.
Defined.

Lemma MatchEnvsApp2 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
                    (env1: Envr K V1) (env2: Envr K V2) : 
  MatchEnvs R env1 env2 ->
  forall ls1 ls2 ls3 ls4 k v1 v2,
    env1 = ls1 ++ ((k,v1)::ls3) ->
    env2 = ls2 ++ ((k,v2)::ls4) ->
    findE ls1 k = None -> 
    findE ls2 k = None -> 
    MatchEnvs R ls1 ls2.
Proof.
eapply MatchEnvsApp.
Defined.

Lemma MatchEnvsApp3 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
                    (env1: Envr K V1) (env2: Envr K V2) : 
  MatchEnvs R env1 env2 ->
  forall ls1 ls2 ls3 ls4 k v1 v2,
    env1 = ls1 ++ ((k,v1)::ls3) ->
    env2 = ls2 ++ ((k,v2)::ls4) ->
    findE ls1 k = None -> 
    findE ls2 k = None -> 
    MatchEnvs R ls3 ls4.
Proof.
eapply MatchEnvsApp.
Defined.


  
Lemma MatchEnvsA2B {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)  
          (env1: Envr K V1) (env2: Envr K V2) :
  MatchEnvs2 R env1 env2 ->
  forall (k: K) (v1: V1) (v2: V2), findEP env1 k v1 ->
                                   findEP env2 k v2 -> 
                              MatchEnvs2B R k v1 v2 env1 env2.
Proof.
intros.
assert (findEP env1 k v1) as K1.
auto.
assert (findEP env2 k v2) as K2.
auto.
apply findEPtoEP2 in K1.
apply findEPtoEP2 in K2.
inversion K1.
rename H3 into K3.
inversion K2.
rename H3 into K4.
dependent induction H.
eapply (MatchEnvs2B_split R k v1 v2 nil nil nil nil nil nil).
inversion H0; subst.
inversion H.
inversion H0; subst.
inversion H.
inversion H0; subst.
inversion H.
inversion H0; subst.
inversion H.
inversion H0; subst.
inversion H.
inversion H0; subst.
inversion H.
assert (MatchEnvs R (ls1 ++ (k, v1) :: ls3) (ls2 ++ (k, v2) :: ls4)).
eapply appEnvLemma.   
assumption.
eapply consEnvLemma.
assumption.
assumption.
rewrite H3 in H7.
rewrite H4 in K4.
econstructor.
(*
inversion H5; subst.
inversion H6; subst.
*)
eapply RelatedByEnvEP.
exact H11.
rewrite <- H3.
exact H5.
rewrite <- H4.
exact H6.
(***)
instantiate (1:=m2).
instantiate (1:=m0).
(*rewrite H3 in H7.
rewrite H4 in K4.*)
eapply MatchEnvsApp2.
eapply H11.
eapply H7.
eapply K4.
assumption.
assumption.
instantiate (1:=m3).
instantiate (1:=m1).
eapply MatchEnvsApp3.
eapply H11.
eapply H7.
eapply K4.
assumption.
assumption.
assumption.
rewrite H3.
assumption.
rewrite H4.
assumption.
Defined.


(*********************************************************************)

Inductive LiftRel {A B: Type} (R: A -> B -> Prop) :
                       option A -> option B -> Prop :=
| SLift : forall (v: A) (t: B), R v t ->
                          LiftRel R (Some v) (Some t)                 
| NLift : LiftRel R None None. 


(**********************************************************************)

(** lemmas on LiftRel *)

Lemma nthErrorAux3 {A B: Type} (R : A -> B -> Prop)
        (ls1: list A) (ls2: list B) (a: A) (b: B): (forall n : nat,
    LiftRel R (nth_error (a :: ls1) n) (nth_error (b :: ls2) n)) ->
  (forall n : nat, LiftRel R (nth_error ls1 n) (nth_error ls2 n)).
Proof.
intros.
specialize (H (S n)).
simpl in H.
assumption.
Defined.


Lemma sameBehSameLengthB {A B: Type} (R : A -> B -> Prop)
        (ls1: list A) (ls2: list B) : (forall n : nat,
          LiftRel R (nth_error ls1 n) (nth_error ls2 n)) ->
            length ls1 = length ls2.                            
Proof.
  intros.
  dependent induction ls1.
  dependent induction ls2.
  reflexivity.
  specialize (H 0).
  simpl in H.
  inversion H; subst.
  dependent induction ls2.
  specialize (H 0).
  simpl in H.
  inversion H.  
  specialize (IHls1 ls2).
  assert ((forall n : nat,
    LiftRel R (nth_error (a :: ls1) n) (nth_error (a0 :: ls2) n)) ->
  (forall n : nat, LiftRel R (nth_error ls1 n) (nth_error ls2 n))). 
  apply (nthErrorAux3 R ls1 ls2 a a0).
  assert (forall n : nat, LiftRel R (nth_error ls1 n) (nth_error ls2 n)).
  auto.
  apply IHls1 in H1.
  simpl.
  auto.
Defined.


(************************************************************************)

Inductive Forall3A {A B :Type} (R: A -> B -> Prop)
          (P: forall (a:A) (b:B), R a b -> Type) :
           list A -> list B -> Prop :=
| Forall3A_nil : Forall3A R P nil nil
| Forall3A_cons : forall (aas: list A) (bbs: list B) 
                        (a:A) (b:B) (p: R a b),
                   P a b p ->
                   Forall3A R P aas bbs ->                          
                   Forall3A R P (a::aas) (b::bbs).              


Inductive Forall3 {K A B :Type} (R: A -> B -> Prop)
          (P: forall (a:A) (b:B), R a b -> Prop) :
           Envr K A -> Envr K B -> Prop :=
| Forall3_nil : Forall3 R P nil nil
| Forall3_cons : forall (aas: Envr K A) (bbs: Envr K B) 
                        (x:K) (a:A) (b:B) (p: R a b),
                   P a b p ->
                   Forall3 R P aas bbs ->                          
                   Forall3 R P ((x,a)::aas) ((x,b)::bbs).              



Inductive Forall2B {K A B :Type} {h: DEq K} (R: A -> B -> Prop)
          (P: forall (a:A) (b:B), R a b -> Prop)
          (Q: forall (ls1: Envr K A) (ls2: Envr K B),
                     MatchEnvs R ls1 ls2 -> Prop) :
          K -> A -> B -> Envr K A -> Envr K B -> Prop :=
 Forall2B_split : forall (aas as1 as2: Envr K A)
                         (bbs bs1 bs2: Envr K B) 
                         (k:K) (a:A) (b:B)
                         (p1: MatchEnvs R as1 bs1)
                         (p2: MatchEnvs R as2 bs2)
                         (p0: R a b),
                 aas = as1 ++ ((k,a)::as2) ->
                 bbs = bs1 ++ ((k,b)::bs2) ->
                 Q as1 bs1 p1 ->
                 Q as2 bs2 p2 ->
                 P a b p0 -> 
                 Forall2B R P Q k a b aas bbs. 


Inductive Forall2BC {K A B :Type} {h: DEq K} (R: A -> B -> Prop)
          (P: forall (ls1: Envr K A) (ls2: Envr K B),
                     MatchEnvs R ls1 ls2 -> Prop) :
          K -> A -> B -> Envr K A -> Envr K B -> Prop :=
 Forall2BC_split : forall (aas as1 as2: Envr K A)
                         (bbs bs1 bs2: Envr K B) 
                         (k:K) (a:A) (b:B)
                         (p1: MatchEnvs R as1 bs1)
                         (p2: MatchEnvs R as2 bs2)
                         (p0: MatchEnvs R (singleE k a) (singleE k b)),
                 aas = as1 ++ ((k,a)::as2) ->
                 bbs = bs1 ++ ((k,b)::bs2) ->
                 P as1 bs1 p1 ->
                 P as2 bs2 p2 ->
                 P (singleE k a) (singleE k b) p0 -> 
                 Forall2BC R P k a b aas bbs. 

Inductive Forall2BB {K A B :Type} {h: DEq K} (R: A -> B -> Prop)
          (P: forall (a0:A) (b0:B), R a0 b0 -> Prop) :
          K -> A -> B -> Envr K A -> Envr K B -> Prop :=
| Forall2BB_one : forall (k:K) (a:A) (b:B) (p: R a b),
                 P a b p ->
                 Forall2BB R P k a b (singleE k a) (singleE k b)
| Forall2BB_cons : forall (aas as1 as2: Envr K A)
                         (bbs bs1 bs2: Envr K B) 
                         (k:K) (a:A) (b:B) (p: R a b),
                    aas = as1 ++ ((k,a)::as2) ->
                    bbs = bs1 ++ ((k,b)::bs2) ->
                    findE as1 k = None ->
                    findE bs1 k = None ->                
                    P a b p ->
                    Forall3 R P as1 bs1 ->                          
                    Forall3 R P as2 bs2 ->
                    Forall2BB R P k a b aas bbs. 

(***********************************************************************)

(** lemmas for Forall *)

Lemma matchForallAux1 {K A B} {h: DEq K} (R: A -> B -> Prop)
      (P: forall (a:A) (b:B), R a b -> Prop)
      (env1: Envr K A) (env2: Envr K B) (x:K) (a:A) (b:B):
  Forall3 R P env1 env2 -> 
  findEP env1 x a -> findEP env2 x b ->
  (forall p: R a b, P a b p). 
Proof.
  intros.
  generalize dependent p.
  dependent induction H.
  inversion H0.
  inversion H.
  intros.
  inversion H1; subst.
  inversion H3; subst.
  destruct (dEq x x0) in H5.
  inversion H5; subst.
  inversion H2; subst.
  inversion H4; subst.
  destruct (dEq x0 x0) in H7.
  inversion H7; subst.
  assert (p = p0).
  apply proof_irrelevance.
  rewrite <- H6.
  assumption.
  intuition n.
  inversion H2; subst.
  inversion H4; subst.
  destruct (dEq x x0) in H7.
  inversion H7; subst.
  intuition n.
  eapply IHForall3.
  constructor.
  assumption.
  constructor.
  assumption.
Defined.

Lemma forall3ConsExt {K A B :Type} {h: DEq K} (R: A -> B -> Prop)
      (P: forall (a:A) (b:B), R a b -> Prop) 
      (env1: Envr K A) (env2: Envr K B) (x:K) (a:A) (b:B) (p: R a b):
  Forall3 R P env1 env2 ->
  P a b p ->
  Forall3 R P ((x,a)::env1) ((x,b)::env2).
Proof.
  intros.
  econstructor.
  eassumption.
  assumption.  
Defined.

Lemma forall3AppExt {K A B :Type} {h: DEq K} (R: A -> B -> Prop)
      (P: forall (a:A) (b:B), R a b -> Prop) 
      (env1 env3: Envr K A) (env2 env4: Envr K B) (x:K):
  Forall3 R P env1 env2 ->
  Forall3 R P env3 env4 ->
  Forall3 R P (env1 ++ env3) (env2 ++ env4).
Proof.
  intros.
  dependent induction H.
  simpl.
  assumption.
  rewrite <- app_comm_cons.
  rewrite <- app_comm_cons. 
  econstructor.
  eassumption.
  auto.
Defined.

Lemma forall2Bto3 {K A B :Type} {h: DEq K} (R: A -> B -> Prop)
      (P: forall (a:A) (b:B), R a b -> Prop) 
      (env1: Envr K A) (env2: Envr K B) (x:K) (a:A) (b:B):
  @Forall2B K A B h R P (fun x y z => Forall3 R P x y) x a b env1 env2 ->
    Forall3 R P env1 env2.
Proof.
  intros.
  inversion H; subst.
  eapply (forall3ConsExt R P) in H3.
  instantiate (1:=b) in H3.
  instantiate (1:=x) in H3.
  instantiate (1:=a) in H3.
  eapply (forall3AppExt R P).
  auto.
  auto.
  auto.
  eauto.
Defined.

(* see OPEN PROBLEMS in EnvListAux8.v *)

(************************************************************************)

Inductive MatchLists {V1 V2: Type} (rel: V1 -> V2 -> Prop) : 
          list V1 -> list V2 -> Prop :=
| MatchLists_Nil : MatchLists rel nil nil
| MatchLists_Cons : forall ls1 ls2 v1 v2,
                     rel v1 v2 ->
                     MatchLists rel ls1 ls2 ->
            MatchLists rel (v1::ls1) (v2::ls2).                          

(************************************************************************)

(** lemmas on MatchLists *)

Lemma prmsTypingAux1 {A T V: Type} (R: V -> T -> Prop)
        (fps : list (A * T)) (vls : list V)
        (h2: length fps = length vls):
  MatchLists R vls (map snd fps) ->
  MatchLists R (map snd (zip (map fst fps) vls (map_fst_length fps vls h2)))
               (map snd fps).
Proof.
  generalize h2; clear.
  dependent induction fps.
  dependent induction vls.
  intros.
  simpl.
  constructor.
  intros.  
  inversion h2.
  dependent induction vls.
  intros.
  inversion h2.  
  intros.
  simpl in h2.
  simpl in H.
  simpl.
  inversion H; subst.
  constructor.
  assumption.  
  specialize (IHfps vls (cons_length fps vls a a0 h2) H5).
  assert (cons_length (map fst fps) vls (fst a) a0
                      (map_fst_length (a :: fps) (a0 :: vls) h2) = (map_fst_length fps vls (cons_length fps vls a a0 h2))).
  apply proof_irrelevance.
  rewrite H0.
  assumption.
Defined.
 


Lemma prmsTypingAux2 {A T V: Type} {h: DEq A} (R: V -> T -> Prop)
      (fps : list (A * T)) (vls : list V) 
      (h2: length fps = length vls):

  (MatchLists R (map snd (zip (map fst fps) vls (map_fst_length fps vls h2)))
                (map snd fps)) ->
  (MatchEnvs R (zip (map fst fps) vls (map_fst_length fps vls h2)) fps).        
Proof.
  generalize h2; clear.
  generalize dependent fps.
  induction vls.
  induction fps.
  intros.
  simpl.
  constructor.
  intro.
  inversion h2.
  generalize dependent vls. 
  induction fps.
  intros.
  inversion h2.
  intros.
  specialize (IHvls fps (cons_length fps vls a0 a h2)).
  assert (MatchLists R (map snd (zip (map fst fps) vls
                      (map_fst_length fps vls (cons_length fps vls a0 a h2)))) (map snd fps)).
  simpl in H.
  inversion H; subst. 
  assert (cons_length (map fst fps) vls (fst a0) a
                      (map_fst_length (a0 :: fps) (a :: vls) h2) = (map_fst_length fps vls (cons_length fps vls a0 a h2))).
  apply proof_irrelevance.
  rewrite <- H0.
  assumption.  
  simpl.
  clear IHfps.
  destruct a0.
  simpl.
  inversion H; subst.
  constructor.
  assumption.
  specialize (IHvls H0).
  assert (cons_length (map fst fps) vls a0 a
                      (map_fst_length ((a0,t) :: fps) (a :: vls) h2) = (map_fst_length fps vls (cons_length fps vls (a0,t) a h2))).
  apply proof_irrelevance.
  rewrite H1.
  assumption.  
Defined.  

