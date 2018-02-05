(* coq_makefile *.v -o Makefile -Q . "" *)

Require Import Coq.Lists.List.

Require Export EnvLibA.

Import ListNotations.

(** lemmas on projections *)

Definition snd_sigT_of_sigT2 {A : Type} {P Q : A -> Type} (X : sigT2 P Q) :
   sigT Q
  := existT Q
            (let (a, _, _) := X in a)
            (let (x, _, q) as s return (Q (let (a, _, _) := s in a)) := X in q).

Definition proj1_of_sigT2 {A : Type} {P Q : A -> Type} (X : sigT2 P Q) : A :=
           (projT1 (sigT_of_sigT2 X)).


(*************************************************************************)

Inductive findET {K V: Type} {h: DEq K} (m: Envr K V) (k: K) : V -> Type :=
  FindET : forall x: V, findE m k = Some x -> findET m k x.

Inductive findET2 {K V: Type} {h: DEq K} (m: Envr K V) (k: K) : V -> Type :=
  FindET2 : forall (v: V) (m0 m1: Envr K V),
            m = m0 ++ ((k, v) :: m1) ->  
            findE m0 k = None ->  
            findET2 m k v.

(*************************************************************************)

(** lemmas on findET *)

Lemma findEP2extCons2 {K V: Type} {h: DEq K} (env: Envr K V) (x y: K)
      (u v: V):
    x <> y -> findET2 ((y, v) :: env) x u -> findET2 env x u. 
  intros.
  rename X into H0.
  inversion H0; subst.
  destruct m0.
  simpl in H1.
  inversion H1; subst.
  intuition H.
  inversion H1; subst.
  simpl in H1.

  econstructor.
  instantiate (1:= m1).
  reflexivity.

  eapply update_simpl1 in H.
  rewrite H.
  eassumption.
Defined.


Lemma findEP2toEP_T {K V: Type} {h: DEq K} (env: Envr K V) (x: K) (v: V):
  findET2 env x v -> findET env x v.
Proof.
intros.
rename X into H.
inversion H; subst.  
constructor.
revert H.
revert H1.
revert m1.
induction m0.
intros.
simpl.
destruct (dEq x x).
reflexivity.
intuition n.
simpl.
destruct a.
destruct (dEq x k).
intros.
inversion H1.
intros.
specialize (IHm0 m1 H1).
eapply findEP2extCons2 with (env := (m0 ++ ((x, v) :: m1))) in n.
eapply IHm0 in n.

assumption.
eassumption.
Defined.


(*************************************************************************)

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


Inductive MatchEnvs2BT1 {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type)  
          (k: K) (v1: V1) (v2: V2) : Envr K V1 -> Envr K V2 -> Type :=
| MatchEnvs2B1_splitT : forall ls1 ls2 ls3 ls4,
                     rel v1 v2 ->
                     MatchEnvsT rel ls1 ls2 ->
                     MatchEnvsT rel ls3 ls4 ->
                     findE ls2 k = None -> 
                     let ls5 := ls1 ++ ((k,v1)::ls3) in
                     let ls6 := ls2 ++ ((k,v2)::ls4) in 
            MatchEnvs2BT1 rel k v1 v2 ls5 ls6.                         

Inductive MatchEnvs2BT0 {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type)  
          (k: K) (v1: V1) (v2: V2) : Envr K V1 -> Envr K V2 -> Type :=
| MatchEnvs2B0_splitT : forall ls1 ls2 ls3 ls4,
                     rel v1 v2 ->
                     MatchEnvsT rel ls1 ls2 ->
                     MatchEnvsT rel ls3 ls4 ->
                     findE ls2 k = None -> 
                     MatchEnvs2BT0 rel k v1 v2
                              (ls1 ++ ((k,v1)::ls3)) (ls2 ++ ((k,v2)::ls4)).                         

(*********************************************************************)

(** lemmas on MatchEnvsT *)

Lemma MatchEnvs2BT_C {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type)  
          (k: K) (v1: V1) (v2: V2) (P: rel v1 v2) :  
  MatchEnvs2BT rel k v1 v2 [(k,v1)] [(k,v2)].
  econstructor.
  auto.
  instantiate (1:=nil).
  instantiate (1:=nil).
  constructor.
  instantiate (1:=nil).
  instantiate (1:=nil).
  constructor.
  simpl.
  auto.
  simpl.
  auto.
  simpl.
  auto.
Defined.  


Lemma consEnvLemmaT {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type)
              (env1: Envr K V1) (env2: Envr K V2) (x: K)
              (v1: V1) (v2: V2) :
    MatchEnvsT rel env1 env2 ->
    rel v1 v2 -> 
    MatchEnvsT rel ((x, v1)::env1) ((x, v2)::env2).  
Proof.
  intros.
  constructor.
  assumption.
  assumption.
Defined.


Lemma updateEnvLemmaT {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type)
              (env1: Envr K V1) (env2: Envr K V2) (x: K)
                      (v1: V1) (v2: V2):
    MatchEnvsT rel env1 env2 ->
    rel v1 v2 -> 
    MatchEnvsT rel ((x, v1) :: env1) ((x, v2) :: env2).  
Proof.
  eapply consEnvLemmaT. 
Defined.
  

Lemma appEnvLemmaT {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type): 
     forall (env1A env1B: Envr K V1) (env2A env2B: Envr K V2), 
  MatchEnvsT rel env1A env2A ->
  MatchEnvsT rel env1B env2B -> 
  MatchEnvsT rel (env1A ++ env1B) (env2A ++ env2B).  
Proof.
  induction env1A.
  intros. 
  induction env2A.
  simpl.
  assumption.
  inversion X.  
  induction env2A.
  intros.
  inversion X.  
  intros.
  simpl.
  destruct a.
  destruct a0.
  destruct (dEq k k0).
  Focus 2.
  inversion X; subst.  
  intuition n.
  destruct e.
  inversion X; subst.
  constructor.
  assumption.
  apply IHenv1A. 
  assumption.
  assumption.
Defined.  


Lemma overrideEnvLemmaT {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type): 
     forall (env1A env1B: Envr K V1) (env2A env2B: Envr K V2), 
  MatchEnvsT rel env1A env2A ->
  MatchEnvsT rel env1B env2B -> 
  MatchEnvsT rel (env1A ++ env1B) (env2A ++ env2B).  
Proof.
  eapply appEnvLemmaT.
Defined.


Lemma RelatedByEnvEP_T {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type) 
                     (env1: Envr K V1) (env2: Envr K V2) (x: K)
                     (v1: V1) (v2: V2)
         : MatchEnvsT rel env1 env2 -> findET env1 x v1 ->
           findET env2 x v2 -> rel v1 v2.
Proof.
  intros.
  rename X0 into H0.
  rename X1 into H1.
  rename X into H.
  inversion H0; subst.
  inversion H1; subst.
  induction H. 
  inversion H2.
  inversion H3; subst.
  inversion H2; subst.
  destruct (dEq x k).
  inversion H6; subst.
  inversion H5; subst.
  assumption.
  apply IHMatchEnvsT.
  constructor.
  assumption.
  constructor.  
  assumption.
  assumption.
  assumption.
Defined.


Lemma ExRelValT {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Type)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2): 
    MatchEnvsT R venv tenv ->
    findET tenv x t ->
    sigT2 (findET venv x) (fun v: V1 => R v t). 
Proof.
  intros.
  induction X; subst.
  inversion X0.
  inversion H.
  inversion X0; subst.
  inversion H; subst.
  rename v2 into t2.
  destruct (dEq x k). 
  inversion H1; subst.
  econstructor.
  instantiate (1:= v1).
  constructor.
  simpl.
  destruct (dEq k k).
  auto.
  intuition n.
  assumption.
  assert (findET ls2 x t).
  constructor.
  auto.
  eapply IHX in X1.
  destruct X1.
  econstructor.
  instantiate (1:= x0).
  constructor.  
  simpl.
  destruct (dEq x k).
  rewrite e in n.
  intuition n.
  inversion f; subst.
  assumption.
  assumption.
Defined.


Lemma ExRelValT1 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Type)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (v: V1): 
    MatchEnvsT R venv tenv ->
    findET venv x v ->
    sigT2 (findET tenv x) (fun t: V2 => R v t). 
Proof.
  intros.
  induction X; subst.
  inversion X0.
  inversion H.
  inversion X0; subst.
  inversion H; subst.
  rename v2 into t2.
  destruct (dEq x k). 
  inversion H1; subst.
  econstructor.
  instantiate (1:= t2).
  constructor.
  simpl.
  destruct (dEq k k).
  auto.
  intuition n.
  assumption.
  assert (findET ls1 x v).
  constructor.
  auto.
  eapply IHX in X1.
  destruct X1.
  econstructor.
  instantiate (1:= x0).
  constructor.  
  simpl.
  destruct (dEq x k).
  rewrite e in n.
  intuition n.
  inversion f; subst.
  assumption.
  assumption.
Defined.


Lemma ExRelValTNone {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Type)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K): (*t: V2:*) 
    MatchEnvsT R venv tenv ->
    findE tenv x = None ->
    findE venv x = None.
Proof.
  intros.
  induction X; subst.
  simpl.
  reflexivity.
  inversion H; subst.
  simpl.
  destruct (dEq x k).
  inversion H1.
  apply IHX.
  assumption.
Defined.  

Lemma RelatedByEnvEP2_T {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type) 
                     (env1: Envr K V1) (env2: Envr K V2) (x: K)
                     (v1: V1) (v2: V2)
         : MatchEnvsT rel env1 env2 -> findET2 env1 x v1 ->
           findET2 env2 x v2 -> rel v1 v2.
intros.
apply findEP2toEP_T in X0.
apply findEP2toEP_T in X1.
eapply RelatedByEnvEP_T.
eassumption.
eassumption.
assumption.
Defined.


Lemma MatchEnvs2BT_find1 {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type)  
      (k: K) (v1: V1) (v2: V2) (env1: Envr K V1) (env2: Envr K V2)
  : MatchEnvs2BT rel k v1 v2 env1 env2 -> findET env1 k v1 * findET env2 k v2. 
  intros.
  inversion X; subst.
  assert (findE ls1 k = None).
  eapply (ExRelValTNone rel ls2 ls1 k).
  auto.
  auto.
  split.
  eapply findEP2toEP_T.
  econstructor.
  reflexivity.
  auto.
  eapply findEP2toEP_T.
  econstructor.
  reflexivity.
  assumption.
Defined.  
   

Lemma envAppendCompare {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Type)
          (env1 env2 env3 env4: Envr K V1)
          (tenv1 tenv3: Envr K V2) 
          (x: K) (f1 f2: V1) :
  MatchEnvsT R env1 tenv1 ->
  MatchEnvsT R env3 tenv3 ->
  findE tenv1 x = None ->
  findE tenv3 x = None ->
  env1 ++ (x,f1) :: env2 = env3 ++ (x,f2) :: env4 ->
  f1 = f2.
Proof.
    intros.
    assert (findE env1 x = None).
    eapply (ExRelValTNone R tenv1 env1).
    assumption.
    assumption.
    assert (findE env3 x = None).
    eapply (ExRelValTNone R).
    eassumption.
    assumption.
    assert (findE (env1 ++ (x, f1) :: env2) x =
            Some f1).
    erewrite override_simpl2.
    simpl.
    destruct (dEq x x).
    auto.
    intuition.
    auto.
    assert (findE (env3 ++ (x, f2) :: env4) x =
            Some f2).
    erewrite override_simpl2.
    simpl.
    destruct (dEq x x).
    auto.
    intuition.
    auto.
    rewrite <- H1 in H5.
    rewrite H4 in H5.
    injection H5.
    auto.
Defined.    
 

(***********************************************************************)

Definition ExRelValTProj1 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Type)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2) 
       (h1: MatchEnvsT R venv tenv)
       (h2: findET tenv x t) :
  sigT (fun v: V1 => findET venv x v) :=
        sigT_of_sigT2 (ExRelValT R tenv venv x t h1 h2).

Definition ExRelValTProj2 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Type)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2) 
       (h1: MatchEnvsT R venv tenv)
       (h2: findET tenv x t) := 
        snd_sigT_of_sigT2 (ExRelValT R tenv venv x t h1 h2).


(*********************************************************************)

Inductive Forall2T {A B : Type} (R: A -> B -> Type): 
    list A -> list B -> Type := 
  | Forall2_nilT : Forall2T R nil nil
  | Forall2_consT : forall x y l l',
      R x y -> Forall2T R l l' -> Forall2T R (x::l) (y::l').

Inductive ForallT {A: Type} (P: A -> Type): list A -> Type :=
      | Forall_nilT : ForallT P nil
      | Forall_consT : forall x l, P x -> ForallT P l -> ForallT P (x::l).


(*************************************************************************)

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
  eapply map_length.
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
  eapply map_length.
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


(**********************************************************************)

Inductive Forall3AT {A B :Type} (R: A -> B -> Type)
          (P: forall (a:A) (b:B), R a b -> Type) :
           list A -> list B -> Type :=
| Forall3AT_nil : Forall3AT R P nil nil
| Forall3AT_cons : forall (aas: list A) (bbs: list B) 
                        (a:A) (b:B) (p: R a b),
                   P a b p ->
                   Forall3AT R P aas bbs ->                          
                   Forall3AT R P (a::aas) (b::bbs).              


Inductive Forall3T {K A B :Type} (R: A -> B -> Type)
                    (P: forall (a:A) (b:B), R a b -> Type) :
           Envr K A -> Envr K B -> Type :=
| Forall3T_nil : Forall3T R P nil nil
| Forall3T_cons : forall (aas: Envr K A) (bbs: Envr K B) 
                        (x:K) (a:A) (b:B) (p: R a b),
                   P a b p ->
                   Forall3T R P aas bbs ->                          
                   Forall3T R P ((x,a)::aas) ((x,b)::bbs).              


Inductive Forall2BT {K A B :Type} {h: DEq K} (R: A -> B -> Type)
          (P: forall (a:A) (b:B), R a b -> Type)
          (Q: forall (ls1: Envr K A) (ls2: Envr K B),
                     MatchEnvsT R ls1 ls2 -> Type) :
          K -> A -> B -> Envr K A -> Envr K B -> Type :=
 Forall2BT_split : forall (aas as1 as2: Envr K A)
                         (bbs bs1 bs2: Envr K B) 
                         (k:K) (a:A) (b:B)
                         (p1: MatchEnvsT R as1 bs1)
                         (p2: MatchEnvsT R as2 bs2)
                         (p0: R a b),
                 aas = as1 ++ ((k,a)::as2) ->
                 bbs = bs1 ++ ((k,b)::bs2) ->
                 Q as1 bs1 p1 ->
                 Q as2 bs2 p2 ->
                 P a b p0 -> 
                 Forall2BT R P Q k a b aas bbs. 



Inductive Forall2BT0 {K A B :Type} {h: DEq K} (R: A -> B -> Type)
          (P: forall (a:A) (b:B), R a b -> Type)
          (Q: forall (ls1: Envr K A) (ls2: Envr K B),
                     MatchEnvsT R ls1 ls2 -> Type) :
          K -> A -> B -> Envr K A -> Envr K B -> Type :=
 Forall2BT0_split : forall (as1 as2: Envr K A)
                         (bs1 bs2: Envr K B) 
                         (k:K) (a:A) (b:B)
                         (p1: MatchEnvsT R as1 bs1)
                         (p2: MatchEnvsT R as2 bs2)
                         (p0: R a b),
                 let aas := as1 ++ ((k,a)::as2) in
                 let bbs := bs1 ++ ((k,b)::bs2) in
                 Q as1 bs1 p1 ->
                 Q as2 bs2 p2 ->
                 P a b p0 -> 
                 Forall2BT0 R P Q k a b aas bbs. 


