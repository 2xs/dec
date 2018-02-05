(* coq_makefile *.v -o Makefile -Q . "" *)

Require Import Coq.Lists.List.
Require Import Omega.
Require Export Coq.Program.Equality.

Import ListNotations.


(* lemmas on lists *)

Lemma app_cons_assoc {A: Type} (x: A) (ls1 ls2: list A):
       (x :: ls1) ++ ls2 = x :: (ls1 ++ ls2).
Proof.
simpl.
reflexivity.
Defined.

Lemma derive_absurd1 {V: Type} (ls: list V) (p: length ls > 0) :
  ls = nil -> False.
  intros.
  rewrite H in p.
  compute in p.
  inversion p.
Defined.  
  
Definition hd_total {V: Type} (ls: list V) : (length ls > 0) -> V :=
  match ls with
      | nil => (fun p => match (derive_absurd1 nil p eq_refl) with end)
      | cons x ts => fun _ => x
  end.                 

Lemma tl_length {V1 V2: Type} (ls1: list V1) (ls2: list V2)
      (p: length ls1 = length ls2) :
  length (tl ls1) = length (tl ls2).
  induction ls2.
  induction ls1.
  compute.
  reflexivity.
  simpl in p.
  inversion p.
  simpl in p.
  simpl.
  assert (length ls1 > 0 -> length ls1 = S (length (tl ls1))).
  intros.
  induction ls1.
  inversion H.
  simpl.
  reflexivity.
  assert (length ls1 > 0).
  rewrite p at 1.
  omega.
  apply H in H0.
  rewrite p in H0.
  inversion H0; subst.
  reflexivity.
Defined.  

Lemma cons_length {V1 V2: Type} (ls1: list V1) (ls2: list V2)
      (x: V1) (y: V2)  
      (p: length (cons x ls1) = length (cons y ls2)) :
  length ls1 = length ls2.
  simpl in p.
  inversion p.
  reflexivity.
Defined.  


Lemma derive_absurd2r {V1 V2: Type} (ls: list V2) (x: V2) :
  (length (@nil V1) = length (cons x ls)) -> False.
  intros.
  inversion H.
Defined.

Lemma derive_absurd2l {V1 V2: Type} (ls: list V1) (x: V1) :
  (length (cons x ls) = length (@nil V2)) -> False.
  intros.
  inversion H.
Defined.

Lemma map_length {V1 V2: Type} (ls: list V1) (f: V1 -> V2) :
  length ls = length (map f ls).
  induction ls.
  simpl.
  reflexivity.
  simpl.
  rewrite IHls.
  reflexivity.
Defined.  
  
Lemma map_fst_length {V1 V2 V3: Type} (ls1: list (V1 * V2)) (ls2: list V3) :
  length ls1 = length ls2 -> length (map fst ls1) = length ls2.
  intros.
  erewrite <- map_length.
  assumption.
Defined.  

Lemma nthErrorAux1 {A: Type} : forall n:nat, @nth_error A nil n = None.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Defined.  

Lemma nthErrorAux2 {A: Type} (a: A) (ls: list A):
                @nth_error A (a::ls) 0 = Some a.
  compute.
  reflexivity.
Defined.  


Lemma nilSum {A: Type} (ls1 ls2: list A) : nil = ls1 ++ ls2 ->
                                           nil = ls1 /\ nil = ls2.
 Proof.
  revert ls2.
  destruct ls1.
  intros.
  auto.
  intros.
  inversion H.
Defined.  

  
(**************************************************************************)  

(** type classes *) 
 
(** decidable equality class *)

Class DEq (K: Type) : Type := {
   dEq : forall x y: K, {x = y} + {x <> y}
}.  


(** admissible Pip value type class *)

Class ValTyp (T: Type) : Prop. 

    
(** Pip state class *)  

  Class PState (W: Type) : Type := {

   loc_pi : forall (T: Type) (p1 p2: ValTyp T), p1 = p2;

   b_init : W ;
}.

(************************************************************************)


(** environment type - list of pairs *)

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

(************************************************************************)

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

(** lemmas on findEP and findEP2 *)

Lemma findEPAbs {K V: Type} {h: DEq K} (x: K) (v: V):
    findEP2 nil x v -> False.
  intros.
  inversion H; subst.
  destruct m0.
  simpl in H0.
  inversion H0.
  inversion H0.
Defined.

Lemma findEPbreak  {K V: Type} {h: DEq K} (env: Envr K V) (x: K) (v: V):
  findEP env x v -> exists (env0 env1: Envr K V),
       env = env0 ++ ((x, v) :: env1) /\ findE env0 x = None.  
intros.
inversion H; subst.
dependent induction env. 
inversion H0.

simpl in H0.
destruct a as [x0 v0].
destruct (dEq x x0).
inversion e; subst.
exists nil.
exists env.
split.
simpl.
unfold updateE.
inversion H0; subst.
reflexivity.
simpl.
reflexivity.

specialize (IHenv x v). 
assert (findEP env x v).
constructor.
assumption.
specialize (IHenv H1 H0).
destruct IHenv as [env0].
destruct H2 as [env1].
destruct H2.
eexists ((x0,v0)::env0).
eexists env1.
simpl.
split.
rewrite H2.
reflexivity.
destruct (dEq x x0).
rewrite e in n.
intuition n.
assumption.
Defined.

Lemma findEP2extCons1 {K V: Type} {h: DEq K} (env: Envr K V) (x y: K)
      (u v: V):
    x <> y -> findEP2 env x u -> findEP2 ((y, v) :: env) x u. 
  intros.
  inversion H0; subst.
  econstructor.
  eapply app_comm_cons.
  rewrite <- H2.
  symmetry.
  eapply update_simpl1.
  assumption.
Defined.

Lemma findEP2extCons2 {K V: Type} {h: DEq K} (env: Envr K V) (x y: K)
      (u v: V):
    x <> y -> findEP2 ((y, v) :: env) x u -> findEP2 env x u. 
  intros.
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

 
Lemma findEPtoEP2  {K V: Type} {h: DEq K} (env: Envr K V) (x: K) (v: V):
   findEP env x v -> findEP2 env x v.
intros.
inversion H; subst.
eapply (findEPbreak) in H.
destruct H.
destruct H.
destruct H.
econstructor.
eassumption.
assumption.
Defined.

Lemma findEP2toEP  {K V: Type} {h: DEq K} (env: Envr K V) (x: K) (v: V):
  findEP2 env x v -> findEP env x v.
intros.
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

Lemma IsEnvEl {K V: Type} {h: DEq K} 
                   (env: Envr K V) (k: K) : 
  forall ls1 ls2 v,
    env = ls1 ++ ((k,v)::ls2) ->
    findE ls1 k = None ->
    findEP env k v.
Proof.
  intros.
  revert H H0.
  revert k v ls2 env.
  induction ls1.
  intros.
  simpl in H.
  rewrite H.
  constructor.
  simpl.
  destruct (dEq k k).
  reflexivity.
  intuition n.
  intros.
  rewrite <- app_comm_cons in H.
  induction env.
  inversion H.
  destruct a.
  inversion H; subst.
  inversion H0; subst.
  constructor.
  simpl.
  destruct (dEq k k0).
  inversion H2.
  specialize (IHls1 k v ls2 (ls1 ++ (k, v) :: ls2) eq_refl H2).
  inversion IHls1.
  assumption.
Defined.  
  

(*************************************************************************)


Fixpoint zip {V1 V2: Type} (ls1 : list V1) (ls2: list V2) :
           (length ls1 = length ls2) -> list (V1 * V2) :=
  match ls1 with
    | nil => match ls2 with
               | nil => fun _ => nil
               | cons _ _ => fun p => match (derive_absurd2r _ _ p) with end
               end
    | cons x ts1 => match ls2 with
               | nil => fun p => match (derive_absurd2l _ _ p) with end          
               | cons y ts2 => fun p => cons (x,y) 
                      (zip ts1 ts2 (cons_length ts1 ts2 x y p))
               end                                   
  end.

(* Extraction zip. *)

Fixpoint interleave {V1 V2: Type} (ls1 : list V1) (ls2: list V2) :
                                                    list (V1 * V2) :=
  match ls1 with
    | nil => nil 
    | cons x ts1 => match ls2 with
               | nil => nil          
               | cons y ts2 => cons (x,y) (interleave ts1 ts2)
               end                                   
  end.

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


