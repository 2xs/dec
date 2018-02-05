Require Export EnvLibA.
Require Export RelLibA.
Require Export PRelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Import StaticSemA.
Require Import DynamicSemA.
Require Import TRInductA.
Require Import WeakenA.
Require Import TSoundnessA.
Require Import IdModTypeA.
Require Import IdModPip.
Require Import DetermA.
Require Import AbbrevA.
Require Import HoareA.
Require Import THoareA.
Require Import Lib.
Require Import Pip_state.
Require Import Pip_stateLib.
Require Import Coq.Structures.Equalities.
Require Import Coq.Logic.Eqdep.
Import ListNotations.

Module Hoare_Test_FstShadow <: IdModType.

Module FstShadow := THoare IdModP.
Export FstShadow.

Definition Id := FstShadow.Id.
Definition IdEqDec := FstShadow.IdEqDec.
Definition IdEq := FstShadow.IdEq.
Definition W := FstShadow.W.
Definition Loc_PI := FstShadow.Loc_PI.
Definition BInit := FstShadow.BInit.
Definition WP := FstShadow.WP.

(**************************************************)

(****** Hoare logic *)

Notation "{{ P }} fenv >> env >> e {{ Q }}" := (THoareTriple_Eval P Q fenv env e ) 
(at level 90) : state_scope.

Open Scope state_scope.



Definition wp (P : Value -> W -> Prop) (fenv: funEnv) (env: valEnv) (e : Exp) :
  W -> Prop := fun s => forall (v:Value) (s': W),
EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v)) -> P v s'.

Lemma wpIsPrecondition (P : Value -> W -> Prop) (fenv: funEnv) (env: valEnv) (e : Exp) :
  {{ wp P fenv env e }} fenv >> env >> e {{ P }}.
Proof.
unfold THoareTriple_Eval.
intros ftenv tenv k1 k2 t k3 s s' v H1 H2.
unfold wp in H2.
eapply H2.
auto.
Qed.

Lemma weakenEval (P Q : W -> Prop) (R : Value -> W -> Prop) (fenv: funEnv) (env: valEnv) (e : Exp) :
  {{ Q }} fenv >> env >> e {{ R }} -> (forall s, P s -> Q s) -> {{ P }} fenv >> env >> e {{ R }}.
Proof.
intros.
unfold THoareTriple_Eval in *.
intros.
eapply H;
eauto.
Qed.

Definition wpPrms (P : list Value -> W -> Prop) (fenv: funEnv) (env: valEnv) (ps: Prms):
  W -> Prop := fun s => forall (vs: list Value) (s': W),
PrmsClosure fenv env (Conf Prms s ps) (Conf Prms s' (PS (map Val vs))) -> P vs s'.

Lemma wpIsPreconditionPrms (P : list Value -> W -> Prop) (fenv: funEnv) (env: valEnv) (ps: Prms):
  THoarePrmsTriple_Eval (wpPrms P fenv env ps) P fenv env ps.
Proof.
unfold THoarePrmsTriple_Eval.
intros ftenv tenv k1 k2 t k3 s s' v H1 H2.
unfold wpPrms in H2.
eapply H2.
auto.
Qed.

Lemma weakenPrms (P Q : W -> Prop) (R : list Value -> W -> Prop) (fenv: funEnv) (env: valEnv) (ps: Prms):
  THoarePrmsTriple_Eval Q R fenv env ps ->
 (forall s, P s -> Q s) -> THoarePrmsTriple_Eval P R fenv env ps .
Proof.
intros.
unfold THoarePrmsTriple_Eval in *.
intros.
eapply H;
eauto.
Qed.

(******* Program *)

(** getSh1idx : returns first shadow *)

Definition getSh1idx : Exp := Val (cst index sh1idx). (** Return in the original definition *)

(** ReadPhysical -page -index : reads physical address *)

Definition xf_read (p: page) : XFun (option index) (option page) := {|
   b_mod := fun s oi => (s,match oi with |None => None |Some i => readPhysicalInternal p i (memory s) end)
|}.

Instance VT_index : ValTyp index.
Instance VT_option_index : ValTyp (option index).
Instance VT_option_page : ValTyp (option page).

Definition ReadPhysical (p:page) (x:Id) : Exp :=
  Modify (option index) (option page) VT_option_index VT_option_page (xf_read p) (Var x).  

(** Succ -index : calculates the successor of an index *)                 

Definition xf_succ : XFun index (option index) := {|
   b_mod := fun s (idx:index) =>  (s, succIndexInternal idx)
|}.

Definition Succ (x:Id) : Exp :=
  Modify index (option index) VT_index VT_option_index xf_succ (Var x).

(** getFstShadow -page : returns the adress of the 1st shadow *)

(* Bind Approach *)

Definition getFstShadowBind (p:page) : Exp :=
 BindS "x" getSh1idx 
           (BindS "y" (Succ "x") 
                      (ReadPhysical p "y")
           ).

(* Apply Approch *)

Definition indexType := vtyp index. 
Definition optionIndexType := vtyp (option index). 

Definition ReadPhysicalQF (p:page) := QF 
(FC emptyE [("x",optionIndexType)] (ReadPhysical p "x") (Val (cst (option page) None)) "ReadPhysical" 0).

Definition SuccQF := QF 
(FC emptyE [("y",indexType)] (Succ "y") (Val (cst (option index) None)) "Succ" 0).

Definition getFstShadowApply (p:page) :Exp :=
Apply (ReadPhysicalQF p) (PS [
                         Apply SuccQF (PS [getSh1idx])
                      ]). 


(*Bind approach & Deep definition of Successor*) 

Instance VT_nat : ValTyp nat.
Instance VT_bool : ValTyp bool.

Definition xf_LtDec (n: nat) : XFun nat bool := {|
   b_mod := fun s i => (s,if lt_dec i n then true else false)
|}.

Definition LtDec (x:Id) (n:nat): Exp :=
  Modify nat bool VT_nat VT_bool (xf_LtDec n) (Var x). 

Definition xf_prj1 : XFun index nat := {|
   b_mod := fun s (idx:index) => (s,let (i,_) := idx in i)
|}.

Definition prj1 (x:Id) : Exp :=
  Modify index nat VT_index VT_nat xf_prj1 (Var x).  

Definition xf_SomeCindex : XFun nat (option index) := {|
   b_mod := fun s i => (s,Some (CIndex i))
|}.

Definition SomeCindex (x:Id) : Exp :=
  Modify nat (option index) VT_nat VT_option_index  xf_SomeCindex (Var x).

Definition SomeCindexQF := QF 
(FC emptyE [("i",Nat)] (SomeCindex "i") (Val (cst (option index) None)) "SomeCindex" 0).

Definition xf_SuccD : XFun nat nat := {|
   b_mod := fun s i => (s,S i)
|}.

Definition SuccR (x:Id) : Exp :=
  Modify nat nat VT_nat VT_nat xf_SuccD (Var x).


Definition SuccD (x:Id) :Exp :=
BindS "i" (prj1 x) 
          (IfThenElse (LtDec "i" tableSize) 
                      (Apply SomeCindexQF
                             (PS[SuccR "i"])
                      ) 
                      (Val(cst (option index) None))
          ).


Definition getFstShadowBindDeep (p:page) : Exp :=
 BindS "x" getSh1idx 
           (BindS "y" (SuccD "x") 
                      (ReadPhysical p "y")
           ).

(*Bind approach & Deep definition of Succ with recursive plus function*) 


Definition plusR' (f: Id) (x:Id) : Exp :=
      Apply (FVar f) (PS [VLift (Var x)]). 

Definition plusR (n:nat) := QF 
(FC emptyE [("i",Nat)] (VLift(Var "i")) (BindS "p" (plusR' "plusR" "i") (SuccR "p")) "plusR" n).

Definition SuccRec (x:Id) :Exp :=
BindS "i" (prj1 x) 
          (IfThenElse (LtDec "i" tableSize) 
                      (Apply SomeCindexQF 
                             (PS[Apply (plusR 1) 
                                       (PS[VLift(Var "i")])
                                ])
                      ) 
                      (Val(cst (option index) None))
          ).


Definition getFstShadowBindDeepRec (p:page) : Exp :=
 BindS "x" getSh1idx 
           (BindS "y" (SuccRec "x") 
                      (ReadPhysical p "y")
           ).


(******* State properties *)

Definition isVA (p:page) (i:index) (s:W): Prop := match (lookup p i (s.(memory)) beqPage beqIndex) with 
             |Some (VA _) => True
             |_ => False
             end.

Definition nextEntryIsPP (p:page) (idx:index) (p':Value) (s:W) : Prop:= 
match succIndexInternal idx with 
| Some i => match lookup p i (memory s) beqPage beqIndex with 
                  | Some (PP table) => p' = cst (option page) (Some table)
                  |_ => False 
                  end
| _ => False 
end.

Definition partitionDescriptorEntry (s:W) := 
forall (p : page),  
  In p (getPartitions multiplexer s) -> forall (idx : index), 
    (idx = PDidx \/ idx = sh1idx \/ idx = sh2idx \/ idx = sh3idx \/ idx = PPRidx  \/ idx = PRidx ) ->
    idx < tableSize - 1  /\ isVA p idx  s /\ exists (p1:page) , nextEntryIsPP p idx (cst (option page) (Some p1)) s  /\  
    (cst page p1) <> (cst page defaultPage).


(******* Useful Lemmas *)

(** about getSh1idx *)

Lemma getSh1idxW (P: Value -> W -> Prop) (fenv: funEnv) (env: valEnv) :
  {{wp P fenv env getSh1idx}} fenv >> env >> getSh1idx {{P}}.
Proof.
apply wpIsPrecondition.
Qed.

Lemma getSh1idxWp P fenv env :
{{P}} fenv >> env >> getSh1idx 
{{fun (idxSh1 : Value) (s : state) => P s  /\ idxSh1 = cst index sh1idx }}.
Proof.
eapply weakenEval.
eapply getSh1idxW.
intros. 
unfold wp.
intros.
unfold getSh1idx in X.
inversion X;subst.
auto.
inversion X0.
Qed.

Lemma getSh1idxWp' P fenv env :
HoarePrmsTriple_Eval P 
(fun (idxSh1 : list Value) (s : state) => P s  /\ idxSh1 = [cst index sh1idx]) fenv env [getSh1idx].
Proof.
unfold HoarePrmsTriple_Eval.
intros.
inversion X;subst.
intuition.
unfold map in H5.
induction vs.
inversion X;subst.
inversion X0;subst.
inversion X2.
inversion X2.
inversion H5;subst.
simpl in *.
destruct vs.
auto.
inversion H2.
inversion X0;subst.
inversion X2.
inversion X2.
Qed.

(** about Succ *)

Lemma succW  (x : Id) (P: Value -> W -> Prop) (v:Value) (fenv: funEnv) (env: valEnv) :
forall (idx:index), {{fun s => idx < (tableSize -1) /\ forall  l : idx + 1 < tableSize , 
    P (cst (option index) (succIndexInternal idx)) s /\ v = cst index idx }}  
fenv >> (x,v)::env >> Succ x {{ P }}.
Proof.
intros.
unfold THoareTriple_Eval.
intros.
intuition.
destruct H1 as [H1 H1'].
omega.
inversion X;subst.
inversion X0;subst.
repeat apply inj_pair2 in H7;subst.
inversion X2;subst.
inversion X3;subst.
inversion H;subst.
destruct IdModP.IdEqDec in H3.
inversion H3;subst.
clear H3 e X3 H XF1.
inversion X1;subst.
inversion X3;subst.
repeat apply inj_pair2 in H7.
repeat apply inj_pair2 in H9.
subst.
unfold b_exec,b_eval,xf_succ,b_mod in *.
simpl in *.
inversion X4;subst.
apply H1.
inversion X5.
inversion X5.
contradiction.
Qed.

Lemma succWp (x:Id) (v:Value) P (fenv: funEnv) (env: valEnv) :
forall (idx:index), {{fun s => P s  /\ idx < tableSize - 1 /\ v=cst index idx}} fenv >> (x,v)::env >> Succ x 
{{fun (idxsuc : Value) (s : state) => P s  /\ idxsuc = cst (option index) (succIndexInternal idx) /\ exists i, idxsuc = cst (option index) (Some i)}}.
Proof.
intros.
eapply weakenEval.
eapply succW.
intros.
simpl.
split.
instantiate (1:=idx).  
intuition.
intros.
intuition.
destruct idx.
exists (CIndex (i + 1)).
f_equal.
unfold succIndexInternal.
case_eq (lt_dec i tableSize).
intros.
auto.
intros.
contradiction.
Qed.

Lemma succDW  (x : Id) (P: Value -> W -> Prop) (v:Value) (fenv: funEnv) (env: valEnv) :
forall (idx:index), {{fun s => idx < (tableSize -1) /\ forall  l : idx + 1 < tableSize , 
    P (cst (option index) (succIndexInternal idx)) s /\ v = cst index idx }}  
fenv >> (x,v)::env >> SuccD x {{ P }}.
Proof.
intros.
unfold THoareTriple_Eval.
intros.
clear k3 t k2 k1 tenv ftenv.
intuition.
destruct H1 as [H1 H1'].
omega.
inversion X;subst.
inversion X0;subst.
inversion X2;subst.
repeat apply inj_pair2 in H7;subst.
inversion X3;subst.
inversion X4;subst.
inversion H;subst.
destruct IdModP.IdEqDec in H3.
inversion H3;subst.
clear H3 e X4 H XF1.
inversion X1;subst.
inversion X4;subst.
inversion X6;subst.
repeat apply inj_pair2 in H7.
repeat apply inj_pair2 in H9.
subst.
unfold xf_prj1 at 3 in X6.
unfold b_exec,b_eval,b_mod in *.
simpl in *.
destruct idx.
inversion X5;subst.
inversion X7;subst.
inversion X8;subst.
inversion X9;subst.
simpl in *.
inversion X11;subst.
inversion X12;subst.
repeat apply inj_pair2 in H7.
subst.
inversion X13;subst.
inversion X14;subst.
inversion H;subst.
clear H X14 XF2.
inversion X10;subst.
inversion X14;subst.
simpl in *.
inversion X16;subst.
inversion X17;subst.
repeat apply inj_pair2 in H7.
repeat apply inj_pair2 in H10.
subst.
unfold xf_LtDec at 3 in X17.
unfold b_exec,b_eval,b_mod in *.
simpl in *.
case_eq (lt_dec i tableSize).
intros.
rewrite H in X17, H1.
inversion X15;subst.
inversion X18;subst.
simpl in *.
inversion X20; subst.
inversion X19;subst.
inversion X21;subst.
simpl in *.
inversion X23;subst.
inversion H10;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X24;subst.
inversion X25;subst.
repeat apply inj_pair2 in H11.
subst.
inversion X26;subst.
inversion X27;subst.
inversion H2;subst.
clear X27 H2 XF3.
inversion X22;subst.
inversion X27;subst.
simpl in *.
inversion X29;subst.
inversion H10;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X30;subst.
inversion X31;subst.
repeat apply inj_pair2 in H11.
repeat apply inj_pair2 in H13.
subst.
unfold xf_SuccD at 3 in X31.
unfold b_exec,b_eval,xf_SuccD,b_mod in *.
simpl in *.
inversion X28;subst.
inversion X32;subst.
simpl in *.
inversion X34;subst.
inversion H10;subst.
destruct vs.
inversion H2.
inversion H2;subst.
destruct vs.
unfold mkVEnv in *.
simpl in *.
inversion X33;subst.
inversion X35;subst.
inversion X37;subst.
simpl in *.
inversion X38;subst.
repeat apply inj_pair2 in H15.
subst.
inversion X39;subst.
inversion X40;subst.
inversion H3;subst.
clear X40 H3 XF4 H5.
inversion X36;subst.
inversion X40;subst.
inversion X42;subst.
simpl in *.
inversion X43;subst.
repeat apply inj_pair2 in H14.
repeat apply inj_pair2 in H16.
subst.
unfold xf_SomeCindex at 3 in X43.
unfold b_exec,b_eval,b_mod in *.
simpl in *.
inversion X41;subst.
inversion X44;subst.
simpl in *.
inversion X46;subst.
inversion X45;subst.
inversion X47;subst.
inversion X48;subst.
assert (Z : S i = i+1). 
omega.
rewrite Z.
auto.
inversion X49.
inversion X49.
inversion X47.
inversion X44.
inversion H5.
inversion X35;subst.
inversion X36.
inversion X36.
inversion X35.
inversion X32.
inversion X30.
inversion X24.
repeat apply inj_pair2 in H6.
rewrite H in H6.
inversion H6.
rewrite H in X21.
inversion X21.
intros.
contradiction.
inversion X18.
inversion X9.
inversion X7.
contradiction.
Qed.

Lemma succDWp (x:Id) (v:Value) P (fenv: funEnv) (env: valEnv) :
forall (idx:index), {{fun s => P s  /\ idx < tableSize - 1 /\ v=cst index idx}} fenv >> (x,v)::env >> SuccD x 
{{fun (idxsuc : Value) (s : state) => P s  /\ idxsuc = cst (option index) (succIndexInternal idx) /\ exists i, idxsuc = cst (option index) (Some i)}}.
Proof.
intros.
eapply weakenEval.
eapply succDW.
intros.
simpl.
split.
instantiate (1:=idx).  
intuition.
intros.
intuition.
destruct idx.
exists (CIndex (i + 1)).
f_equal.
unfold succIndexInternal.
case_eq (lt_dec i tableSize).
intros.
auto.
intros.
contradiction.
Qed.


Lemma succRecW  (x : Id) (P: Value -> W -> Prop) (v:Value) (fenv: funEnv) (env: valEnv) :
forall (idx:index), {{fun s => idx < (tableSize -1) /\ forall  l : idx + 1 < tableSize , 
    P (cst (option index) (succIndexInternal idx)) s /\ v = cst index idx }}  
fenv >> (x,v)::env >> SuccRec x {{ P }}.
Proof.
intros.
destruct idx.
simpl.
unfold SuccRec.
eapply BindS_VHTT1.
(** prj1 *)
unfold THoareTriple_Eval.
intros.
instantiate (1:= fun v0 s => {| i := i; Hi := Hi |} < (tableSize -1) /\ forall  l : {| i := i; Hi := Hi |} + 1 < tableSize , 
    P (cst (option index) (succIndexInternal {| i := i; Hi := Hi |})) s /\ v = cst index {| i := i; Hi := Hi |}
            /\ v0 = cst nat i).
destruct H.
destruct H0.
omega.
subst.
inversion X;subst.
inversion X0;subst.
repeat apply inj_pair2 in H7.
inversion X2;subst.
inversion X3;subst.
inversion H1;subst.
case_eq (IdModP.IdEqDec x x);intros; try contradiction.
rewrite H2 in H3.
inversion H3;subst.
inversion X1;subst.
inversion X4;subst.
repeat apply inj_pair2 in H10.
repeat apply inj_pair2 in H12.
subst.
unfold b_eval, b_exec, xf_prj1, b_mod in *.
simpl in *.
inversion X5;subst.
intuition.
inversion X6.
inversion X6.
intros; simpl.
eapply IfTheElse_VHTT1.
(** LtDec *)
unfold THoareTriple_Eval.
intros.
instantiate (1:= fun v1 s => {| i := i; Hi := Hi |} < (tableSize -1) 
            /\ forall  l : {| i := i; Hi := Hi |} + 1 < tableSize , 
                 P (cst (option index) (succIndexInternal {| i := i; Hi := Hi |})) s 
            /\ v = cst index {| i := i; Hi := Hi |}
            /\ v0 = cst nat i 
            /\ v1 = cst bool (if lt_dec i tableSize then true else false)).
simpl.
split.
intuition.
intros.
destruct H.
destruct H0.
omega.
destruct H1.
subst.
inversion X;subst.
inversion X0;subst.
repeat apply inj_pair2 in H7.
subst.
inversion X2;subst.
inversion X3;subst.
inversion H1;subst.
clear X3 H1 XF1 k3 k2 k1 t ftenv tenv.
inversion X1;subst.
inversion X3;subst.
repeat apply inj_pair2 in H7.
repeat apply inj_pair2 in H9.
subst.
unfold b_eval, b_exec, xf_LtDec, b_mod in *.
simpl in *.
inversion X4;subst.
intuition.
inversion X5.
inversion X5.
simpl.
eapply Apply_VHTT1.
eapply Prms_VHTT1.
eapply Apply_VHTT1.
eapply Prms_VHTT1.
(* Var i *)
instantiate (1:= fun v1 s => {| i := i; Hi := Hi |} < (tableSize -1) 
            /\ forall  l : {| i := i; Hi := Hi |} + 1 < tableSize , 
                 P (cst (option index) (succIndexInternal {| i := i; Hi := Hi |})) s 
            /\ v = cst index {| i := i; Hi := Hi |}
            /\ v0 = cst nat i 
            /\ v1 = v0).
unfold THoareTriple_Eval.
intros.
destruct H.
split.
intuition.
intros.
destruct H0.
omega.
destruct H1.
destruct H2.
subst.
inversion X;subst.
inversion X0;subst.
inversion X2;subst.
inversion X3;subst.
inversion H1;subst.
inversion X1;subst.
inversion X4;subst.
inversion X5;subst.
intuition.
inversion X6.
inversion X6.
intros.
simpl.
(** PS *)
unfold THoarePrmsTriple_Eval.
intros.
destruct H.
destruct H0.
omega.
destruct H1.
destruct H2.
subst.
case_eq (lt_dec i tableSize); intros; try contradiction.
rewrite H1 in H0.
clear H1 l.
inversion X;subst.
destruct vs; inversion H6.
inversion X;subst.
instantiate (1:= fun vs s => {| i := i; Hi := Hi |} < (tableSize -1) 
            /\ forall  l : {| i := i; Hi := Hi |} + 1 < tableSize , 
                 P (cst (option index) (Some (CIndex (i + 1)))) s 
            /\ v = cst index {| i := i; Hi := Hi |}
            /\ v0 = cst nat i 
            /\ vs = [cst nat i]).
simpl; intuition.
inversion X0.
inversion X0.
intuition.
unfold mkVEnv;simpl.
destruct vs.
unfold THoareTriple_Eval.
intros.
intuition.
destruct H1.
omega.
intuition.
inversion H4.
eapply BindS_VHTT1.
(** plus R' *)
unfold THoareTriple_Eval.
intros.
intuition.
destruct H1.
omega.
intuition.
inversion H4;subst.
clear H4 k3 k2 k1 t tenv ftenv.
inversion X;subst.
inversion X0;subst.
inversion X2;subst.
inversion X3;subst.
inversion H1;subst.
inversion X1;subst.
inversion X4;subst.
inversion H12;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X6;subst.
inversion X7;subst.
inversion X8;subst.
inversion X9;subst.
inversion H2;subst.
clear H1 H2 X3 X9.
inversion X5;subst.
inversion X3;subst.
inversion H11;subst.
destruct vs.
inversion H1.
inversion H1.
inversion X10;subst.
inversion X11;subst.
inversion X9;subst.
inversion X12;subst.
inversion H11;subst.
destruct vs.
inversion H1.
inversion H1;subst.
destruct vs; inversion H4.
clear H4 H11 H12 H1.
inversion X13;subst.
inversion X14;subst.
unfold mkVEnv in *; simpl in *.
inversion X16;subst.
inversion X17;subst.
inversion X18;subst.
inversion H1;subst.
clear X18 H1.
inversion X5;subst.
inversion X18;subst.
inversion H11;subst.
destruct vs.
inversion H1.
inversion H1.
inversion X20;subst.
inversion X21;subst.
inversion X19;subst.
inversion X22;subst.
inversion H11;subst.
destruct vs.
inversion H1.
inversion H1;subst.
destruct vs; inversion H4.
clear H4 H11 H12 H1.
unfold mkVEnv in *; simpl in *.
inversion X23;subst.
inversion X24;subst.
inversion X26;subst.
inversion X27;subst.
inversion X28;subst.
simpl in *.
inversion H1;subst.
clear H1 X28.
inversion X27;subst.
inversion X25;subst.
inversion X29;subst.
inversion X31;subst.
inversion X30;subst.
inversion X32;subst.
inversion X33;subst.
clear X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 
      X11 X12 X13 X14 X15 X16 X17 X18 X19 X20 
      X21 X22 X23 X24 X25 X26 X27 X28 X29 X30 
      X31 X32 X33.
instantiate (1:= fun v2 s => {| i := i; Hi := Hi |} < (tableSize -1) 
            /\ forall  l : {| i := i; Hi := Hi |} + 1 < tableSize , 
                 P (cst (option index) (Some (CIndex (i + 1)))) s 
            /\ v = cst index {| i := i; Hi := Hi |}
            /\ v0 = cst nat i 
            /\ v1 = cst nat i
            /\ vs = []
            /\ v2 = cst nat i).
simpl;intuition.
inversion X34.
inversion X34.
inversion X32.
inversion X24;subst.
inversion X25.
inversion X25.
inversion X24.
inversion X22.
inversion X20.
inversion X14;subst.
inversion X15.
inversion X15.
inversion X14.
inversion X12.
inversion X10.
inversion X6.
(** SuccR *)
intros;simpl.
unfold THoareTriple_Eval.
intros.
clear k3 k2 k1 t tenv ftenv.
intuition.
destruct H1.
omega.
intuition.
subst.
inversion X;subst.
inversion X0;subst.
repeat apply inj_pair2 in H7.
subst.
inversion X2;subst.
inversion X3;subst.
inversion H1;subst.
clear X3 H1 XF1.
inversion X1;subst.
inversion X3;subst.
repeat apply inj_pair2 in H7.
repeat apply inj_pair2 in H9.
subst.
unfold b_eval, b_exec, xf_SuccD, b_mod in *.
simpl in *.
inversion X4;subst.
instantiate (1:= fun v3 s => {| i := i; Hi := Hi |} < (tableSize -1) 
            /\ forall  l : {| i := i; Hi := Hi |} + 1 < tableSize , 
                 P (cst (option index) (Some (CIndex (i + 1)))) s 
            /\ v = cst index {| i := i; Hi := Hi |}
            /\ v3 = cst nat (S i)).
intuition.
inversion X5.
inversion X5.
intros; simpl.
(** PS *)
unfold THoarePrmsTriple_Eval.
intros.
destruct H.
destruct H0.
omega.
destruct H1.
subst.
clear k3 k2 k1 pt tenv ftenv.
inversion X;subst.
destruct vs; inversion H6.
inversion X;subst.
instantiate (1:= fun vs s => {| i := i; Hi := Hi |} < (tableSize -1) 
            /\ forall  l : {| i := i; Hi := Hi |} + 1 < tableSize , 
                 P (cst (option index) (Some (CIndex (i + 1)))) s 
            /\ v = cst index {| i := i; Hi := Hi |}
            /\ vs = [cst nat (S i)]).
simpl; intuition.
inversion X0.
inversion X0.
intros; intuition.
unfold mkVEnv in *.
simpl in *.
destruct vs.
unfold THoareTriple_Eval.
intros.
intuition.
destruct H1.
omega.
intuition.
inversion H3.
(** SomeCindex *)
unfold THoareTriple_Eval.
intros.
destruct H.
destruct H0.
omega.
destruct H1.
inversion H2;subst.
clear H2 k3 k2 k1 t tenv ftenv.
inversion X;subst.
inversion X0;subst.
repeat apply inj_pair2 in H7.
subst.
inversion X2;subst.
inversion X3;subst.
inversion H1;subst.
clear X3 H1 XF1.
inversion X1;subst.
inversion X3;subst.
repeat apply inj_pair2 in H7.
repeat apply inj_pair2 in H9.
subst.
unfold b_eval,b_exec,xf_SomeCindex,b_mod in *.
simpl in *.
inversion X4;subst.
assert (Succ_trivial : S i = i + 1) by omega.
rewrite Succ_trivial.
auto.
inversion X5.
inversion X5.
(** impossible case *)
unfold THoareTriple_Eval.
intros.
intuition.
destruct H1.
omega.
intuition.
case_eq (lt_dec i tableSize); intros; try contradiction.
rewrite H3 in H4.
unfold cst in H4.
apply inj_pair2 in H4.
inversion H4.
Qed.

(*Proof without Hoare Lemmas

Lemma succRecWByInversion  (x : Id) (P: Value -> W -> Prop) (v:Value) (fenv: funEnv) (env: valEnv) :
forall (idx:index), {{fun s => idx < (tableSize -1) /\ forall  l : idx + 1 < tableSize , 
    P (cst (option index) (succIndexInternal idx)) s /\ v = cst index idx }}  
fenv >> (x,v)::env >> SuccRec x {{ P }}.
Proof.
intros.
unfold THoareTriple_Eval.
intros.
clear k3 t k2 k1 tenv ftenv.
intuition.
destruct H1 as [H1 H1'].
omega.
inversion X;subst.
inversion X0;subst.
inversion X2;subst.
repeat apply inj_pair2 in H7;subst.
inversion X3;subst.
inversion X4;subst.
inversion H;subst.
destruct IdModP.IdEqDec in H3;try contradiction.
inversion H3;subst.
clear H3 e X4 H XF1.
inversion X1;subst.
inversion X4;subst.
inversion X6;subst.
repeat apply inj_pair2 in H7.
repeat apply inj_pair2 in H9.
subst.
unfold b_exec,b_eval,xf_prj1, b_mod in *.
simpl in *.
destruct idx.
inversion X5;subst.
inversion X7;subst.
inversion X8;subst.
inversion X9;subst.
simpl in *.
inversion X11;subst.
inversion X12;subst.
repeat apply inj_pair2 in H7.
subst.
inversion X13;subst.
inversion X14;subst.
inversion H;subst.
clear H X14 XF2.
inversion X10;subst.
inversion X14;subst.
simpl in *.
inversion X16;subst.
inversion X17;subst.
repeat apply inj_pair2 in H7.
repeat apply inj_pair2 in H10.
subst.
unfold b_exec,b_eval,xf_LtDec,b_mod in *.
simpl in *.
case_eq (lt_dec i tableSize);intros; try contradiction.
rewrite H in X17,H1.
inversion X15;subst.
inversion X18;subst.
simpl in *.
inversion X20; subst.
clear H6.
inversion X19;subst.
inversion X21;subst.
simpl in *.
inversion X23;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X24;subst.
inversion X25;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X26;subst.
inversion X27;subst.
inversion X28;subst.
inversion X29;subst.
inversion H2;subst.
clear X29 H2.
inversion X22;subst.
inversion X29;subst.
inversion X31;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
simpl in *.
inversion X32;subst.
inversion X33;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
unfold mkVEnv in *.
simpl in *.
inversion X34;subst.
inversion X35;subst.
inversion X30;subst.
inversion X36;subst.
simpl in *.
inversion X38;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X39;subst.
inversion X40;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2;subst.
destruct vs; inversion H5.
unfold mkVEnv in *.
simpl in *.
clear H5 H7 H17 H2.
inversion X37;subst.
inversion X41;subst.
inversion X43;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X44;subst.
inversion X45;subst.
inversion X46;subst.
simpl in *.
inversion X47;subst.
inversion X48;subst.
inversion X49;subst.
inversion H2;subst.
clear X49 H2.
inversion X42;subst.
inversion X49;subst.
inversion X51;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X52;subst.
inversion X53;subst.
inversion X54;subst.
inversion X55;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
simpl in *.
inversion X56;subst.
inversion X57;subst.
inversion X58;subst.
inversion X59;subst.
inversion H2;subst.
clear X59 H2.
inversion X50;subst.
inversion X59;subst.
inversion X61;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
simpl in *.
inversion X62;subst.
inversion X63;subst.
simpl in *.
inversion X64;subst.
inversion X65;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
simpl in *.
inversion X66;subst.
inversion X67;subst.
inversion X60;subst.
inversion X68;subst.
inversion X70;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
simpl in *.
inversion X71;subst.
inversion X72;subst.
inversion X73;subst.
inversion X74;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2;subst.
destruct vs; inversion H5.
unfold mkVEnv in *.
simpl in *.
clear H5 H7 H16 H2.
inversion X69;subst.
inversion X75;subst.
inversion X77;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X78;subst.
inversion X79;subst.
inversion X80;subst.
inversion X81;subst.
simpl in *.
inversion X60;subst.
inversion X82;subst.
inversion X84;subst.
inversion X85;subst.
simpl in *.
inversion X86;subst.
inversion H2;subst.
clear X86 H2.
inversion X83;subst.
inversion X85;subst.
inversion X88;subst.
inversion H2;subst.
clear X88 H2.
inversion X83;subst.
inversion X88;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X89;subst.
inversion X90;subst.
simpl in *.
inversion X91;subst.
inversion X92;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2;subst.
destruct vs; inversion H5.
unfold mkVEnv in *.
simpl in *.
clear H5 H7 H16 H2.
inversion X86;subst.
inversion X93;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X94;subst.
inversion X95;subst.
simpl in *.
inversion X96;subst.
inversion X97;subst.
simpl in *.
inversion X98;subst.
inversion X99;subst.
inversion X100;subst.
inversion H2;subst.
clear X100 H2.
inversion X87;subst.
inversion X100;subst.
inversion X102;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X103;subst.
inversion X104;subst.
inversion X105;subst.
simpl in *.
clear X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 
      X11 X12 X13 X14 X15 X16 X17 X18 X19 X20 
      X21 X22 X23 X24 X25 X26 X27 X28 X29 X30 
      X31 X32 X33 X34 X35 X36 X36 X38 X39 X40
      X41 X42 X43 X44 X45 X46 X47 X48 X49 X50.
inversion X106;subst.
simpl in *.
inversion X1;subst.
inversion X101;subst.
inversion X2;subst.
inversion X4;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X5;subst.
inversion X6;subst.
inversion X7;subst.
simpl in *.
inversion X8;subst.
inversion X3;subst.
inversion X9;subst.
inversion X11;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X12;subst.
inversion X13;subst.
inversion X14;subst.
simpl in *.
inversion X10;subst.
inversion X15;subst.
inversion X17;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X18;subst.
inversion X19;subst.
simpl in *.
inversion X20;subst.
inversion X21;subst.
repeat apply inj_pair2 in H10.
subst.
inversion X22;subst.
simpl in *.
inversion X23;subst.
inversion H2;subst.
clear X23 H2 XF3.
inversion X16;subst.
inversion X23;subst.
inversion X25;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X26;subst.
inversion X27;subst.
inversion X28;subst.
simpl in *.
inversion X29;subst.
repeat apply inj_pair2 in H10.
repeat apply inj_pair2 in H12.
subst.
unfold b_exec,b_eval,xf_SuccD,b_mod in *.
simpl in *.
inversion X16;subst.
inversion X30;subst.
clear X51 X52 X53 X54 X55 X56 X57 X58 X59 X60
      X61 X62 X63 X64 X65 X66 X67 X68 X69 X70
      X71 X72 X73 X74 X75 X76 X77 X78 X79 X80
      X81 X82 X83 X84 X85 X86 X87 X88 X89 X90
      X91 X92 X93 X94 X95 X96 X97 X98 X99 X100
      X101 X102 X103 X104 X105 X106.
inversion X32;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X33;subst.
inversion X34;subst.
simpl in *.
inversion X35;subst.
inversion X36;subst.
repeat apply inj_pair2 in H10.
repeat apply inj_pair2 in H13.
subst.
unfold b_exec,b_eval,b_mod in *.
simpl in *.
inversion X24;subst.
inversion X38;subst.
inversion X40;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X41;subst.
inversion X42;subst.
inversion X43;subst.
inversion X39;subst.
inversion X44;subst.
inversion X46;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X47;subst.
inversion X48;subst.
inversion X39;subst.
inversion X49;subst.
inversion X51;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2.
inversion X52;subst.
inversion X53;subst.
simpl in *.
clear X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 
      X11 X12 X13 X14 X15 X16 X17 X18 X19 X20 
      X21 X22 X23 X24 X25 X26 X27 X28 X29 X30. 
inversion X50;subst.
inversion X1;subst.
inversion X3;subst.
inversion H7;subst.
destruct vs.
inversion H2.
inversion H2;subst.
destruct vs; inversion H5.
unfold mkVEnv in *.
simpl in *.
clear H5 H7 H18 H2.
inversion X2;subst.
inversion X4;subst.
simpl in *.
inversion X5;subst.
inversion X6;subst.
inversion X9;subst.
repeat apply inj_pair2 in H10.
subst.
inversion X10;subst.
inversion X11;subst.
inversion H2;subst.
clear X11 H2 XF5.
inversion X7;subst.
inversion X11;subst.
inversion X12;subst.
repeat apply inj_pair2 in H10.
repeat apply inj_pair2 in H14.
subst.
unfold b_exec,b_eval,xf_SomeCindex,b_mod in *.
simpl in *.
inversion X8;subst.
inversion X13;subst.
inversion X15;subst.
simpl in *.
inversion X14;subst.
inversion X16;subst.
inversion X17;subst.
assert (Z : S i = i+1). 
omega.
rewrite Z.
auto.
inversion X18.
inversion X18.
inversion X16.
inversion X13.
inversion X4;subst.
inversion X5.
inversion X5.
inversion X4.
inversion X54.
inversion X52.
inversion X49.
inversion X47.
inversion X44.
inversion X41.
inversion X38.
inversion X33.
inversion X30.
inversion X26.
inversion X18.
inversion X15.
inversion X12.
inversion X9.
inversion X5.
inversion X2.
inversion X103.
inversion X94.
inversion X93;subst.
inversion X94.
inversion X94.
inversion X93.
inversion X89.
inversion X78.
inversion X75;subst.
inversion X76.
inversion X76.
inversion X75.
inversion X71.
inversion X68.
inversion X66.
inversion X62.
inversion X56.
inversion X52.
inversion X44.
inversion X41;subst.
inversion X42.
inversion X42.
inversion X41.
inversion X39.
inversion X36.
inversion X34.
inversion X32.
inversion X26.
inversion X24.
repeat apply inj_pair2 in H6.
rewrite H in H6; inversion H6.
rewrite H in X21; inversion X21.
inversion X18.
inversion X9.
inversion X7.
Qed.
*)

Lemma succRecWp (x:Id) (v:Value) P (fenv: funEnv) (env: valEnv) :
forall (idx:index), {{fun s => P s  /\ idx < tableSize - 1 /\ v=cst index idx}} fenv >> (x,v)::env >> SuccRec x 
{{fun (idxsuc : Value) (s : state) => P s  /\ idxsuc = cst (option index) (succIndexInternal idx) /\ exists i, idxsuc = cst (option index) (Some i)}}.
Proof.
intros.
eapply weakenEval.
eapply succRecW.
intros.
simpl.
split.
instantiate (1:=idx).  
intuition.
intros.
intuition.
destruct idx.
exists (CIndex (i + 1)).
f_equal.
unfold succIndexInternal.
case_eq (lt_dec i tableSize).
intros.
auto.
intros.
contradiction.
Qed.

Lemma succW' (P: list Value -> W -> Prop)(fenv: funEnv) (env: valEnv) :
forall (idx:index), 
THoarePrmsTriple_Eval (fun s => idx < tableSize -1 /\ forall  l : idx + 1 < tableSize , 
    P ([cst (option index) (succIndexInternal idx)]) s ) P
fenv env (PS [Apply SuccQF (PS [Val (cst index idx)])]).
Proof.
intros.
unfold THoarePrmsTriple_Eval.
intros.
clear k3 pt k2 k1 ftenv tenv.
intuition.
inversion X;subst.
destruct vs.
inversion H6.
inversion H6.
inversion X0;subst.
inversion X2;subst.
simpl in *.
inversion H6;subst.
destruct vs0.
inversion H.
inversion H.
induction vs0.
simpl in *.
subst.
clear H13 H H4 H6.
unfold mkVEnv in *.
simpl in *.
inversion X1; subst.
destruct vs.
inversion H6.
inversion H6.
inversion X3; subst.
inversion X5; subst.
simpl in *.
inversion X6; subst.
repeat apply inj_pair2 in H7.
subst.
inversion X7; subst.
inversion X8; subst.
inversion H; subst.
clear X8 H XF1.
inversion X6; subst.
repeat apply inj_pair2 in H7.
repeat apply inj_pair2 in H11.
subst.
inversion X4; subst.
induction vs.
inversion H6.
inversion H6.
inversion X9; subst.
inversion X11; subst.
simpl in *.
inversion X12; subst.
repeat apply inj_pair2 in H7.
repeat apply inj_pair2 in H9.
subst.
unfold xf_succ at 2 3 in X12.
unfold b_exec, b_eval, b_mod in X12.
simpl in *.
inversion X10; subst.
destruct vs.
inversion H6.
inversion H6.
inversion X13; subst.
unfold xf_succ, b_exec, b_eval, b_mod in X15.
simpl in *.
inversion X15; subst.
inversion X14; subst.
destruct vs.
inversion H6.
inversion H6;subst.
destruct vs.
apply H1.
omega.
inversion H3.
inversion X16; subst.
inversion X18.
inversion X18.
inversion X16.
inversion X13.
inversion H4.
inversion X3;subst.
inversion X4.
inversion X4.
inversion X3.
Qed.


Lemma succWp' partition P fenv env :
forall vs (idx:index), THoarePrmsTriple_Eval 
  (fun (s:W) => P s  /\ partitionDescriptorEntry s /\ 
                          In partition (getPartitions multiplexer s) /\  
      idx < tableSize - 1 /\ vs=[cst index idx])
  (fun vs s =>  P s /\ partitionDescriptorEntry s /\ 
                          In partition (getPartitions multiplexer s) /\ 
   (exists i : index, succIndexInternal idx = Some i /\ vs = [cst (option index) (Some i)]))
  fenv env (PS [Apply SuccQF (PS [Val (cst index idx)])]).
Proof.
intros.
eapply weakenPrms.
eapply succW'.
intros.
simpl.
intuition.
exists (CIndex (idx + 1)).
intuition.
unfold succIndexInternal.
destruct idx.
case_eq (lt_dec i tableSize).
intros.
auto.
intros.
contradiction.
f_equal.
f_equal.
unfold succIndexInternal.
destruct idx.
case_eq (lt_dec i tableSize).
intros.
auto.
intros.
contradiction.
Qed.


(******* about readPhysical *)

Lemma readPhysicalW (y:Id) table (v:Value) (P' : Value -> W -> Prop) (fenv: funEnv) (env: valEnv) :
 {{fun s =>  exists idxsucc p1, v = cst (option index) (Some idxsucc)
              /\ readPhysicalInternal table idxsucc (memory s) = Some p1 
              /\ P' (cst (option page) (Some p1)) s}} 
fenv >> (y,v)::env >> ReadPhysical table y {{P'}}.
Proof.
intros.
unfold THoareTriple_Eval.
intros.
intuition.
destruct H.
destruct H.
intuition.
inversion H0;subst.
clear k3 t k2 k1 ftenv tenv H1.
inversion X;subst.
inversion X0;subst.
repeat apply inj_pair2 in H7.
subst.
inversion X2;subst.
inversion X3;subst.
inversion H0;subst.
destruct IdEqDec in H3.
inversion H3;subst.
clear H3 e X3 H0 XF1. 
inversion X0;subst.
repeat apply inj_pair2 in H7.
repeat apply inj_pair2 in H11.
subst.
inversion X1;subst.
inversion X4;subst.
repeat apply inj_pair2 in H7.
apply inj_pair2 in H9.
subst.
unfold xf_read at 2 in X4.
unfold b_eval,b_exec,b_mod in X4.
simpl in *.
rewrite H in X4.
unfold xf_read,b_eval,b_exec,b_mod in X5.
simpl in *.
rewrite H in X5.
inversion X5;subst.
auto.
inversion X6.
inversion X6.
contradiction.
Qed.


Lemma readPhysicalW' (y:Id) table (vs: list Value) (P' : Value -> W -> Prop) (fenv: funEnv) :
 {{fun s =>  exists idxsucc p1, vs = [cst (option index) (Some idxsucc)]
              /\ readPhysicalInternal table idxsucc (memory s) = Some p1 
              /\ P' (cst (option page) (Some p1)) s}} 
fenv >> (mkVEnv [(y, optionIndexType)] vs) >> ReadPhysical table y {{P'}}.
Proof.
intros.
unfold THoareTriple_Eval.
intros.
intuition.
destruct H.
destruct H.
intuition.
inversion H0;subst.
unfold mkVEnv in *.
simpl in *.
clear k3 t k2 k1 ftenv tenv H1.
inversion X;subst.
inversion X0;subst.
repeat apply inj_pair2 in H7.
subst.
inversion X2;subst.
inversion X3;subst.
inversion H0;subst.
destruct IdEqDec in H3.
inversion H3;subst.
clear H3 e X3 H0 XF1. 
inversion X0;subst.
repeat apply inj_pair2 in H7.
repeat apply inj_pair2 in H11.
subst.
inversion X1;subst.
inversion X4;subst.
repeat apply inj_pair2 in H7.
apply inj_pair2 in H9.
subst.
unfold xf_read at 2 in X4.
unfold b_eval,b_exec,b_mod in X4.
simpl in *.
rewrite H in X4.
unfold xf_read,b_eval,b_exec,b_mod in X5.
simpl in *.
rewrite H in X5.
inversion X5;subst.
auto.
inversion X6.
inversion X6.
contradiction.
Qed.


(******* Hoare Triple *)

(* For Bind Approach *)

Lemma getFstShadowBindH (partition : page) (P : W -> Prop) (fenv: funEnv) (env: valEnv) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ In partition (getPartitions multiplexer s)}}
fenv >> env >> (getFstShadowBind partition) 
{{fun sh1 s => P s /\ nextEntryIsPP partition sh1idx sh1 s}}.
Proof.
unfold getFstShadowBind.
eapply BindS_VHTT1.
eapply getSh1idxWp.
simpl; intros.
eapply BindS_VHTT1.
eapply weakenEval.
eapply succWp. simpl.
simpl; intros; intuition.
instantiate (1:=(fun s => P s /\ partitionDescriptorEntry s /\ 
                          In partition (getPartitions multiplexer s))).
simpl. intuition.
instantiate (1:=sh1idx).
eapply H0 in H3.
specialize H3 with sh1idx.
eapply H3.
auto. auto.
simpl; intros.
eapply weakenEval.
eapply readPhysicalW.
simpl;intros.
intuition.
destruct H3.
exists x.
unfold partitionDescriptorEntry in H1.
apply H1 with partition sh1idx in H4.
clear H1.
intuition.
destruct H5.
exists x0.
intuition.
unfold nextEntryIsPP in H4.
unfold readPhysicalInternal.
subst.
inversion H2.
repeat apply inj_pair2 in H3.
unfold nextEntryIsPP in H5.
rewrite H3 in H5.
destruct (lookup partition x (memory s) beqPage beqIndex).
unfold cst in H5.
destruct v0;try contradiction.
apply inj_pairT2 in H5.
inversion H5.
auto.
unfold isVA in H4.
destruct (lookup partition sh1idx (memory s) beqPage beqIndex) in H2;try contradiction.
auto.
Qed.

(* For Bind Approach with Deep successor function *)

Lemma getFstShadowBindDeepH (partition : page) (P : W -> Prop) (fenv: funEnv) (env: valEnv) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ In partition (getPartitions multiplexer s)}}
fenv >> env >> (getFstShadowBindDeep partition) 
{{fun sh1 s => P s /\ nextEntryIsPP partition sh1idx sh1 s}}.
Proof.
unfold getFstShadowBindDeep.
eapply BindS_VHTT1.
eapply getSh1idxWp.
simpl; intros.
eapply BindS_VHTT1.
eapply weakenEval.
eapply succDWp. simpl.
simpl; intros; intuition.
instantiate (1:=(fun s => P s /\ partitionDescriptorEntry s /\ 
                          In partition (getPartitions multiplexer s))).
simpl. intuition.
instantiate (1:=sh1idx).
eapply H0 in H3.
specialize H3 with sh1idx.
eapply H3.
auto. auto.
simpl; intros.
eapply weakenEval.
eapply readPhysicalW.
simpl;intros.
intuition.
destruct H3.
exists x.
unfold partitionDescriptorEntry in H1.
apply H1 with partition sh1idx in H4.
clear H1.
intuition.
destruct H5.
exists x0.
intuition.
unfold nextEntryIsPP in H4.
unfold readPhysicalInternal.
subst.
inversion H2.
repeat apply inj_pair2 in H3.
unfold nextEntryIsPP in H5.
rewrite H3 in H5.
destruct (lookup partition x (memory s) beqPage beqIndex).
unfold cst in H5.
destruct v0;try contradiction.
apply inj_pairT2 in H5.
inversion H5.
auto.
unfold isVA in H4.
destruct (lookup partition sh1idx (memory s) beqPage beqIndex) in H2;try contradiction.
auto.
Qed.

(*Bind approach & Deep definition of Succ with recursive plus function*) 

Lemma getFstShadowBindDeepRecH (partition : page) (P : W -> Prop) (fenv: funEnv) (env: valEnv) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ In partition (getPartitions multiplexer s)}}
fenv >> env >> (getFstShadowBindDeepRec partition) 
{{fun sh1 s => P s /\ nextEntryIsPP partition sh1idx sh1 s}}.
Proof.
unfold getFstShadowBindDeep.
eapply BindS_VHTT1.
eapply getSh1idxWp.
simpl; intros.
eapply BindS_VHTT1.
eapply weakenEval.
eapply succRecWp. simpl.
simpl; intros; intuition.
instantiate (1:=(fun s => P s /\ partitionDescriptorEntry s /\ 
                          In partition (getPartitions multiplexer s))).
simpl. intuition.
instantiate (1:=sh1idx).
eapply H0 in H3.
specialize H3 with sh1idx.
eapply H3.
auto. auto.
simpl; intros.
eapply weakenEval.
eapply readPhysicalW.
simpl;intros.
intuition.
destruct H3.
exists x.
unfold partitionDescriptorEntry in H1.
apply H1 with partition sh1idx in H4.
clear H1.
intuition.
destruct H5.
exists x0.
intuition.
unfold nextEntryIsPP in H4.
unfold readPhysicalInternal.
subst.
inversion H2.
repeat apply inj_pair2 in H3.
unfold nextEntryIsPP in H5.
rewrite H3 in H5.
destruct (lookup partition x (memory s) beqPage beqIndex).
unfold cst in H5.
destruct v0;try contradiction.
apply inj_pairT2 in H5.
inversion H5.
auto.
unfold isVA in H4.
destruct (lookup partition sh1idx (memory s) beqPage beqIndex) in H2;try contradiction.
auto.
Qed.

(* For Apply Approach *)

Lemma getFstShadowApplyH (partition : page) (P : W -> Prop) (fenv: funEnv) (env: valEnv) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ In partition (getPartitions multiplexer s)}}
fenv >> env >> (getFstShadowApply partition) 
{{fun sh1 s => P s /\ nextEntryIsPP partition sh1idx sh1 s}}.
Proof.
unfold getFstShadowApply.
eapply Apply_VHTT1.
eapply weakenPrms.
unfold getSh1idx.
eapply succWp'.
simpl; intros.
intuition.
instantiate (1:=P).
auto.
eauto.
eapply H in H2.
specialize H2 with sh1idx.
eapply H2.
auto.
intuition.
eapply weakenEval.
eapply readPhysicalW'.
simpl; intros.
intuition.
destruct H3.
exists x.
unfold partitionDescriptorEntry in H.
apply H with partition sh1idx in H1.
clear H.
intuition.
destruct H5.
exists x0.
intuition.
unfold nextEntryIsPP in H5.
unfold readPhysicalInternal.
rewrite H1 in H5.
destruct (lookup partition x (memory s) beqPage beqIndex).
unfold cst in H5.
destruct v;try contradiction.
apply inj_pairT2 in H5.
inversion H5.
auto.
unfold isVA in H2.
destruct (lookup partition sh1idx (memory s) beqPage beqIndex) in H2;try contradiction.
auto.
Qed.

Lemma getFstShadowApplyH' (partition : page) (P : W -> Prop) (fenv: funEnv) (env: valEnv) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ In partition (getPartitions multiplexer s)}}
fenv >> env >> (getFstShadowApply partition) 
{{fun sh1 s => P s /\ nextEntryIsPP partition sh1idx sh1 s}}.
Proof.
unfold getFstShadowApply.
eapply Apply_VHTT1.
eapply Prms_VHTT1.
eapply Apply_VHTT1.
eapply Prms_VHTT1.
eapply getSh1idxWp.
intros; unfold THoarePrmsTriple_Eval; intros;simpl.
inversion X;subst.
destruct vs; inversion H5.
instantiate (1:= fun vs s => P s /\ partitionDescriptorEntry s /\
     In partition (getPartitions multiplexer s) /\ vs = [cst index sh1idx]).
intuition. f_equal. auto.
inversion X0.
intuition.
destruct vs.
unfold THoareTriple_Eval; intros.
intuition. inversion H3.
destruct vs.
Focus 2.
unfold THoareTriple_Eval; intros.
intuition. inversion H3.
unfold mkVEnv. simpl.
eapply weakenEval.
eapply succWp.
simpl; intros. 
instantiate (1:= sh1idx).
instantiate (1:= fun s => P s /\
    partitionDescriptorEntry s /\
    In partition (getPartitions multiplexer s)).
simpl. intuition.
eapply H in H1.
specialize H1 with sh1idx.
eapply H1.
auto.
inversion H3; intuition.
intros; simpl.
unfold THoarePrmsTriple_Eval; intros.
inversion X; subst.
destruct vs; inversion H5.
instantiate (1:= fun vs s => P s /\ partitionDescriptorEntry s /\
     In partition (getPartitions multiplexer s) 
     /\ (exists i : index,
     succIndexInternal sh1idx = Some i /\ vs = [cst (option index) (Some i)]) 
    ).
intuition.
destruct H3.
exists x.
intuition.
rewrite H0 in H2.
inversion H2; subst.
repeat apply inj_pair2 in H6.
auto.
f_equal.
auto.
inversion X0.
intuition.
destruct vs.
unfold THoareTriple_Eval; intros.
destruct H as [a [b [c d]]].
destruct d. destruct H.
inversion H0.
destruct vs.
Focus 2.
unfold THoareTriple_Eval; intros.
destruct H as [a [b [c d]]].
destruct d. destruct H.
inversion H0.
unfold mkVEnv; simpl.
eapply weakenEval.
eapply readPhysicalW.
simpl; intros.
intuition.
destruct H3.
exists x.
unfold partitionDescriptorEntry in H.
apply H with partition sh1idx in H1.
clear H.
intuition.
destruct H5.
exists x0.
intuition.
inversion H4;subst. auto.
unfold nextEntryIsPP in H5.
unfold readPhysicalInternal.
rewrite H1 in H5.
destruct (lookup partition x (memory s) beqPage beqIndex).
destruct v0;try contradiction.
unfold cst in H5.
apply inj_pairT2 in H5.
inversion H5.
auto.
unfold isVA in H2.
destruct (lookup partition sh1idx (memory s) beqPage beqIndex) in H2;try contradiction.
auto.
Qed.


End Hoare_Test_FstShadow.
