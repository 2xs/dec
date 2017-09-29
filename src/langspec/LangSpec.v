(*  DEC 1.0 language specification.
   Paolo Torrini and David Nowak, 
   Universite' Lille-1 - CRIStAL-CNRS
*)

Require Export List. 
Require Import DEC.AuxLib.
Require Import DEC.ModTyp. 

Import ListNotations.


(** * DEC 1.0 language specification *)

(** Syntax definition, static semantics, dynamic small-step semantics *)

Module LSpec (IdT: ModTyp) <: ModTyp.
Export IdT.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.


(** * Syntax definition *)

(** Inductively defined syntactic categories and definitions *)

(* *)

(** Generic effect record *)

Record XFun (T1 T2: Type) : Type := {
    b_mod : W -> T1 -> prod W T2 ;
    b_exec : W -> T1 -> W := fun state input => fst (b_mod state input) ;
    b_eval : W -> T1 -> T2 := fun state input => snd (b_mod state input)        
}.                                                     

(** Admissible value types *)

Instance NatVT : ValTyp nat.
  
Instance UnitVT : ValTyp unit.

Instance BoolVT : ValTyp bool.

(**********************************************************************)

(** Value types *)

(** - The type of value types *)

Definition VTyp : Type := sig ValTyp.

(** - Smart value type constructor *)

Definition vtyp (T: Type) {VT: ValTyp T} : VTyp :=
    @exist Type ValTyp T VT.

(** - Extractor *)

Definition vtypExt (t: VTyp) : Type := proj1_sig t.

(** - Value type abbreviations *)

Definition Nat : VTyp := vtyp nat.

Definition Unit : VTyp := vtyp unit.

Definition Bool : VTyp := vtyp bool.


(************************************************************************)

(** - Parameter types *)

Inductive PTyp : Type := PT (ts: list VTyp).

(** - Value typing contexts *)

Definition valTC : Type := list (Id * VTyp).

(** - Function types *)

Inductive FTyp : Type := FT (prs_type: valTC) (ret_type: VTyp).

(** - Function typing contexts *)

Definition funTC : Type := list (Id * FTyp).

(** - Extractors for function types *)

Definition extParType (ft: FTyp) : valTC :=
  match ft with FT ps _ => ps end.

Definition extRetType (ft: FTyp) : VTyp :=
  match ft with FT _ t => t end.


(***************************************************************************)

(** Value expressions *)

(** - The internal type of values, parametrised by Gallina types *)

Inductive ValueI (T: Type) : Type := Cst (v: T).

(** - The external type of values, hiding Gallina types *)

Definition Value : Type := sigT ValueI.

(** - Smart value constructor *)

Definition cst (T: Type) (v: T) : Value :=
           @existT Type ValueI T (Cst T v).

(** - Extractors *)

Definition ValueI2T (T: Type) (v: ValueI T) : T :=
    match v with Cst _  x => x end.             

Definition cstExt (v: Value) : projT1 v := ValueI2T (projT1 v) (projT2 v).


(***********************************************************************)

(** - Value environments *)

Definition valEnv : Type := list (Id * Value).

(** Quasi-values *)
Inductive QValue : Type := Var (x: Id) | QV (v: Value).


(*************************************************************************)

(** Syntactic type tags *)

Inductive Tag : Type := LL | RR.

(*************************************************************************)

(** Program terms *)

(** Syntactic categories defined by mutual induction: 
    functions, quasi-functions, expressions, parameters *)

Inductive Fun : (** - Functions *)
   Type := FC (fenv: Envr Id Fun) 
              (tenv: valTC) (e0 e1: Exp) (x: Id) (n: nat)
with QFun : (** - Quasi-functions *)
   Type := FVar (x: Id) | QF (v: Fun)
with Exp : (** - Expressions *)
       Type :=
         | Val (v: Value)
         | Return (G: Tag) (q: QValue)
         | BindN (e1: Exp) (e2: Exp) 
         | BindS (x: Id) (e1: Exp) (e2: Exp) 
         | BindMS (fenv: Envr Id Fun) (venv: valEnv) (e: Exp)
         | IfThenElse (e1: Exp) (e2: Exp) (e3: Exp)       
         | Apply (q: QFun) (ps: Prms) 
         | Modify (T1 T2: Type) (VT1: ValTyp T1) (VT2: ValTyp T2)
                  (XF: XFun T1 T2) (q: QValue)
with Prms : (** - Parameters *)
   Type := PS (es: list Exp).


(** Function environments *)

Definition funEnv : Type := Envr Id Fun.


(** Top-level programs *)

Inductive Prog : Type := prog (e: Exp)
             | define (x: Id) (f: Fun) (p: Prog).



(** Auxiliary functions *)

(** - Conversion from typing contexts to type lists *)

Definition env2ptyp (m: valTC) : PTyp := PT (map snd m).


(** - Creation of value environments *)

Definition mkVEnv (tenv: valTC) (vs: list Value) : valEnv :=
     interleave (map fst tenv) vs.


(*************************************************************************)

(** Abbreviations *)

Definition NatCst (v: nat) : Value := cst nat v.

Definition UnitCst (v: unit) : Value := cst unit v.

Definition BoolCst (v: bool) : Value := cst bool v.
 
Definition TrueV : Exp := Val (cst bool true).

Definition FalseV : Exp := Val (cst bool false).

Definition UnitV : Exp := Val (cst unit tt).

Definition VLift := Return LL.

Definition Skip : Exp := VLift (QV (cst unit tt)).

Definition NoRet (e: Exp) : Exp := BindN e Skip. 



Instance PState_ValTyp : ValTyp (PState W).

Definition xf_read {T: Type} (f: W -> T) : XFun unit T := {|
   b_mod := fun x _ => (x, f x)     
|}.                                                     

Definition xf_write {T: Type} (f: T -> W) : XFun T unit := {|
   b_mod := fun _ x => (f x, tt)     
|}.                                                     

Definition xf_reset : XFun (PState W) unit := {|
   b_mod := fun x _ => (b_init, tt)     
|}.                                                     

Definition Read {T: Type} (VT: ValTyp T) (f: W -> T) : Exp :=
  Modify unit T UnitVT VT (xf_read f) (QV (cst unit tt)).

Definition Write {T: Type} (VT: ValTyp T) (f: T -> W) (x: T) : Exp :=
  Modify T unit VT UnitVT (xf_write f) (QV (cst T x)).

Definition Reset : Exp :=
  Modify (PState W) unit PState_ValTyp UnitVT xf_reset
         (QV (cst (PState W) WP)).



(************************************************************************)

(** * Static semantics *)

(** Typing relations for the syntactic categories *)

(* *)

(** Value typing *)

Inductive ValueTyping (v: Value) (t: VTyp) : Type :=
| ValueTypingC : let T := projT1 v
          in T = (proj1_sig t) ->
             ValTyp T -> 
             ValueTyping v t.

(** Smart value constructor *)

Definition valueTyping (T: Type) {VT: ValTyp T} (v: T) :
  ValueTyping (cst T v) (vtyp T) :=
   ValueTypingC (cst T v) (vtyp T) eq_refl VT. 

(** Typing of identifiers *)

Inductive IdTyping : valTC -> Id -> VTyp -> Type :=
   | Id_Typing : forall (tenv: valTC) (x: Id) (t: VTyp), 
                    findET tenv x t -> 
                    IdTyping tenv x t.

(** Typing of quasi-values *)

Inductive QValueTyping : valTC -> QValue -> VTyp -> Type :=
  | ProperValue_Typing : forall (tenv: valTC ) (v: Value) (t: VTyp),
                   ValueTyping v t -> 
                   QValueTyping tenv (QV v) t
  | Var_Typing : forall (tenv: valTC) (x: Id) (t: VTyp),
                   IdTyping tenv x t -> 
                   QValueTyping tenv (Var x) t.

(** Typing of value environments *)

Definition EnvTyping : valEnv -> valTC -> Type :=
    MatchEnvsT ValueTyping.


(** Typing of program terms *)

Inductive FunTyping : (** - Bounded recursive functions *)
  Fun -> FTyp -> Type :=
(** - with no fuel *)  
  | FunZ_Typing: forall (ftenv: funTC) (tenv: valTC)
                        (fenv: funEnv) 
                        (e0 e1: Exp) (x: Id) (t: VTyp),
      MatchEnvsT FunTyping fenv ftenv -> 
      ExpTyping ftenv tenv fenv e0 t -> 
      FunTyping (FC fenv tenv e0 e1 x 0) (FT tenv t)
(** - with some fuel *)                
  | FunS_Typing: forall (ftenv: funTC) (tenv: valTC)
                        (fenv: funEnv) 
            (e0 e1: Exp) (x: Id) (n: nat) (t: VTyp),
      let ftenv' := (x, FT tenv t) :: ftenv in 
      let fenv' := (x, FC fenv tenv e0 e1 x n) :: fenv in 
      MatchEnvsT FunTyping fenv ftenv -> 
      ExpTyping ftenv' tenv fenv' e1 t -> 
      FunTyping (FC fenv tenv e0 e1 x n) (FT tenv t) ->
      FunTyping (FC fenv tenv e0 e1 x (S n)) (FT tenv t)
with QFunTyping : (** - Quasi-functions *)
       funTC -> funEnv -> QFun -> FTyp -> Type :=
(** - lifting of a function *)       
  | QF_Typing: forall (ftenv: funTC) (fenv: funEnv) (f: Fun) (ft: FTyp),
      FunTyping f ft ->
      QFunTyping ftenv fenv (QF f) ft
(** - lifting of a function variable *)                 
  | FVar_Typing: forall (ftenv: funTC) (fenv: funEnv)
                       (x: Id) (f: Fun) (ft: FTyp),
      MatchEnvs2BT FunTyping x f ft fenv ftenv ->  
      QFunTyping ftenv fenv (FVar x) ft
with ExpTyping : (** Expressions *)
       funTC -> valTC -> funEnv -> Exp -> VTyp -> Type :=
(** - lifting of values *)                        
  | Val_Typing : forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv) 
                        (v: Value) (t: VTyp), 
                       ValueTyping v t -> 
                       ExpTyping ftenv tenv fenv (Val v) t
(** - tagged lifting of quasi-values *)                               
  | Return_Typing : forall (G: Tag)
                           (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                           (q: QValue) (t: VTyp),
                       QValueTyping tenv q t ->  
                       ExpTyping ftenv tenv fenv (Return G q) t
(** - sequencing *)                                 
  | BindN_Typing : forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                          (e1 e2: Exp) (t1 t2: VTyp), 
                       ExpTyping ftenv tenv fenv e1 t1 ->
                       ExpTyping ftenv tenv fenv e2 t2 ->
                       ExpTyping ftenv tenv fenv (BindN e1 e2) t2
(** - let-style binding of identifiers *)
  | BindS_Typing : forall (ftenv: funTC) (tenv: valTC) 
                          (fenv: funEnv) (x: Id) 
                          (e1 e2: Exp) (t1 t2: VTyp), 
                       let tenv' := (x, t1) :: tenv in  
                       ExpTyping ftenv tenv fenv e1 t1 ->
                       ExpTyping ftenv tenv' fenv e2 t2 ->
                       ExpTyping ftenv tenv fenv (BindS x e1 e2) t2
(** - binding by local environments *)                                 
  | BindMS_Typing : forall (ftenv ftenvP ftenv': funTC)
                           (tenv tenvP tenv': valTC)
                           (fenv fenvP fenv': funEnv) (envP: valEnv) 
                           (e: Exp) (t: VTyp), 
                       MatchEnvsT ValueTyping envP tenvP ->
                       MatchEnvsT FunTyping fenv ftenv -> 
                       MatchEnvsT FunTyping fenvP ftenvP ->
                       tenv' = tenvP ++ tenv ->
                       ftenv' = ftenvP ++ ftenv ->                        
                       fenv' = fenvP ++ fenv ->                         
                       ExpTyping ftenv' tenv' fenv' e t ->
                       ExpTyping ftenv tenv fenv (BindMS fenvP envP e) t
(** - conditional expression *)                                 
  | IfThenElse_Typing : forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                               (e1 e2 e3: Exp) (t: VTyp),
             ExpTyping ftenv tenv fenv e1 Bool ->
             ExpTyping ftenv tenv fenv e2 t ->
             ExpTyping ftenv tenv fenv e3 t ->
             ExpTyping ftenv tenv fenv (IfThenElse e1 e2 e3) t
(** - function application *)                                 
  | Apply_Typing : forall (ftenv: funTC) (tenv fps: valTC) (fenv: funEnv)
                          (q: QFun) (ps: Prms) (pt: PTyp) (t: VTyp),
              pt = PT (map snd fps) ->    
              MatchEnvsT FunTyping fenv ftenv -> 
              QFunTyping ftenv fenv q (FT fps t) ->
              PrmsTyping ftenv tenv fenv ps pt ->
              ExpTyping ftenv tenv fenv (Apply q ps) t
(** - call to a generic effect (external function) *)       
  | Modify_Typing : forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                           (T1 T2: Type) (VT1: ValTyp T1) (VT2: ValTyp T2)
                           (XF: XFun T1 T2) (q: QValue),
                     QValueTyping tenv q (vtyp T1) ->  
                     ExpTyping ftenv tenv fenv
                               (Modify T1 T2 VT1 VT2 XF q) (vtyp T2)
with PrmsTyping : (** - Parameters *)
         funTC -> valTC -> funEnv -> Prms -> PTyp -> Type :=
| PS_Typing: forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                    (es: list Exp) (ts: list VTyp),
      Forall2T (ExpTyping ftenv tenv fenv) es ts ->          
      PrmsTyping ftenv tenv fenv (PS es) (PT ts).


(** Typing of function environments *)

Definition FEnvTyping : funEnv -> funTC -> Type :=
    MatchEnvsT FunTyping.


(** Typing of top-level programs *)

Inductive ProgTyping : 
    funTC -> funEnv -> Prog -> VTyp -> Type := 
| Prog_Typing : forall (ftenv: funTC) (fenv: funEnv) (e: Exp) (t: VTyp),
                   MatchEnvsT FunTyping fenv ftenv -> 
                   ProgTyping ftenv fenv (prog e) t
| Define_Typing : forall (ftenv ftenv': funTC) (fenv fenv': funEnv)   
                         (x: Id) (f: Fun) (p: Prog)
                         (ft: FTyp) (t: VTyp), 
      MatchEnvsT FunTyping fenv ftenv -> 
      ftenv' = (x, ft) :: ftenv -> 
      fenv' = (x, f) :: fenv -> 
      QFunTyping ftenv fenv (QF f) ft ->
      ProgTyping ftenv' fenv' p t ->
      ProgTyping ftenv fenv (define x f p) t.


(********************************************************************)

(** Value lists in Prop *)

Inductive isValue (e: Exp) : Prop :=
  IsValue : forall (v: Value), e = Val v -> isValue e.

Definition isValueList (ls : list Exp) : Prop :=
Forall isValue ls.

Inductive isValueList2  
  (els : list Exp) (vls : list Value) : Prop :=
IsValueList2 :  els = map Val vls -> isValueList2 els vls.

(** Value lists in Type *)

Inductive isValueT (e: Exp) : Type :=
  IsValueT : forall (v: Value), e = Val v -> isValueT e.

Definition isValueListT (ls : list Exp) : Type :=
ForallT isValueT ls.

Inductive isValueList2T  
  (els : list Exp) (vls : list Value) : Type :=
IsValueList2T :  els = map Val vls -> isValueList2T els vls.


(*********************************************************************)

(** * Dynamic semantics *)

(** Inductively defined transition relations that define one-step
execution on program-and-state configurations *)

(* *)

(** Configurations *)

Inductive AConfig (T: Type) : Type := Conf (state: W) (qq: T).


(** Quasi-value computation *)

Inductive QVStep :
   valEnv -> AConfig QValue -> AConfig QValue -> Type :=
   OK_QVStep : forall (env: valEnv) (n: W) (x: Id) (v: Value),
          findET env x v ->  
          QVStep env (Conf QValue n (Var x))
                       (Conf QValue n (QV v)).

(** Quasi-function computation *)

Inductive QFStep :
   funEnv -> AConfig QFun -> AConfig QFun -> Type :=
   OK_QFStep : forall (env: funEnv) (n: W) (x: Id) (v: Fun),
          findET env x v ->  
          QFStep env (Conf QFun n (FVar x))
                       (Conf QFun n (QF v)).


(** Program term computation *)    

Inductive EStep : (** - Expressions *)
  funEnv -> valEnv -> AConfig Exp -> AConfig Exp -> Type :=
(** - tagged q-value lifting *)
| Return_EStep : forall (G: Tag)
                        (fenv: funEnv) (env: valEnv) (n: W) (v: Value),
    EStep fenv env (Conf Exp n (Return G (QV v)))
                        (Conf Exp n (Val v))
| Return_Cg_EStep : forall (G: Tag)
                           (fenv: funEnv) (env: valEnv) 
                           (n n': W) (q q': QValue),
    QVStep env (Conf QValue n q) (Conf QValue n' q') ->
    EStep fenv env (Conf Exp n (Return G q)) (Conf Exp n' (Return G q'))
(** - sequencing *)
| BindN_EStep : forall (fenv: funEnv) (env: valEnv)
                       (n: W) (v: Value) (e: Exp),
    EStep fenv env (Conf Exp n (BindN (Val v) e)) (Conf Exp n e)
| BindN_Cg_EStep : forall (fenv: funEnv) (env: valEnv) 
                          (n n': W) (e1 e1' e2: Exp),
    EStep fenv env (Conf Exp n e1) (Conf Exp n' e1') ->
    EStep fenv env (Conf Exp n (BindN e1 e2))
                        (Conf Exp n' (BindN e1' e2))
(** - let-style binding *)
| BindS_EStep : forall (fenv: funEnv) (env: valEnv) 
                       (n: W) (x: Id) (v: Value) (e: Exp),          
    EStep fenv env (Conf Exp n (BindS x (Val v) e))
                        (Conf Exp n (BindMS emptyE (singleE x v) e))
| BindS_Cg_EStep : forall (fenv: funEnv) (env: valEnv) 
                          (n n': W) (x: Id) (e1 e1' e2: Exp),
    EStep fenv env (Conf Exp n e1) (Conf Exp n' e1') ->
    EStep fenv env (Conf Exp n (BindS x e1 e2))     
                        (Conf Exp n' (BindS x e1' e2))
(** - local environments *)
| BindMS_EStep : forall (fenv fenv': funEnv) (env env': valEnv)    
                        (n: W) (v: Value),
    EStep fenv env (Conf Exp n (BindMS fenv' env' (Val v)))
                     (Conf Exp n (Val v))
| BindMS_Cg_EStep : forall (fenv fenvL fenv': funEnv)
                           (env envL env': valEnv) 
                           (n n': W) (e e': Exp),
    fenv' = fenvL ++ fenv -> 
    env' = envL ++ env ->
    EStep fenv' env' (Conf Exp n e) (Conf Exp n' e') ->
    EStep fenv env (Conf Exp n (BindMS fenvL envL e))
                   (Conf Exp n' (BindMS fenvL envL e'))
(** - conditional *)
| IfThenElse_EStep1 :  forall (fenv: funEnv) (env: valEnv)
                              (n: W) (e1 e2: Exp),
     EStep fenv env (Conf Exp n (IfThenElse (Val (cst bool true)) e1 e2))
                         (Conf Exp n e1)                   
| IfThenElse_EStep2 :  forall (fenv: funEnv) (env: valEnv)
                              (n: W) (e1 e2: Exp),
     EStep fenv env (Conf Exp n
                (IfThenElse (Val (cst bool false)) e1 e2))
                         (Conf Exp n e2)
| IfThenElse_Cg_EStep :  forall (fenv: funEnv) (env: valEnv)
                                (n n': W) (e e' e1 e2: Exp),
     EStep fenv env (Conf Exp n e) (Conf Exp n' e') ->                       
     EStep fenv env (Conf Exp n (IfThenElse e e1 e2))
                         (Conf Exp n' (IfThenElse e' e1 e2))
(** - function application *)
| Apply_EStep0 : forall (fenv fenv': funEnv) (env env': valEnv)
                        (n: W) (e0 e1: Exp)
                        (es: list Exp) (vs: list Value)
                        (x: Id) 
                        (pt: valTC),
     isValueList2T es vs ->              
     length pt = length vs ->
     env' = mkVEnv pt vs ->
     EStep fenv env (Conf Exp n
              (Apply (QF (FC fenv' pt e0 e1 x 0)) (PS es)))
                     (Conf Exp n (BindMS fenv' env' e0))
| Apply_EStep1 : forall (fenv fenv': funEnv) (env env': valEnv)
                        (n: W) (e0 e1: Exp)
                        (es: list Exp) (vs: list Value)
                        (x: Id) (i: nat)
                        (pt: valTC),
     isValueList2T es vs ->              
     length pt = length vs ->
     env' = mkVEnv pt vs ->
     EStep fenv env
           (Conf Exp n (Apply (QF (FC fenv' pt e0 e1 x (S i))) (PS es)))
           (Conf Exp n
                 (BindMS ((x,(FC fenv' pt e0 e1 x i))::fenv') env' e1))
                   | Apply_Cg1_EStep : forall (fenv: funEnv) (env: valEnv)
                           (n n': W) 
                           (f: Fun) (ps ps': Prms),
     PrmsStep fenv env (Conf Prms n ps) (Conf Prms n' ps') ->
     EStep fenv env (Conf Exp n (Apply (QF f) ps))
                         (Conf Exp n' (Apply (QF f) ps'))
| Apply_Cg2_EStep : forall (fenv: funEnv) (env: valEnv)
                           (n n': W) 
                           (qf qf': QFun) (ps: Prms),
     QFStep fenv (Conf QFun n qf) (Conf QFun n' qf') ->
     EStep fenv env (Conf Exp n (Apply qf ps))
                         (Conf Exp n' (Apply qf' ps))
(** - modify *)
| Modify_EStep : forall (fenv: funEnv) (env: valEnv) (n: W)
                        (T1 T2: Type) (VT1: ValTyp T1) (VT2: ValTyp T2)
                        (XF: XFun T1 T2) (w: T1),
    EStep fenv env
       (Conf Exp n (Modify T1 T2 VT1 VT2 XF (QV (cst T1 w))))
       (Conf Exp (b_exec T1 T2 XF n w)
                   (Val (cst T2 (b_eval T1 T2 XF n w))))
| Modify_Cg_EStep : forall (fenv: funEnv) (env: valEnv) (n n': W)
                        (T1 T2: Type) (VT1: ValTyp T1) (VT2: ValTyp T2)
                        (XF: XFun T1 T2) (q q': QValue),
    QVStep env (Conf QValue n q) (Conf QValue n' q') ->
    EStep fenv env (Conf Exp n (Modify T1 T2 VT1 VT2 XF q))
                        (Conf Exp n' (Modify T1 T2 VT1 VT2 XF q'))

with PrmsStep : (** - Parameters *)
       funEnv -> valEnv -> AConfig Prms -> AConfig Prms -> Type :=
| Prms_Cg_Step : forall (fenv: funEnv) (env: valEnv)
                   (n n': W) 
                   (es es': list Exp) (v: Value),
         PrmsStep fenv env (Conf Prms n (PS es))
                                (Conf Prms n' (PS es')) ->
         PrmsStep fenv env (Conf Prms n (PS (Val v :: es)))
                                (Conf Prms n' (PS (Val v :: es')))
| Prms_Step1 : forall (fenv: funEnv) (env: valEnv)
                   (n n': W) (es: list Exp) (e e': Exp),
         EStep fenv env (Conf Exp n e) (Conf Exp n' e') ->   
         PrmsStep fenv env (Conf Prms n (PS (e::es)))
                                (Conf Prms n' (PS (e'::es))).


(** Top-level program computation *)

Inductive PStep :
          funEnv -> AConfig Prog -> AConfig Prog -> Type := 
| Prog_PStep : forall (fenv: funEnv) (env: valEnv)   
                      (n n': W) (e e': Exp),
                 EStep fenv env (Conf Exp n e) (Conf Exp n' e') ->
                 env = emptyE -> 
                 PStep fenv (Conf Prog n (prog e))
                                 (Conf Prog n' (prog e'))
| Define_PStep : forall (fenv: funEnv) (env: valEnv)   
                        (n: W) (x: Id) (f: Fun) (v: Value),
      PStep fenv (Conf Prog n (define x f (prog (Val v))))
                      (Conf Prog n (prog (Val v)))
| Define_Cg_PStep : forall (fenv fenv': funEnv)     
                           (n n': W) 
                           (x: Id) (f: Fun) (p p': Prog),
      fenv' = (x, f) :: fenv ->                 
      PStep fenv' (Conf Prog n p) (Conf Prog n' p') ->
      PStep fenv (Conf Prog n (define x f p))
                      (Conf Prog n' (define x f p')).



End LSpec.


  





