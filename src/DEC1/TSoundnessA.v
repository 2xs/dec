
Require Export Basics.

Require Export EnvLibA.
Require Export RelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Import StaticSemA.
Require Import DynamicSemA.
Require Import TRInductA.
Require Import WeakenA.

Require Import IdModTypeA.

Import ListNotations.

Module TSoundness (IdT: IdModType) <: IdModType.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module WeakenI := Weaken IdT.
Export WeakenI.

(** type soundness *)

Definition SoundExp (fenv: funEnv) (env: valEnv)
                     (e: Exp) (t: VTyp) (n: W)  
  := sigT2 (fun v: Value => ValueTyping v t)
           (fun v: Value => sigT (fun n': W =>
                         EClosure fenv env (Conf Exp n e)
                                                (Conf Exp n' (Val v)))).


Definition SoundPrms (fenv: funEnv) (env: valEnv)
                     (ps: Prms) (pt: PTyp) (n: W)  
  := sigT (fun es: list Exp =>
        sigT2 (isValueList2T es) 
              (fun vs: list Value =>
                 prod (PrmsTyping emptyE emptyE emptyE (PS es) pt)
                      (sigT (fun n': W =>
                         PrmsClosure fenv env (Conf Prms n ps)
                                               (Conf Prms n' (PS es)))))).


Definition SoundFun (env: valEnv) (tenv: valTC) 
                    (f: Fun) (t: VTyp) (n: W)  
  := match f with FC fenv' fps e0 e1 x i =>
           fps = tenv ->
           match i with 
           | 0 => SoundExp fenv' env e0 t n
           | S j => SoundExp ((x, FC fenv' fps e0 e1 x j) :: fenv')
                           env e1 t n
           end
      end.     


Definition SoundQFun (fenv: funEnv) (env: valEnv)
                      (tenv: valTC) (q: QFun) (t: VTyp) (n: W)  
  := sigT2 (fun f: Fun => SoundFun env tenv f t n)
           (fun f: Fun => forall n':W, QFClosure fenv (Conf QFun n' q)
                                           (Conf QFun n' (QF f))).


(*************************************************************)
      
Definition FunSoundness :=
     fun (f: Fun) (ft: FTyp) 
         (k: FunTyping f ft) => 
      forall env: valEnv, 
      MatchEnvsT ValueTyping env (extParType ft) ->
      forall n: W, SoundFun env (extParType ft) f (extRetType ft) n. 
      
Definition QFunSoundness :=
     fun (ftenv: funTC) (fenv: funEnv)
         (q: QFun) (ft: FTyp) 
         (k: QFunTyping ftenv fenv q ft) =>      
      MatchEnvsT FunTyping fenv ftenv -> 
      forall env: valEnv,                      
      MatchEnvsT ValueTyping env (extParType ft) ->   
      forall n: W,
        SoundQFun fenv env (extParType ft) q (extRetType ft) n.                          
Definition ExpSoundness :=
     fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (e: Exp) (t: VTyp) 
         (k: ExpTyping ftenv tenv fenv e t) =>
   MatchEnvsT FunTyping fenv ftenv ->
   forall env: valEnv,                      
   MatchEnvsT ValueTyping env tenv ->
   forall n: W, SoundExp fenv env e t n.

Definition PrmsSoundness :=
     fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (ps: Prms) (pt: PTyp) 
         (k: PrmsTyping ftenv tenv fenv ps pt) => 
   MatchEnvsT FunTyping fenv ftenv ->
   forall env: valEnv,                      
   MatchEnvsT ValueTyping env tenv ->
   forall n: W, SoundPrms fenv env ps pt n.  


Definition ExpTypingSound_rect :=
  ExpTyping_str_rect FunSoundness QFunSoundness 
                     ExpSoundness PrmsSoundness. 


Lemma ExpEval :
  forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (e: Exp) (t: VTyp)
   (k: ExpTyping ftenv tenv fenv e t),
   ExpSoundness ftenv tenv fenv e t k.
    
Proof.
eapply ExpTypingSound_rect.

- (** base Par_SSL *)
  unfold Par_SSL, ExpSoundness.
  constructor.

- (** step Par_SSL *)
  unfold Par_SSL, ExpSoundness.
  intros.  
  constructor.
  + assumption.
  + assumption.    
  + assumption.

- (** base Par_SSA *)
  unfold Par_SSA, FunSoundness.
  constructor.

- (** step Par_SSA *)
  unfold Par_SSA, FunSoundness.
  intros.
  constructor.
  + assumption.
  + assumption.
  + assumption.

- (** Par_SSB *)
  unfold Par_SSB, Par_SSA, FunSoundness.
  intros.
  econstructor.
  
(*  eapply (Forall2BT_split FunTyping _ 
                         fenv0 fenv1 ftenv0 ftenv1 x f t). *)
  + exact m0.
  + exact m1.
  + exact k.
  + assumption.
  + assumption.  
  + assumption.
  + assumption.
  + assumption.  

- (** base Par_F *)
  unfold FunSoundness, ExpSoundness, SoundFun.
  intros.
  simpl in *.
  specialize (X m env X0 n).
  exact X.

- (** step Par_F *)
  unfold FunSoundness, ExpSoundness, SoundFun, SoundExp.
  intros.
  clear H.
  eapply updateFEnvLemma with (x:= x)
            (v1:= FC fenv tenv e0 e1 x n) (v2:= FT tenv t) in m.
  specialize (X m env X1 n0).
  assumption.
  assumption.

- (** Par_Q - QF *)    
  unfold QFunSoundness, FunSoundness, SoundQFun. 
  intros.
  destruct ft. 
  intros.  
  constructor 1 with (x:=f).
  * eapply X.
    exact X1.
  * constructor.

- (** Par_Q - FId *)
  unfold QFunSoundness, Par_SSB, FunSoundness, Par_SSA, SoundQFun.
  intros.
  destruct ft.
  simpl.
  inversion X; subst.
  clear X.
  simpl in *.
  constructor 1 with (x:=f).
  + eapply X4.
    exact X1.
  + clear X2 X3 X4.
    constructor.
    constructor.
    constructor.
    inversion m; subst.
    (* rewrite H0. *)
    eapply ExRelValTNone with (venv:=ls1) in H.
    * eapply override_simpl3 with (env0:=(x,f)::ls3) in H.
      rewrite H0.
      rewrite <- H at 1.
      simpl.
      destruct (IdT.IdEqDec x x).
      {- auto. }
      {- intuition n. }
    (* * apply (FT prs_type ret_type). *)
    * eassumption.  
(** Par_E *)
-  (* modify *)
  unfold ExpSoundness, SoundExp.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q H H0 env H0' n.
  inversion H; subst.
  destruct v.
  destruct v.
  inversion H1; subst.
  subst T.
  simpl in H2.
  destruct H2.
  constructor 1 with (x:=cst T2 (b_eval _ _ XF n v)).
  + constructor.
    * reflexivity.
    * constructor.  
  + inversion H; subst.
    * inversion H1; subst.
      subst T.
      simpl in H2.
      clear H2.
      constructor 1 with (x:=b_exec _ _ XF n v).
      eapply StepIsEClos.
      constructor.
  + inversion X; subst.
    eapply ExTDefNatT with (venv:=env) (T:=T1) in X0.      
    * destruct X0 as [v k].
      constructor 1 with (x:= cst T2 (b_eval _ _ XF n v)).
      econstructor.
      {- constructor. }
      {- econstructor. }
      {- constructor 1 with (x:=b_exec _ _ XF n v). 
         econstructor.
         econstructor.
         econstructor.
         eassumption.
         eapply StepIsEClos.
         constructor. }
    * assumption.
    * assumption.
    * reflexivity.
- (* return *)
  unfold ExpSoundness, SoundExp.
  intros G ftenv tenv fenv q t H H0 env H0' n.
  inversion H; subst.
  + constructor 1 with (x:=v).
    * assumption.
    * constructor 1 with (x:=n).
      econstructor.
      {- econstructor. }
      {- constructor. }
  + inversion X; subst.
    eapply ExTDefVal with (venv:=env) in X0.     
    * destruct X0 as [v k1 k2].
      constructor 1 with (x:=v).
      {- assumption. }
      {- constructor 1 with (x:=n).
         econstructor. 
         + constructor.
           constructor.
           eassumption.             
         + eapply StepIsEClos.
           constructor.
      }
    * auto.   
- (* bindN *)
  unfold ExpSoundness, SoundExp.
  intros ftenv tenv fenv e1 e2 t1 t2.
  intros k1 k2 IH1 IH2.
  intros H0 env H0' n.  
  specialize (IH1 H0 env H0' n).
  destruct IH1 as [v0 k3 H2].
  destruct H2 as [n0 H2].
  specialize (IH2 H0 env H0' n0).
  destruct IH2 as [v2 k4 H3].
  destruct H3 as [n2 H3].
  constructor 1 with (x:=v2).
  + auto.
  + constructor 1 with (x:=n2).
    eapply (EClosConcat fenv env).
    * instantiate  (1 := Conf Exp n0 (BindN (Val v0) e2)).
      apply  BindN_extended_congruence.
      assumption.
    * econstructor.
      {- econstructor. }
      {- assumption. }
- (* BindS *)
  unfold ExpSoundness, SoundExp.
  intros ftenv tenv fenv x e1 e2 t1 t2.
  intros k1 k2 IH1 IH2.
  intros H0 env H0' n.  
  specialize (IH1 H0 env H0' n).
  destruct IH1 as [v1 k3 H1].
  destruct H1 as [n0 H1].
  specialize (IH2 H0 ((x, v1) :: env)).
  cut (MatchEnvsT ValueTyping ((x, v1) :: env) ((x, t1) :: tenv)).
  + intro.
    specialize (IH2 X n0).
    destruct IH2 as [v2 k4 H2].
    destruct H2 as [n1 H2].
    constructor 1 with (x:=v2).
    * assumption.   
    * constructor 1 with (x:=n1).    
      eapply EClosConcat.
      {- instantiate (1:= (Conf Exp n0 (BindS x (Val v1) e2))).
         apply BindS_extended_congruence.
         assumption.
      }   
      {- eapply EClosConcat.
         + eapply StepIsEClos.
           econstructor.
         + eapply EClosConcat.
           * eapply BindMS_extended_congruence.
             {- reflexivity. }
             {- reflexivity. }
             {- rewrite app_nil_l.
                eassumption.
             }
           * eapply StepIsEClos.
             constructor.
       }      
  + apply updateVEnvLemma.  
    * assumption.
    * assumption.
- (* BindMS *)
  unfold ExpSoundness, SoundExp.  
  intros ftenv ftenvP ftenv' tenv tenvP tenv' fenv fenvP fenv' envP e t.
  intros k1 k2 k3 E1 E2 E3 k4 IH.  
  intros H0 env H0' n.
  eapply (overrideVEnvLemma envP env tenvP tenv k1) in H0'.
  eapply (overrideFEnvLemma fenvP fenv ftenvP ftenv k3) in H0.
  cut (FEnvTyping fenv' ftenv').
  + cut (EnvTyping (envP ++ env) tenv').
    * intros H1' H1.
      specialize (IH H1 (envP ++ env) H1' n). 
      destruct IH as [v k5 H2].
      destruct H2 as [n1 H2].
      constructor 1 with (x:=v).
      {- auto. }
      {- constructor 1 with (x:=n1).
         eapply (EClosConcat fenv env).
         + eapply BindMS_extended_congruence.
           * reflexivity.
           * reflexivity.
           * rewrite <- E3. 
             eassumption.
         + eapply StepIsEClos.
           constructor.
      }    
    * rewrite E1.
      assumption.
  + rewrite E2.
    rewrite E3.
    assumption.
- (* Apply *)
  unfold QFunSoundness, PrmsSoundness, ExpSoundness, SoundExp.  
  intros ftenv tenv fps fenv q ps pt t.  
  intros E1 k1 k2 k3 IH1 IH2.
  intros H0 env H0' n.

  cut (sigT (fun n' : W =>
        (sigT (fun f: Fun =>
          sigT2 (fun es: list Exp => isValueListT es)
             (fun es: list Exp => prod
               (EClosure fenv env (Conf Exp n (Apply q ps))
                         (Conf Exp n' (Apply (QF f) (PS es))))
               (sigT2 (fun v : Value =>
                    sigT (fun n'' : W =>                  
                       EClosure fenv env
                             (Conf Exp n' (Apply (QF f) (PS es)))
                             (Conf Exp n'' (Val v)))) 
                    (fun v: Value => ValueTyping v t))))))).

  intros.
  + destruct X as [n1 X].
    destruct X as [f X].
    destruct X as [vls k4 X].
    destruct X as [H1 X].
    destruct X as [v X k5].   
    destruct X as [n2 H2].
    constructor 1 with (x:=v).
    * assumption.
    * constructor 1 with (x:=n2). 
      eapply EClosConcat.
      {- eassumption. }
      {- eassumption. }
  + inversion E1; subst.
    clear H.
    specialize (IH2 H0 env H0' n).
    unfold SoundPrms in IH2.
    destruct IH2 as [es H2].
    destruct H2 as [vs k6 H2].
    destruct H2 as [k7 H2].
    destruct H2 as [n1 H2].
    specialize (IH1 H0).
    specialize (IH1 (mkVEnv fps vs)).
    eapply matchListsAux02_T with (vs:=vs) in k7.
    * eapply prmsTypingAux_T in k7 as k9.
      {- unfold SoundQFun, SoundFun in IH1.
         unfold SoundExp in IH1.
         specialize (IH1 k9 n1).
         destruct IH1 as [f H3 H1].
         specialize (H1 n).
         constructor 1 with (x:=n1).
         constructor 1 with (x:=f).
         constructor 1 with (x:=es).
         + eapply isValueList2IsValueT.
           eassumption.
         + split.  
           * eapply EClosConcat.  
             {- instantiate (1:=(Conf Exp n (Apply (QF f) ps))).
                eapply Apply2_extended_congruence. 
                assumption. }
             {- eapply Apply1_extended_congruence.
                assumption. }
           * assert (length fps = length vs) as H5.
             {- eapply prmsAux2. 
                eassumption. }
             {- inversion k2; subst.
                inversion H1; subst.
                destruct f.
                inversion X; subst.
                
                specialize (H3 eq_refl).
                destruct H3 as [v k8 HF].
                destruct HF as [n2 HF].
                constructor 1 with (x:=v).
                constructor 1 with (x:=n2).
                econstructor.
                eapply Apply_EStep0.
                eassumption.
                assumption.
                reflexivity.
                eapply EClosConcat.
                eapply BindMS_extended_congruence.
                reflexivity.
                reflexivity.
                eapply (weaken fenv0 fenv (mkVEnv fps vs) env) in HF.
                eassumption. 
                apply StepIsEClos.
                constructor.
                assumption.

                specialize (H3 eq_refl).
                destruct H3 as [v k8 HF].
                destruct HF as [n3 HF].
                constructor 1 with (x:=v).
                constructor 1 with (x:=n3).
                econstructor.
                eapply Apply_EStep1.
                eassumption.
                assumption.
                reflexivity.
                eapply EClosConcat.
                eapply BindMS_extended_congruence.
                reflexivity.
                reflexivity.
                eapply (weaken _ fenv _ env) in HF.
                eassumption. 
                apply StepIsEClos.
                constructor.
                assumption.

                inversion X0. 

                destruct f. 
                inversion X; subst.
                assert (findE ls1 x = None).
                eapply ExRelValTNone in H.
                exact H.
                (* exact (FT fps t). *)
                exact X1.           
                inversion H1; subst.
                inversion X3; subst.
                eapply override_simpl3 with (env0:=(x,f0)::ls3) in H4.
                inversion X4; subst.
                rewrite <- H4 in H6.
                rewrite find_simpl0 in H6.
                inversion H6; subst.
                inversion X0; subst.
                
                specialize (H3 eq_refl).
                destruct H3 as [v k8 HF].
                destruct HF as [n3 HF].
                constructor 1 with (x:=v).
                constructor 1 with (x:=n3).
                econstructor.
                eapply Apply_EStep0.
                eassumption.
                assumption.
                reflexivity.
                eapply EClosConcat.
                eapply BindMS_extended_congruence.
                reflexivity.
                reflexivity.
                
                eapply (weaken fenv0 _ _ env) in HF.
                eassumption. 
                apply StepIsEClos.
                constructor.
                assumption.

                specialize (H3 eq_refl).
                destruct H3 as [v k8 HF].
                destruct HF as [n3 HF].
                constructor 1 with (x:=v).
                constructor 1 with (x:=n3).
                econstructor.
                eapply Apply_EStep1.
                eassumption.
                assumption.
                reflexivity.
                eapply EClosConcat.
                eapply BindMS_extended_congruence.
                reflexivity.
                reflexivity.
                
                eapply (weaken _ (ls1 ++
                     (x, FC fenv0 fps e0 e1 x0 (S n2)) :: ls3) _ env) in HF.
                eassumption. 
                apply StepIsEClos.
                constructor.
                assumption.
             }
           }  
      {- eapply prmsAux2.
         eassumption. }
    * assumption.

- (* Val *)
  unfold ExpSoundness, SoundExp. 
  intros.
  constructor 1 with (x:=v).
  + assumption.
  + constructor 1 with (x:=n).
    constructor.
- (* IFThenElse *)
  unfold ExpSoundness, SoundExp.    
  intros.
  specialize (X X2 env X3 n).
  destruct X as [v K X].
  destruct X as [n' X].
  specialize (X0 X2 env X3 n').
  destruct X0 as [v0 K0 X0].
  destruct X0 as [n0 X0].
  specialize (X1 X2 env X3 n').
  destruct X1 as [v1 K1 X1].
  destruct X1 as [n1 X1].
  inversion K; subst.
  subst T.
  destruct v as [T v].
  destruct v.
  
  unfold Bool in H.
  unfold vtyp in H.
  simpl in H.
  inversion H; subst.
 
  destruct v.
  + constructor 1 with (x:=v0).
    assumption.
    constructor 1 with (x:=n0).
    eapply EClosConcat.
    instantiate (1:=Conf Exp n'
       (IfThenElse (Val (existT ValueI bool (Cst bool true))) e2 e3)).
    eapply IfThenElse_extended_congruence.
    eassumption.

    econstructor.
    econstructor.

    eassumption.
  + constructor 1 with (x:=v1).
    assumption.
    constructor 1 with (x:=n1).
    eapply EClosConcat.
    eapply IfThenElse_extended_congruence.
    eassumption.
    econstructor.
    econstructor.
    eassumption.
- (** Par_P *)
  unfold Par_SSL, ExpSoundness, PrmsSoundness, SoundExp. 
  intros.
  dependent induction X.
  constructor 1 with (x:=nil).
  constructor 1 with (x:=nil).
  constructor.
  simpl.
  auto.
  split.
  constructor.
  constructor.
  constructor 1 with (x:=n).
  constructor.
  (**)
  clear X.
  specialize (p0 X0 env X1 n).
  destruct p0 as [v k1 X2].
  destruct X2 as [n1 H].
  inversion m; subst.
  specialize (IHX X2).
  specialize (IHX X0 env X1 n1).
  destruct IHX as [es IHX].
  destruct IHX as [vs k2 IHX].
  destruct IHX as [k3 IHX].
  destruct IHX as [n2 k4].
  constructor 1 with (x:=(Val v::es)).
  constructor 1 with (x:=v::vs).
  constructor.
  eapply IsValueList2T.
  simpl.
  inversion k2; subst.
  auto.
  split.
  constructor.
  constructor.
  constructor.
  assumption.
  inversion k3; subst.
  assumption.
  constructor 1 with (x:=n2).
  eapply PrmsConcat.
  eapply Pars_extended_congruence2.
  eassumption.  
  eapply Pars_extended_congruence1.  
  assumption.
Defined.

(************************************************************************)

Definition FunTypingSound_rect :=
  FunTyping_str_rect FunSoundness QFunSoundness 
                     ExpSoundness PrmsSoundness. 


Lemma FunEval :
  forall (f: Fun) (ft: FTyp)
   (k: FunTyping f ft),
   FunSoundness f ft k.
    
Proof.
eapply FunTypingSound_rect.

- (** base Par_SSL *)
  unfold Par_SSL, ExpSoundness.
  constructor.

- (** step Par_SSL *)
  unfold Par_SSL, ExpSoundness.
  intros.  
  constructor.
  + assumption.
  + assumption.    
  + assumption.

- (** base Par_SSA *)
  unfold Par_SSA, FunSoundness.
  constructor.

- (** step Par_SSA *)
  unfold Par_SSA, FunSoundness.
  intros.
  constructor.
  + assumption.
  + assumption.
  + assumption.

- (** Par_SSB *)
  unfold Par_SSB, Par_SSA, FunSoundness.
  intros.
  econstructor.
  
(*  eapply (Forall2BT_split FunTyping _ 
                         fenv0 fenv1 ftenv0 ftenv1 x f t). *)
  + exact m0.
  + exact m1.
  + exact k.
  + assumption.
  + assumption.  
  + assumption.
  + assumption.
  + assumption.  

- (** base Par_F *)
  unfold FunSoundness, ExpSoundness, SoundFun.
  intros.
  simpl in *.
  specialize (X m env X0 n).
  exact X.

- (** step Par_F *)
  unfold FunSoundness, ExpSoundness, SoundFun, SoundExp.
  intros.
  clear H.
  eapply updateFEnvLemma with (x:= x)
            (v1:= FC fenv tenv e0 e1 x n) (v2:= FT tenv t) in m.
  specialize (X m env X1 n0).
  assumption.
  assumption.

- (** Par_Q - QF *)    
  unfold QFunSoundness, FunSoundness, SoundQFun. 
  intros.
  destruct ft. 
  intros.  
  constructor 1 with (x:=f).
  * eapply X.
    exact X1.
  * constructor.

- (** Par_Q - FId *)
  unfold QFunSoundness, Par_SSB, FunSoundness, Par_SSA, SoundQFun.
  intros.
  destruct ft.
  simpl.
  inversion X; subst.
  clear X.
  simpl in *.
  constructor 1 with (x:=f).
  + eapply X4.
    exact X1.
  + clear X2 X3 X4.
    constructor.
    constructor.
    constructor.
    inversion m; subst.
    (* rewrite H0. *)
    eapply ExRelValTNone with (venv:=ls1) in H.
    * eapply override_simpl3 with (env0:=(x,f)::ls3) in H.
      rewrite H0.
      rewrite <- H at 1.
      simpl.
      destruct (IdT.IdEqDec x x).
      {- auto. }
      {- intuition n. }
    (* apply (FT prs_type ret_type). *)
    * eassumption.  
(** Par_E *)
-  (* modify *)
  unfold ExpSoundness, SoundExp.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q H H0 env H0' n.
  inversion H; subst.
  destruct v.
  destruct v.
  inversion H1; subst.
  subst T.
  simpl in H2.
  destruct H2.
  constructor 1 with (x:=cst T2 (b_eval _ _ XF n v)).
  + constructor.
    * reflexivity.
    * constructor.  
  + inversion H; subst.
    * inversion H1; subst.
      subst T.
      simpl in H2.
      clear H2.
      constructor 1 with (x:=b_exec _ _ XF n v).
      eapply StepIsEClos.
      constructor.
  + inversion X; subst.
    eapply ExTDefNatT with (venv:=env) (T:=T1) in X0.      
    * destruct X0 as [v k].
      constructor 1 with (x:= cst T2 (b_eval _ _ XF n v)).
      econstructor.
      {- constructor. }
      {- econstructor. }
      {- constructor 1 with (x:=b_exec _ _ XF n v). 
         econstructor.
         econstructor.
         econstructor.
         eassumption.
         eapply StepIsEClos.
         constructor. }
    * assumption.
    * assumption.
    * reflexivity.
- (* return *)
  unfold ExpSoundness, SoundExp.
  intros G ftenv tenv fenv q t H H0 env H0' n.
  inversion H; subst.
  + constructor 1 with (x:=v).
    * assumption.
    * constructor 1 with (x:=n).
      econstructor.
      {- econstructor. }
      {- constructor. }
  + inversion X; subst.
    eapply ExTDefVal with (venv:=env) in X0.     
    * destruct X0 as [v k1 k2].
      constructor 1 with (x:=v).
      {- assumption. }
      {- constructor 1 with (x:=n).
         econstructor. 
         + constructor.
           constructor.
           eassumption.             
         + eapply StepIsEClos.
           constructor.
      }
    * auto.   
- (* bindN *)
  unfold ExpSoundness, SoundExp.
  intros ftenv tenv fenv e1 e2 t1 t2.
  intros k1 k2 IH1 IH2.
  intros H0 env H0' n.  
  specialize (IH1 H0 env H0' n).
  destruct IH1 as [v0 k3 H2].
  destruct H2 as [n0 H2].
  specialize (IH2 H0 env H0' n0).
  destruct IH2 as [v2 k4 H3].
  destruct H3 as [n2 H3].
  constructor 1 with (x:=v2).
  + auto.
  + constructor 1 with (x:=n2).
    eapply (EClosConcat fenv env).
    * instantiate  (1 := Conf Exp n0 (BindN (Val v0) e2)).
      apply  BindN_extended_congruence.
      assumption.
    * econstructor.
      {- econstructor. }
      {- assumption. }
- (* BindS *)
  unfold ExpSoundness, SoundExp.
  intros ftenv tenv fenv x e1 e2 t1 t2.
  intros k1 k2 IH1 IH2.
  intros H0 env H0' n.  
  specialize (IH1 H0 env H0' n).
  destruct IH1 as [v1 k3 H1].
  destruct H1 as [n0 H1].
  specialize (IH2 H0 ((x, v1) :: env)).
  cut (MatchEnvsT ValueTyping ((x, v1) :: env) ((x, t1) :: tenv)).
  + intro.
    specialize (IH2 X n0).
    destruct IH2 as [v2 k4 H2].
    destruct H2 as [n1 H2].
    constructor 1 with (x:=v2).
    * assumption.   
    * constructor 1 with (x:=n1).    
      eapply EClosConcat.
      {- instantiate (1:= (Conf Exp n0 (BindS x (Val v1) e2))).
         apply BindS_extended_congruence.
         assumption.
      }   
      {- eapply EClosConcat.
         + eapply StepIsEClos.
           econstructor.
         + eapply EClosConcat.
           * eapply BindMS_extended_congruence.
             {- reflexivity. }
             {- reflexivity. }
             {- rewrite app_nil_l.
                eassumption.
             }
           * eapply StepIsEClos.
             constructor.
       }      
  + apply updateVEnvLemma.  
    * assumption.
    * assumption.
- (* BindMS *)
  unfold ExpSoundness, SoundExp.  
  intros ftenv ftenvP ftenv' tenv tenvP tenv' fenv fenvP fenv' envP e t.
  intros k1 k2 k3 E1 E2 E3 k4 IH.  
  intros H0 env H0' n.
  eapply (overrideVEnvLemma envP env tenvP tenv k1) in H0'.
  eapply (overrideFEnvLemma fenvP fenv ftenvP ftenv k3) in H0.
  cut (FEnvTyping fenv' ftenv').
  + cut (EnvTyping (envP ++ env) tenv').
    * intros H1' H1.
      specialize (IH H1 (envP ++ env) H1' n). 
      destruct IH as [v k5 H2].
      destruct H2 as [n1 H2].
      constructor 1 with (x:=v).
      {- auto. }
      {- constructor 1 with (x:=n1).
         eapply (EClosConcat fenv env).
         + eapply BindMS_extended_congruence.
           * reflexivity.
           * reflexivity.
           * rewrite <- E3. 
             eassumption.
         + eapply StepIsEClos.
           constructor.
      }    
    * rewrite E1.
      assumption.
  + rewrite E2.
    rewrite E3.
    assumption.
- (* Apply *)
  unfold QFunSoundness, PrmsSoundness, ExpSoundness, SoundExp.  
  intros ftenv tenv fps fenv q ps pt t.  
  intros E1 k1 k2 k3 IH1 IH2.
  intros H0 env H0' n.

  cut (sigT (fun n' : W =>
        (sigT (fun f: Fun =>
          sigT2 (fun es: list Exp => isValueListT es)
             (fun es: list Exp => prod
               (EClosure fenv env (Conf Exp n (Apply q ps))
                         (Conf Exp n' (Apply (QF f) (PS es))))
               (sigT2 (fun v : Value =>
                    sigT (fun n'' : W =>                  
                       EClosure fenv env
                             (Conf Exp n' (Apply (QF f) (PS es)))
                             (Conf Exp n'' (Val v)))) 
                    (fun v: Value => ValueTyping v t))))))).

  intros.
  + destruct X as [n1 X].
    destruct X as [f X].
    destruct X as [vls k4 X].
    destruct X as [H1 X].
    destruct X as [v X k5].   
    destruct X as [n2 H2].
    constructor 1 with (x:=v).
    * assumption.
    * constructor 1 with (x:=n2). 
      eapply EClosConcat.
      {- eassumption. }
      {- eassumption. }
  + inversion E1; subst.
    clear H.
    specialize (IH2 H0 env H0' n).
    unfold SoundPrms in IH2.
    destruct IH2 as [es H2].
    destruct H2 as [vs k6 H2].
    destruct H2 as [k7 H2].
    destruct H2 as [n1 H2].
    specialize (IH1 H0).
    specialize (IH1 (mkVEnv fps vs)).
    eapply matchListsAux02_T with (vs:=vs) in k7.
    * eapply prmsTypingAux_T in k7 as k9.
      {- unfold SoundQFun, SoundFun in IH1.
         unfold SoundExp in IH1.
         specialize (IH1 k9 n1).
         destruct IH1 as [f H3 H1].
         specialize (H1 n).
         constructor 1 with (x:=n1).
         constructor 1 with (x:=f).
         constructor 1 with (x:=es).
         + eapply isValueList2IsValueT.
           eassumption.
         + split.  
           * eapply EClosConcat.  
             {- instantiate (1:=(Conf Exp n (Apply (QF f) ps))).
                eapply Apply2_extended_congruence. 
                assumption. }
             {- eapply Apply1_extended_congruence.
                assumption. }
           * assert (length fps = length vs) as H5.
             {- eapply prmsAux2. 
                eassumption. }
             {- inversion k2; subst.
                inversion H1; subst.
                destruct f.
                inversion X; subst.
                
                specialize (H3 eq_refl).
                destruct H3 as [v k8 HF].
                destruct HF as [n2 HF].
                constructor 1 with (x:=v).
                constructor 1 with (x:=n2).
                econstructor.
                eapply Apply_EStep0.
                eassumption.
                assumption.
                reflexivity.
                eapply EClosConcat.
                eapply BindMS_extended_congruence.
                reflexivity.
                reflexivity.
                eapply (weaken fenv0 fenv (mkVEnv fps vs) env) in HF.
                eassumption. 
                apply StepIsEClos.
                constructor.
                assumption.

                specialize (H3 eq_refl).
                destruct H3 as [v k8 HF].
                destruct HF as [n3 HF].
                constructor 1 with (x:=v).
                constructor 1 with (x:=n3).
                econstructor.
                eapply Apply_EStep1.
                eassumption.
                assumption.
                reflexivity.
                eapply EClosConcat.
                eapply BindMS_extended_congruence.
                reflexivity.
                reflexivity.
                eapply (weaken _ fenv _ env) in HF.
                eassumption. 
                apply StepIsEClos.
                constructor.
                assumption.

                inversion X0. 

                destruct f. 
                inversion X; subst.
                assert (findE ls1 x = None).
                eapply ExRelValTNone in H.
                exact H.
                (* exact (FT fps t).*)
                exact X1.           
                inversion H1; subst.
                inversion X3; subst.
                eapply override_simpl3 with (env0:=(x,f0)::ls3) in H4.
                inversion X4; subst.
                rewrite <- H4 in H6.
                rewrite find_simpl0 in H6.
                inversion H6; subst.
                inversion X0; subst.
                
                specialize (H3 eq_refl).
                destruct H3 as [v k8 HF].
                destruct HF as [n3 HF].
                constructor 1 with (x:=v).
                constructor 1 with (x:=n3).
                econstructor.
                eapply Apply_EStep0.
                eassumption.
                assumption.
                reflexivity.
                eapply EClosConcat.
                eapply BindMS_extended_congruence.
                reflexivity.
                reflexivity.
                
                eapply (weaken fenv0 _ _ env) in HF.
                eassumption. 
                apply StepIsEClos.
                constructor.
                assumption.

                specialize (H3 eq_refl).
                destruct H3 as [v k8 HF].
                destruct HF as [n3 HF].
                constructor 1 with (x:=v).
                constructor 1 with (x:=n3).
                econstructor.
                eapply Apply_EStep1.
                eassumption.
                assumption.
                reflexivity.
                eapply EClosConcat.
                eapply BindMS_extended_congruence.
                reflexivity.
                reflexivity.
                
                eapply (weaken _ (ls1 ++
                     (x, FC fenv0 fps e0 e1 x0 (S n2)) :: ls3) _ env) in HF.
                eassumption. 
                apply StepIsEClos.
                constructor.
                assumption.
             }
           }  
      {- eapply prmsAux2.
         eassumption. }
    * assumption.

- (* Val *)
  unfold ExpSoundness, SoundExp. 
  intros.
  constructor 1 with (x:=v).
  + assumption.
  + constructor 1 with (x:=n).
    constructor.
- (* IFThenElse *)
  unfold ExpSoundness, SoundExp.    
  intros.
  specialize (X X2 env X3 n).
  destruct X as [v K X].
  destruct X as [n' X].
  specialize (X0 X2 env X3 n').
  destruct X0 as [v0 K0 X0].
  destruct X0 as [n0 X0].
  specialize (X1 X2 env X3 n').
  destruct X1 as [v1 K1 X1].
  destruct X1 as [n1 X1].
  inversion K; subst.
  subst T.
  destruct v as [T v].
  destruct v.
  
  unfold Bool in H.
  unfold vtyp in H.
  simpl in H.
  inversion H; subst.
 
  destruct v.
  + constructor 1 with (x:=v0).
    assumption.
    constructor 1 with (x:=n0).
    eapply EClosConcat.
    instantiate (1:=Conf Exp n'
       (IfThenElse (Val (existT ValueI bool (Cst bool true))) e2 e3)).
    eapply IfThenElse_extended_congruence.
    eassumption.

    econstructor.
    econstructor.

    eassumption.
  + constructor 1 with (x:=v1).
    assumption.
    constructor 1 with (x:=n1).
    eapply EClosConcat.
    eapply IfThenElse_extended_congruence.
    eassumption.
    econstructor.
    econstructor.
    eassumption.
- (** Par_P *)
  unfold Par_SSL, ExpSoundness, PrmsSoundness, SoundExp. 
  intros.
  dependent induction X.
  constructor 1 with (x:=nil).
  constructor 1 with (x:=nil).
  constructor.
  simpl.
  auto.
  split.
  constructor.
  constructor.
  constructor 1 with (x:=n).
  constructor.
  (**)
  clear X.
  specialize (p0 X0 env X1 n).
  destruct p0 as [v k1 X2].
  destruct X2 as [n1 H].
  inversion m; subst.
  specialize (IHX X2).
  specialize (IHX X0 env X1 n1).
  destruct IHX as [es IHX].
  destruct IHX as [vs k2 IHX].
  destruct IHX as [k3 IHX].
  destruct IHX as [n2 k4].
  constructor 1 with (x:=(Val v::es)).
  constructor 1 with (x:=v::vs).
  constructor.
  eapply IsValueList2T.
  simpl.
  inversion k2; subst.
  auto.
  split.
  constructor.
  constructor.
  constructor.
  assumption.
  inversion k3; subst.
  assumption.
  constructor 1 with (x:=n2).
  eapply PrmsConcat.
  eapply Pars_extended_congruence2.
  eassumption.  
  eapply Pars_extended_congruence1.  
  assumption.
Defined.



(*********************************************************************)

Definition QFunTypingSound_rect :=
  QFunTyping_str_rect FunSoundness QFunSoundness 
                     ExpSoundness PrmsSoundness. 


Lemma QFunEval :
  forall (ftenv: funTC) (fenv: funEnv)
   (q: QFun) (ft: FTyp)
   (k: QFunTyping ftenv fenv q ft),
   QFunSoundness ftenv fenv q ft k.
    
Proof.
eapply QFunTypingSound_rect.

- (** base Par_SSL *)
  unfold Par_SSL, ExpSoundness.
  constructor.

- (** step Par_SSL *)
  unfold Par_SSL, ExpSoundness.
  intros.  
  constructor.
  + assumption.
  + assumption.    
  + assumption.

- (** base Par_SSA *)
  unfold Par_SSA, FunSoundness.
  constructor.

- (** step Par_SSA *)
  unfold Par_SSA, FunSoundness.
  intros.
  constructor.
  + assumption.
  + assumption.
  + assumption.

- (** Par_SSB *)
  unfold Par_SSB, Par_SSA, FunSoundness.
  intros.
  econstructor.
  
(*  eapply (Forall2BT_split FunTyping _ 
                         fenv0 fenv1 ftenv0 ftenv1 x f t). *)
  + exact m0.
  + exact m1.
  + exact k.
  + assumption.
  + assumption.  
  + assumption.
  + assumption.
  + assumption.  

- (** base Par_F *)
  unfold FunSoundness, ExpSoundness, SoundFun.
  intros.
  simpl in *.
  specialize (X m env X0 n).
  exact X.

- (** step Par_F *)
  unfold FunSoundness, ExpSoundness, SoundFun, SoundExp.
  intros.
  clear H.
  eapply updateFEnvLemma with (x:= x)
            (v1:= FC fenv tenv e0 e1 x n) (v2:= FT tenv t) in m.
  specialize (X m env X1 n0).
  assumption.
  assumption.

- (** Par_Q - QF *)    
  unfold QFunSoundness, FunSoundness, SoundQFun. 
  intros.
  destruct ft. 
  intros.  
  constructor 1 with (x:=f).
  * eapply X.
    exact X1.
  * constructor.

- (** Par_Q - FId *)
  unfold QFunSoundness, Par_SSB, FunSoundness, Par_SSA, SoundQFun.
  intros.
  destruct ft.
  simpl.
  inversion X; subst.
  clear X.
  simpl in *.
  constructor 1 with (x:=f).
  + eapply X4.
    exact X1.
  + clear X2 X3 X4.
    constructor.
    constructor.
    constructor.
    inversion m; subst.
    (* rewrite H0. *)
    eapply ExRelValTNone with (venv:=ls1) in H.
    * eapply override_simpl3 with (env0:=(x,f)::ls3) in H.
      rewrite H0.
      rewrite <- H at 1.
      simpl.
      destruct (IdT.IdEqDec x x).
      {- auto. }
      {- intuition n. }
    (* apply (FT prs_type ret_type). *)
    * eassumption.  
(** Par_E *)
-  (* modify *)
  unfold ExpSoundness, SoundExp.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q H H0 env H0' n.
  inversion H; subst.
  destruct v.
  destruct v.
  inversion H1; subst.
  subst T.
  simpl in H2.
  destruct H2.
  constructor 1 with (x:=cst T2 (b_eval _ _ XF n v)).
  + constructor.
    * reflexivity.
    * constructor.  
  + inversion H; subst.
    * inversion H1; subst.
      subst T.
      simpl in H2.
      clear H2.
      constructor 1 with (x:=b_exec _ _ XF n v).
      eapply StepIsEClos.
      constructor.
  + inversion X; subst.
    eapply ExTDefNatT with (venv:=env) (T:=T1) in X0.      
    * destruct X0 as [v k].
      constructor 1 with (x:= cst T2 (b_eval _ _ XF n v)).
      econstructor.
      {- constructor. }
      {- econstructor. }
      {- constructor 1 with (x:=b_exec _ _ XF n v). 
         econstructor.
         econstructor.
         econstructor.
         eassumption.
         eapply StepIsEClos.
         constructor. }
    * assumption.
    * assumption.
    * reflexivity.
- (* return *)
  unfold ExpSoundness, SoundExp.
  intros G ftenv tenv fenv q t H H0 env H0' n.
  inversion H; subst.
  + constructor 1 with (x:=v).
    * assumption.
    * constructor 1 with (x:=n).
      econstructor.
      {- econstructor. }
      {- constructor. }
  + inversion X; subst.
    eapply ExTDefVal with (venv:=env) in X0.     
    * destruct X0 as [v k1 k2].
      constructor 1 with (x:=v).
      {- assumption. }
      {- constructor 1 with (x:=n).
         econstructor. 
         + constructor.
           constructor.
           eassumption.             
         + eapply StepIsEClos.
           constructor.
      }
    * auto.   
- (* bindN *)
  unfold ExpSoundness, SoundExp.
  intros ftenv tenv fenv e1 e2 t1 t2.
  intros k1 k2 IH1 IH2.
  intros H0 env H0' n.  
  specialize (IH1 H0 env H0' n).
  destruct IH1 as [v0 k3 H2].
  destruct H2 as [n0 H2].
  specialize (IH2 H0 env H0' n0).
  destruct IH2 as [v2 k4 H3].
  destruct H3 as [n2 H3].
  constructor 1 with (x:=v2).
  + auto.
  + constructor 1 with (x:=n2).
    eapply (EClosConcat fenv env).
    * instantiate  (1 := Conf Exp n0 (BindN (Val v0) e2)).
      apply  BindN_extended_congruence.
      assumption.
    * econstructor.
      {- econstructor. }
      {- assumption. }
- (* BindS *)
  unfold ExpSoundness, SoundExp.
  intros ftenv tenv fenv x e1 e2 t1 t2.
  intros k1 k2 IH1 IH2.
  intros H0 env H0' n.  
  specialize (IH1 H0 env H0' n).
  destruct IH1 as [v1 k3 H1].
  destruct H1 as [n0 H1].
  specialize (IH2 H0 ((x, v1) :: env)).
  cut (MatchEnvsT ValueTyping ((x, v1) :: env) ((x, t1) :: tenv)).
  + intro.
    specialize (IH2 X n0).
    destruct IH2 as [v2 k4 H2].
    destruct H2 as [n1 H2].
    constructor 1 with (x:=v2).
    * assumption.   
    * constructor 1 with (x:=n1).    
      eapply EClosConcat.
      {- instantiate (1:= (Conf Exp n0 (BindS x (Val v1) e2))).
         apply BindS_extended_congruence.
         assumption.
      }   
      {- eapply EClosConcat.
         + eapply StepIsEClos.
           econstructor.
         + eapply EClosConcat.
           * eapply BindMS_extended_congruence.
             {- reflexivity. }
             {- reflexivity. }
             {- rewrite app_nil_l.
                eassumption.
             }
           * eapply StepIsEClos.
             constructor.
       }      
  + apply updateVEnvLemma.  
    * assumption.
    * assumption.
- (* BindMS *)
  unfold ExpSoundness, SoundExp.  
  intros ftenv ftenvP ftenv' tenv tenvP tenv' fenv fenvP fenv' envP e t.
  intros k1 k2 k3 E1 E2 E3 k4 IH.  
  intros H0 env H0' n.
  eapply (overrideVEnvLemma envP env tenvP tenv k1) in H0'.
  eapply (overrideFEnvLemma fenvP fenv ftenvP ftenv k3) in H0.
  cut (FEnvTyping fenv' ftenv').
  + cut (EnvTyping (envP ++ env) tenv').
    * intros H1' H1.
      specialize (IH H1 (envP ++ env) H1' n). 
      destruct IH as [v k5 H2].
      destruct H2 as [n1 H2].
      constructor 1 with (x:=v).
      {- auto. }
      {- constructor 1 with (x:=n1).
         eapply (EClosConcat fenv env).
         + eapply BindMS_extended_congruence.
           * reflexivity.
           * reflexivity.
           * rewrite <- E3. 
             eassumption.
         + eapply StepIsEClos.
           constructor.
      }    
    * rewrite E1.
      assumption.
  + rewrite E2.
    rewrite E3.
    assumption.
- (* Apply *)
  unfold QFunSoundness, PrmsSoundness, ExpSoundness, SoundExp.  
  intros ftenv tenv fps fenv q ps pt t.  
  intros E1 k1 k2 k3 IH1 IH2.
  intros H0 env H0' n.

  cut (sigT (fun n' : W =>
        (sigT (fun f: Fun =>
          sigT2 (fun es: list Exp => isValueListT es)
             (fun es: list Exp => prod
               (EClosure fenv env (Conf Exp n (Apply q ps))
                         (Conf Exp n' (Apply (QF f) (PS es))))
               (sigT2 (fun v : Value =>
                    sigT (fun n'' : W =>                  
                       EClosure fenv env
                             (Conf Exp n' (Apply (QF f) (PS es)))
                             (Conf Exp n'' (Val v)))) 
                    (fun v: Value => ValueTyping v t))))))).

  intros.
  + destruct X as [n1 X].
    destruct X as [f X].
    destruct X as [vls k4 X].
    destruct X as [H1 X].
    destruct X as [v X k5].   
    destruct X as [n2 H2].
    constructor 1 with (x:=v).
    * assumption.
    * constructor 1 with (x:=n2). 
      eapply EClosConcat.
      {- eassumption. }
      {- eassumption. }
  + inversion E1; subst.
    clear H.
    specialize (IH2 H0 env H0' n).
    unfold SoundPrms in IH2.
    destruct IH2 as [es H2].
    destruct H2 as [vs k6 H2].
    destruct H2 as [k7 H2].
    destruct H2 as [n1 H2].
    specialize (IH1 H0).
    specialize (IH1 (mkVEnv fps vs)).
    eapply matchListsAux02_T with (vs:=vs) in k7.
    * eapply prmsTypingAux_T in k7 as k9.
      {- unfold SoundQFun, SoundFun in IH1.
         unfold SoundExp in IH1.
         specialize (IH1 k9 n1).
         destruct IH1 as [f H3 H1].
         specialize (H1 n).
         constructor 1 with (x:=n1).
         constructor 1 with (x:=f).
         constructor 1 with (x:=es).
         + eapply isValueList2IsValueT.
           eassumption.
         + split.  
           * eapply EClosConcat.  
             {- instantiate (1:=(Conf Exp n (Apply (QF f) ps))).
                eapply Apply2_extended_congruence. 
                assumption. }
             {- eapply Apply1_extended_congruence.
                assumption. }
           * assert (length fps = length vs) as H5.
             {- eapply prmsAux2. 
                eassumption. }
             {- inversion k2; subst.
                inversion H1; subst.
                destruct f.
                inversion X; subst.
                
                specialize (H3 eq_refl).
                destruct H3 as [v k8 HF].
                destruct HF as [n2 HF].
                constructor 1 with (x:=v).
                constructor 1 with (x:=n2).
                econstructor.
                eapply Apply_EStep0.
                eassumption.
                assumption.
                reflexivity.
                eapply EClosConcat.
                eapply BindMS_extended_congruence.
                reflexivity.
                reflexivity.
                eapply (weaken fenv0 fenv (mkVEnv fps vs) env) in HF.
                eassumption. 
                apply StepIsEClos.
                constructor.
                assumption.

                specialize (H3 eq_refl).
                destruct H3 as [v k8 HF].
                destruct HF as [n3 HF].
                constructor 1 with (x:=v).
                constructor 1 with (x:=n3).
                econstructor.
                eapply Apply_EStep1.
                eassumption.
                assumption.
                reflexivity.
                eapply EClosConcat.
                eapply BindMS_extended_congruence.
                reflexivity.
                reflexivity.
                eapply (weaken _ fenv _ env) in HF.
                eassumption. 
                apply StepIsEClos.
                constructor.
                assumption.

                inversion X0. 

                destruct f. 
                inversion X; subst.
                assert (findE ls1 x = None).
                eapply ExRelValTNone in H.
                exact H.
                (* exact (FT fps t). *)
                exact X1.           
                inversion H1; subst.
                inversion X3; subst.
                eapply override_simpl3 with (env0:=(x,f0)::ls3) in H4.
                inversion X4; subst.
                rewrite <- H4 in H6.
                rewrite find_simpl0 in H6.
                inversion H6; subst.
                inversion X0; subst.
                
                specialize (H3 eq_refl).
                destruct H3 as [v k8 HF].
                destruct HF as [n3 HF].
                constructor 1 with (x:=v).
                constructor 1 with (x:=n3).
                econstructor.
                eapply Apply_EStep0.
                eassumption.
                assumption.
                reflexivity.
                eapply EClosConcat.
                eapply BindMS_extended_congruence.
                reflexivity.
                reflexivity.
                
                eapply (weaken fenv0 _ _ env) in HF.
                eassumption. 
                apply StepIsEClos.
                constructor.
                assumption.

                specialize (H3 eq_refl).
                destruct H3 as [v k8 HF].
                destruct HF as [n3 HF].
                constructor 1 with (x:=v).
                constructor 1 with (x:=n3).
                econstructor.
                eapply Apply_EStep1.
                eassumption.
                assumption.
                reflexivity.
                eapply EClosConcat.
                eapply BindMS_extended_congruence.
                reflexivity.
                reflexivity.
                
                eapply (weaken _ (ls1 ++
                     (x, FC fenv0 fps e0 e1 x0 (S n2)) :: ls3) _ env) in HF.
                eassumption. 
                apply StepIsEClos.
                constructor.
                assumption.
             }
           }  
      {- eapply prmsAux2.
         eassumption. }
    * assumption.

- (* Val *)
  unfold ExpSoundness, SoundExp. 
  intros.
  constructor 1 with (x:=v).
  + assumption.
  + constructor 1 with (x:=n).
    constructor.
- (* IFThenElse *)
  unfold ExpSoundness, SoundExp.    
  intros.
  specialize (X X2 env X3 n).
  destruct X as [v K X].
  destruct X as [n' X].
  specialize (X0 X2 env X3 n').
  destruct X0 as [v0 K0 X0].
  destruct X0 as [n0 X0].
  specialize (X1 X2 env X3 n').
  destruct X1 as [v1 K1 X1].
  destruct X1 as [n1 X1].
  inversion K; subst.
  subst T.
  destruct v as [T v].
  destruct v.
  
  unfold Bool in H.
  unfold vtyp in H.
  simpl in H.
  inversion H; subst.
 
  destruct v.
  + constructor 1 with (x:=v0).
    assumption.
    constructor 1 with (x:=n0).
    eapply EClosConcat.
    instantiate (1:=Conf Exp n'
       (IfThenElse (Val (existT ValueI bool (Cst bool true))) e2 e3)).
    eapply IfThenElse_extended_congruence.
    eassumption.

    econstructor.
    econstructor.

    eassumption.
  + constructor 1 with (x:=v1).
    assumption.
    constructor 1 with (x:=n1).
    eapply EClosConcat.
    eapply IfThenElse_extended_congruence.
    eassumption.
    econstructor.
    econstructor.
    eassumption.
- (** Par_P *)
  unfold Par_SSL, ExpSoundness, PrmsSoundness, SoundExp. 
  intros.
  dependent induction X.
  constructor 1 with (x:=nil).
  constructor 1 with (x:=nil).
  constructor.
  simpl.
  auto.
  split.
  constructor.
  constructor.
  constructor 1 with (x:=n).
  constructor.
  (**)
  clear X.
  specialize (p0 X0 env X1 n).
  destruct p0 as [v k1 X2].
  destruct X2 as [n1 H].
  inversion m; subst.
  specialize (IHX X2).
  specialize (IHX X0 env X1 n1).
  destruct IHX as [es IHX].
  destruct IHX as [vs k2 IHX].
  destruct IHX as [k3 IHX].
  destruct IHX as [n2 k4].
  constructor 1 with (x:=(Val v::es)).
  constructor 1 with (x:=v::vs).
  constructor.
  eapply IsValueList2T.
  simpl.
  inversion k2; subst.
  auto.
  split.
  constructor.
  constructor.
  constructor.
  assumption.
  inversion k3; subst.
  assumption.
  constructor 1 with (x:=n2).
  eapply PrmsConcat.
  eapply Pars_extended_congruence2.
  eassumption.  
  eapply Pars_extended_congruence1.  
  assumption.
Defined.



(*************************************************************************)

Definition PrmsTypingSound_rect :=
  PrmsTyping_str_rect FunSoundness QFunSoundness 
                     ExpSoundness PrmsSoundness. 


Lemma PrmsEval :
  forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (ps: Prms) (pt: PTyp)
   (k: PrmsTyping ftenv tenv fenv ps pt),
   PrmsSoundness ftenv tenv fenv ps pt k.
    
Proof.
eapply PrmsTypingSound_rect.

- (** base Par_SSL *)
  unfold Par_SSL, ExpSoundness.
  constructor.

- (** step Par_SSL *)
  unfold Par_SSL, ExpSoundness.
  intros.  
  constructor.
  + assumption.
  + assumption.    
  + assumption.

- (** base Par_SSA *)
  unfold Par_SSA, FunSoundness.
  constructor.

- (** step Par_SSA *)
  unfold Par_SSA, FunSoundness.
  intros.
  constructor.
  + assumption.
  + assumption.
  + assumption.

- (** Par_SSB *)
  unfold Par_SSB, Par_SSA, FunSoundness.
  intros.
  econstructor.
  
(*  eapply (Forall2BT_split FunTyping _ 
                         fenv0 fenv1 ftenv0 ftenv1 x f t). *)
  + exact m0.
  + exact m1.
  + exact k.
  + assumption.
  + assumption.  
  + assumption.
  + assumption.
  + assumption.  

- (** base Par_F *)
  unfold FunSoundness, ExpSoundness, SoundFun.
  intros.
  simpl in *.
  specialize (X m env X0 n).
  exact X.

- (** step Par_F *)
  unfold FunSoundness, ExpSoundness, SoundFun, SoundExp.
  intros.
  clear H.
  eapply updateFEnvLemma with (x:= x)
            (v1:= FC fenv tenv e0 e1 x n) (v2:= FT tenv t) in m.
  specialize (X m env X1 n0).
  assumption.
  assumption.

- (** Par_Q - QF *)    
  unfold QFunSoundness, FunSoundness, SoundQFun. 
  intros.
  destruct ft. 
  intros.  
  constructor 1 with (x:=f).
  * eapply X.
    exact X1.
  * constructor.

- (** Par_Q - FId *)
  unfold QFunSoundness, Par_SSB, FunSoundness, Par_SSA, SoundQFun.
  intros.
  destruct ft.
  simpl.
  inversion X; subst.
  clear X.
  simpl in *.
  constructor 1 with (x:=f).
  + eapply X4.
    exact X1.
  + clear X2 X3 X4.
    constructor.
    constructor.
    constructor.
    inversion m; subst.
    (* rewrite H0. *)
    eapply ExRelValTNone with (venv:=ls1) in H.
    * eapply override_simpl3 with (env0:=(x,f)::ls3) in H.
      rewrite H0.
      rewrite <- H at 1.
      simpl.
      destruct (IdT.IdEqDec x x).
      {- auto. }
      {- intuition n. }
    (* apply (FT prs_type ret_type). *)
    * eassumption.  
(** Par_E *)
-  (* modify *)
  unfold ExpSoundness, SoundExp.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q H H0 env H0' n.
  inversion H; subst.
  destruct v.
  destruct v.
  inversion H1; subst.
  subst T.
  simpl in H2.
  destruct H2.
  constructor 1 with (x:=cst T2 (b_eval _ _ XF n v)).
  + constructor.
    * reflexivity.
    * constructor.  
  + inversion H; subst.
    * inversion H1; subst.
      subst T.
      simpl in H2.
      clear H2.
      constructor 1 with (x:=b_exec _ _ XF n v).
      eapply StepIsEClos.
      constructor.
  + inversion X; subst.
    eapply ExTDefNatT with (venv:=env) (T:=T1) in X0.      
    * destruct X0 as [v k].
      constructor 1 with (x:= cst T2 (b_eval _ _ XF n v)).
      econstructor.
      {- constructor. }
      {- econstructor. }
      {- constructor 1 with (x:=b_exec _ _ XF n v). 
         econstructor.
         econstructor.
         econstructor.
         eassumption.
         eapply StepIsEClos.
         constructor. }
    * assumption.
    * assumption.
    * reflexivity.
- (* return *)
  unfold ExpSoundness, SoundExp.
  intros G ftenv tenv fenv q t H H0 env H0' n.
  inversion H; subst.
  + constructor 1 with (x:=v).
    * assumption.
    * constructor 1 with (x:=n).
      econstructor.
      {- econstructor. }
      {- constructor. }
  + inversion X; subst.
    eapply ExTDefVal with (venv:=env) in X0.     
    * destruct X0 as [v k1 k2].
      constructor 1 with (x:=v).
      {- assumption. }
      {- constructor 1 with (x:=n).
         econstructor. 
         + constructor.
           constructor.
           eassumption.             
         + eapply StepIsEClos.
           constructor.
      }
    * auto.   
- (* bindN *)
  unfold ExpSoundness, SoundExp.
  intros ftenv tenv fenv e1 e2 t1 t2.
  intros k1 k2 IH1 IH2.
  intros H0 env H0' n.  
  specialize (IH1 H0 env H0' n).
  destruct IH1 as [v0 k3 H2].
  destruct H2 as [n0 H2].
  specialize (IH2 H0 env H0' n0).
  destruct IH2 as [v2 k4 H3].
  destruct H3 as [n2 H3].
  constructor 1 with (x:=v2).
  + auto.
  + constructor 1 with (x:=n2).
    eapply (EClosConcat fenv env).
    * instantiate  (1 := Conf Exp n0 (BindN (Val v0) e2)).
      apply  BindN_extended_congruence.
      assumption.
    * econstructor.
      {- econstructor. }
      {- assumption. }
- (* BindS *)
  unfold ExpSoundness, SoundExp.
  intros ftenv tenv fenv x e1 e2 t1 t2.
  intros k1 k2 IH1 IH2.
  intros H0 env H0' n.  
  specialize (IH1 H0 env H0' n).
  destruct IH1 as [v1 k3 H1].
  destruct H1 as [n0 H1].
  specialize (IH2 H0 ((x, v1) :: env)).
  cut (MatchEnvsT ValueTyping ((x, v1) :: env) ((x, t1) :: tenv)).
  + intro.
    specialize (IH2 X n0).
    destruct IH2 as [v2 k4 H2].
    destruct H2 as [n1 H2].
    constructor 1 with (x:=v2).
    * assumption.   
    * constructor 1 with (x:=n1).    
      eapply EClosConcat.
      {- instantiate (1:= (Conf Exp n0 (BindS x (Val v1) e2))).
         apply BindS_extended_congruence.
         assumption.
      }   
      {- eapply EClosConcat.
         + eapply StepIsEClos.
           econstructor.
         + eapply EClosConcat.
           * eapply BindMS_extended_congruence.
             {- reflexivity. }
             {- reflexivity. }
             {- rewrite app_nil_l.
                eassumption.
             }
           * eapply StepIsEClos.
             constructor.
       }      
  + apply updateVEnvLemma.  
    * assumption.
    * assumption.
- (* BindMS *)
  unfold ExpSoundness, SoundExp.  
  intros ftenv ftenvP ftenv' tenv tenvP tenv' fenv fenvP fenv' envP e t.
  intros k1 k2 k3 E1 E2 E3 k4 IH.  
  intros H0 env H0' n.
  eapply (overrideVEnvLemma envP env tenvP tenv k1) in H0'.
  eapply (overrideFEnvLemma fenvP fenv ftenvP ftenv k3) in H0.
  cut (FEnvTyping fenv' ftenv').
  + cut (EnvTyping (envP ++ env) tenv').
    * intros H1' H1.
      specialize (IH H1 (envP ++ env) H1' n). 
      destruct IH as [v k5 H2].
      destruct H2 as [n1 H2].
      constructor 1 with (x:=v).
      {- auto. }
      {- constructor 1 with (x:=n1).
         eapply (EClosConcat fenv env).
         + eapply BindMS_extended_congruence.
           * reflexivity.
           * reflexivity.
           * rewrite <- E3. 
             eassumption.
         + eapply StepIsEClos.
           constructor.
      }    
    * rewrite E1.
      assumption.
  + rewrite E2.
    rewrite E3.
    assumption.
- (* Apply *)
  unfold QFunSoundness, PrmsSoundness, ExpSoundness, SoundExp.  
  intros ftenv tenv fps fenv q ps pt t.  
  intros E1 k1 k2 k3 IH1 IH2.
  intros H0 env H0' n.

  cut (sigT (fun n' : W =>
        (sigT (fun f: Fun =>
          sigT2 (fun es: list Exp => isValueListT es)
             (fun es: list Exp => prod
               (EClosure fenv env (Conf Exp n (Apply q ps))
                         (Conf Exp n' (Apply (QF f) (PS es))))
               (sigT2 (fun v : Value =>
                    sigT (fun n'' : W =>                  
                       EClosure fenv env
                             (Conf Exp n' (Apply (QF f) (PS es)))
                             (Conf Exp n'' (Val v)))) 
                    (fun v: Value => ValueTyping v t))))))).

  intros.
  + destruct X as [n1 X].
    destruct X as [f X].
    destruct X as [vls k4 X].
    destruct X as [H1 X].
    destruct X as [v X k5].   
    destruct X as [n2 H2].
    constructor 1 with (x:=v).
    * assumption.
    * constructor 1 with (x:=n2). 
      eapply EClosConcat.
      {- eassumption. }
      {- eassumption. }
  + inversion E1; subst.
    clear H.
    specialize (IH2 H0 env H0' n).
    unfold SoundPrms in IH2.
    destruct IH2 as [es H2].
    destruct H2 as [vs k6 H2].
    destruct H2 as [k7 H2].
    destruct H2 as [n1 H2].
    specialize (IH1 H0).
    specialize (IH1 (mkVEnv fps vs)).
    eapply matchListsAux02_T with (vs:=vs) in k7.
    * eapply prmsTypingAux_T in k7 as k9.
      {- unfold SoundQFun, SoundFun in IH1.
         unfold SoundExp in IH1.
         specialize (IH1 k9 n1).
         destruct IH1 as [f H3 H1].
         specialize (H1 n).
         constructor 1 with (x:=n1).
         constructor 1 with (x:=f).
         constructor 1 with (x:=es).
         + eapply isValueList2IsValueT.
           eassumption.
         + split.  
           * eapply EClosConcat.  
             {- instantiate (1:=(Conf Exp n (Apply (QF f) ps))).
                eapply Apply2_extended_congruence. 
                assumption. }
             {- eapply Apply1_extended_congruence.
                assumption. }
           * assert (length fps = length vs) as H5.
             {- eapply prmsAux2. 
                eassumption. }
             {- inversion k2; subst.
                inversion H1; subst.
                destruct f.
                inversion X; subst.
                
                specialize (H3 eq_refl).
                destruct H3 as [v k8 HF].
                destruct HF as [n2 HF].
                constructor 1 with (x:=v).
                constructor 1 with (x:=n2).
                econstructor.
                eapply Apply_EStep0.
                eassumption.
                assumption.
                reflexivity.
                eapply EClosConcat.
                eapply BindMS_extended_congruence.
                reflexivity.
                reflexivity.
                eapply (weaken fenv0 fenv (mkVEnv fps vs) env) in HF.
                eassumption. 
                apply StepIsEClos.
                constructor.
                assumption.

                specialize (H3 eq_refl).
                destruct H3 as [v k8 HF].
                destruct HF as [n3 HF].
                constructor 1 with (x:=v).
                constructor 1 with (x:=n3).
                econstructor.
                eapply Apply_EStep1.
                eassumption.
                assumption.
                reflexivity.
                eapply EClosConcat.
                eapply BindMS_extended_congruence.
                reflexivity.
                reflexivity.
                eapply (weaken _ fenv _ env) in HF.
                eassumption. 
                apply StepIsEClos.
                constructor.
                assumption.

                inversion X0. 

                destruct f. 
                inversion X; subst.
                assert (findE ls1 x = None).
                eapply ExRelValTNone in H.
                exact H.
                (* exact (FT fps t).*)
                exact X1.           
                inversion H1; subst.
                inversion X3; subst.
                eapply override_simpl3 with (env0:=(x,f0)::ls3) in H4.
                inversion X4; subst.
                rewrite <- H4 in H6.
                rewrite find_simpl0 in H6.
                inversion H6; subst.
                inversion X0; subst.
                
                specialize (H3 eq_refl).
                destruct H3 as [v k8 HF].
                destruct HF as [n3 HF].
                constructor 1 with (x:=v).
                constructor 1 with (x:=n3).
                econstructor.
                eapply Apply_EStep0.
                eassumption.
                assumption.
                reflexivity.
                eapply EClosConcat.
                eapply BindMS_extended_congruence.
                reflexivity.
                reflexivity.
                
                eapply (weaken fenv0 _ _ env) in HF.
                eassumption. 
                apply StepIsEClos.
                constructor.
                assumption.

                specialize (H3 eq_refl).
                destruct H3 as [v k8 HF].
                destruct HF as [n3 HF].
                constructor 1 with (x:=v).
                constructor 1 with (x:=n3).
                econstructor.
                eapply Apply_EStep1.
                eassumption.
                assumption.
                reflexivity.
                eapply EClosConcat.
                eapply BindMS_extended_congruence.
                reflexivity.
                reflexivity.
                
                eapply (weaken _ (ls1 ++
                     (x, FC fenv0 fps e0 e1 x0 (S n2)) :: ls3) _ env) in HF.
                eassumption. 
                apply StepIsEClos.
                constructor.
                assumption.
             }
           }  
      {- eapply prmsAux2.
         eassumption. }
    * assumption.

- (* Val *)
  unfold ExpSoundness, SoundExp. 
  intros.
  constructor 1 with (x:=v).
  + assumption.
  + constructor 1 with (x:=n).
    constructor.
- (* IFThenElse *)
  unfold ExpSoundness, SoundExp.    
  intros.
  specialize (X X2 env X3 n).
  destruct X as [v K X].
  destruct X as [n' X].
  specialize (X0 X2 env X3 n').
  destruct X0 as [v0 K0 X0].
  destruct X0 as [n0 X0].
  specialize (X1 X2 env X3 n').
  destruct X1 as [v1 K1 X1].
  destruct X1 as [n1 X1].
  inversion K; subst.
  subst T.
  destruct v as [T v].
  destruct v.
  
  unfold Bool in H.
  unfold vtyp in H.
  simpl in H.
  inversion H; subst.
 
  destruct v.
  + constructor 1 with (x:=v0).
    assumption.
    constructor 1 with (x:=n0).
    eapply EClosConcat.
    instantiate (1:=Conf Exp n'
       (IfThenElse (Val (existT ValueI bool (Cst bool true))) e2 e3)).
    eapply IfThenElse_extended_congruence.
    eassumption.

    econstructor.
    econstructor.

    eassumption.
  + constructor 1 with (x:=v1).
    assumption.
    constructor 1 with (x:=n1).
    eapply EClosConcat.
    eapply IfThenElse_extended_congruence.
    eassumption.
    econstructor.
    econstructor.
    eassumption.
- (** Par_P *)
  unfold Par_SSL, ExpSoundness, PrmsSoundness, SoundExp. 
  intros.
  dependent induction X.
  constructor 1 with (x:=nil).
  constructor 1 with (x:=nil).
  constructor.
  simpl.
  auto.
  split.
  constructor.
  constructor.
  constructor 1 with (x:=n).
  constructor.
  (**)
  clear X.
  specialize (p0 X0 env X1 n).
  destruct p0 as [v k1 X2].
  destruct X2 as [n1 H].
  inversion m; subst.
  specialize (IHX X2).
  specialize (IHX X0 env X1 n1).
  destruct IHX as [es IHX].
  destruct IHX as [vs k2 IHX].
  destruct IHX as [k3 IHX].
  destruct IHX as [n2 k4].
  constructor 1 with (x:=(Val v::es)).
  constructor 1 with (x:=v::vs).
  constructor.
  eapply IsValueList2T.
  simpl.
  inversion k2; subst.
  auto.
  split.
  constructor.
  constructor.
  constructor.
  assumption.
  inversion k3; subst.
  assumption.
  constructor 1 with (x:=n2).
  eapply PrmsConcat.
  eapply Pars_extended_congruence2.
  eassumption.  
  eapply Pars_extended_congruence1.  
  assumption.
Defined.


   
(***********************************************************************)

(** not used *)


Definition SoundExpT (fenv: funEnv) (env: valEnv)
                   (e: Exp) (t: VTyp) (n: W) 
                   (k: SoundExp fenv env e t n) : SoundExp fenv env e t n := k.

Definition SoundPrmsT (fenv: funEnv) (env: valEnv)
                   (ps: Prms) (pt: PTyp) (n: W) 
                   (k: SoundPrms fenv env ps pt n) :
  SoundPrms fenv env ps pt n := k.

Definition SoundFunT (f: Fun) (ft: FTyp) (n: W)
        (k0: FunTyping f ft)
        (env: valEnv)
        (k: SoundFun env (extParType ft) f (extRetType ft) n) : 
                    SoundFun env (extParType ft) f (extRetType ft) n := k.

Definition SoundQFunT (ftenv: funTC) (fenv: funEnv)
         (q: QFun) (ft: FTyp) (n: W)
         (k0: QFunTyping ftenv fenv q ft)
         (env: valEnv)  
         (k: SoundQFun fenv env (extParType ft) q (extRetType ft) n) :
  SoundQFun fenv env (extParType ft) q (extRetType ft) n := k.


(***)

Definition FunSoundnessO :=
     fun (f: Fun) (ft: FTyp) 
         (k: FunTyping f ft) =>
   match ft with FT tenv t =>      
      forall env: valEnv, 
      MatchEnvsT ValueTyping env tenv ->
      forall n: W, SoundFun env tenv f t n
   end. 

Definition QFunSoundnessO :=
     fun (ftenv: funTC) (fenv: funEnv)
         (q: QFun) (ft: FTyp) 
         (k: QFunTyping ftenv fenv q ft) =>
   match ft with FT tenv t =>      
      MatchEnvsT FunTyping fenv ftenv -> 
      forall env: valEnv,                      
      MatchEnvsT ValueTyping env tenv ->   
      forall n: W, SoundQFun fenv env tenv q t n
   end.                          


End TSoundness.
