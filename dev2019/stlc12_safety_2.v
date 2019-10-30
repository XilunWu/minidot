Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.

Require Export stlc12.

(* ############################################################ *)
(* Proofs                                                       *)
(* ############################################################ *)

(* ### Some helper lemmas ### *)

Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.

Hint Constructors option.
Hint Constructors list.
Hint Constructors env.

Hint Unfold index.
Hint Unfold length.
Hint Unfold expand_env.
Hint Unfold lookup.
Hint Unfold index.
Hint Unfold sanitize_env.
Hint Unfold sanitize_any.

Hint Resolve ex_intro.

(* ############################################################ *)
(* Definitions                                                  *)
(* ############################################################ *)

(* ### Value typing and well-typed runtime environments ### *)

Inductive wf_env : venv -> tenv -> Prop := 
| wfe_nil : forall n, wf_env (Def vl nil nil n) (Def ty nil nil n)
| wfe_cons : forall v t vs ts n,
    val_type (expand_env vs v n) v t ->
    wf_env vs ts ->
    get_inv_idx vs = get_inv_idx ts ->
    wf_env (expand_env vs v n) (expand_env ts t n)

with val_type : venv -> vl -> ty -> Prop :=
     | v_bool: forall venv b,
         val_type venv (vbool b) TBool
     | v_rec: forall venv,
         val_type venv vrec TRec
     | v_abs: forall env venv tenv y T1 T2 m,
         wf_env venv tenv ->
         has_type (expand_env (expand_env tenv (TFun T1 m T2) Second) T1 m) y First T2 ->
         val_type env (vabs venv m y) (TFun T1 m T2)
     | v_absrec: forall env venv tenv y T1 T2 m,
         wf_env venv tenv ->
         has_type (expand_env (expand_env tenv (TFunRec T1 m T2) Second) T1 m) y First T2 ->
         val_type env (vabsrec venv m y) (TFunRec T1 m T2)
.

(* type equivalence: only via reflexivity *)
Inductive stp: venv -> ty -> venv -> ty -> Prop :=
| stp_refl: forall G1 G2 T,
   stp G1 T G2 T.

Hint Constructors val_type.
Hint Constructors wf_env.

Hint Unfold expand_env.

Lemma length_env_incr : forall (X : Type) n m env (x : X),
   n = m ->
   length_env n (expand_env env x m) = 1 + length_env n env.
Proof.
  intros. destruct env; destruct n; inversion H; auto.
Qed.

Lemma length_env_same : forall (X : Type) n m env (x : X),
   n <> m ->
   length_env n (expand_env env x m) = length_env n env.
Proof.
  intros. destruct env; destruct n; destruct m; try contradiction; auto.
Qed.

Hint Rewrite length_env_incr.
Hint Rewrite length_env_same.
Hint Unfold not.

Lemma wf_length : forall vs ts,
      wf_env vs ts ->
      length_env First vs = length_env First ts /\ length_env Second vs = length_env Second ts.
Proof.
  intros. induction H; split; auto.
  - destruct n.
    + rewrite length_env_incr. rewrite length_env_incr. destruct IHwf_env. auto. auto. auto.
    + rewrite length_env_same. rewrite length_env_same. destruct IHwf_env. auto.
      congruence. congruence.
  - destruct n.
    + rewrite length_env_same. rewrite length_env_same. destruct IHwf_env. auto.
      congruence. congruence.
    + rewrite length_env_incr. rewrite length_env_incr. destruct IHwf_env. auto.
      auto. auto.
Qed.

Hint Immediate wf_length.

Lemma wf_idx : forall vs ts,
      wf_env vs ts ->
      get_inv_idx vs = get_inv_idx ts.
Proof.
  intros. induction H.
  - auto.
  - destruct n; destruct vs; destruct ts; auto.
Qed.

Lemma valtp_extend : forall vs v v1 T n,
                       val_type vs v T ->
                       val_type (expand_env vs v1 n) v T.
Proof. intros. induction H; eauto. Qed.

Lemma index_extend : forall X vs n a (T: X),
                       index n vs = Some T ->
                       index n (a::vs) = Some T.
Proof.
  intros.
  assert (n < length vs). eapply index_max with T. auto.
  assert (n <> length vs). omega.
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff. auto.
  simpl. rewrite E. auto.
Qed.

Lemma lookup_extend : forall X vs x a (T: X) n,
                       lookup x vs = Some T ->
                       lookup x (expand_env vs a n) = Some T.
Proof.
  intros.
  assert (get_idx x < length_env (get_class x) vs). eapply lookup_max. eauto.
  assert (get_idx x <> length_env (get_class x) vs). omega.
  assert (beq_nat (get_idx x) (length_env (get_class x) vs) = false) as E. eapply beq_nat_false_iff; eauto.
  destruct vs.
  destruct n; destruct x; destruct c; simpl in E;
    inversion H; simpl; try rewrite E; auto.
Qed.

Lemma lookup_safe_ex: forall H1 G1 TF x,
             wf_env H1 G1 ->
             lookup x G1 = Some TF ->
             exists v, lookup x H1 = Some v /\ val_type H1 v TF.
Proof.
  intros. induction H.  
  Case "nil". inversion H0. destruct x; destruct c; destruct (ble_nat n i); inversion H1.
  Case "cons". destruct vs as [vl1 vl2 vidx]. destruct ts as [tl1 tl2 tidx].
    apply wf_length in H1. destruct H1 as [H1l H1r].
    destruct x; destruct c; inversion H0.
    SCase "VFst". destruct n; simpl in H0 ; simpl in H2.
      SSCase "First".
        case_eq (beq_nat i (length tl1)).
        SSSCase "hit".
          intros E.
          rewrite E in H0. inversion H0. subst t. simpl.
          assert (beq_nat i (length vl1) = true). eauto.
          rewrite H1. eauto.
        SSSCase "miss".
          intros E.
          assert (beq_nat i (length vl1) = false). eauto.
          assert (exists v0, lookup (V First i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type (Def vl vl1 vl2 vidx) v0 TF) as HI.
          eapply IHwf_env. simpl. rewrite E in H0. eauto.
          inversion HI as [v0 HI1]. inversion HI1.
          eexists. econstructor. eapply lookup_extend; eauto. eapply valtp_extend; eauto.
     SSCase "Second".
       assert (exists v0, lookup (V First i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type (Def vl vl1 vl2 vidx) v0 TF) as HI.
       eapply IHwf_env. simpl. eauto.
       inversion HI as [v0 HI1]. inversion HI1.
       eexists. econstructor. eapply lookup_extend; eauto. eapply valtp_extend; eauto.
   SCase "VSnd". destruct n; simpl in H0; simpl in H2.
     SSCase "First".
       assert (exists v0, lookup (V Second i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type (Def vl vl1 vl2 vidx) v0 TF) as HI.
       eapply IHwf_env. simpl. eauto.
       inversion HI as [v0 HI1]. inversion HI1.
       eexists. econstructor. eapply lookup_extend; eauto. eapply valtp_extend; eauto.
     SSCase "Second".
       case_eq (beq_nat i (length tl2)).
        SSSCase "hit".
          intro E.
          rewrite E in H0. simpl. destruct (ble_nat tidx i); inversion H0.
          subst t.
          assert (beq_nat i (length vl2) = true). eauto.
          rewrite H1. inversion H3. subst vidx. destruct (ble_nat tidx i); eauto. inversion H5.
        SSSCase "miss".
          intro E.
          assert (beq_nat i (length vl2) = false). eauto.
          assert (exists v0, lookup (V Second i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type (Def vl vl1 vl2 vidx) v0 TF) as HI.
          eapply IHwf_env. simpl. destruct (ble_nat tidx i). inversion H0. rewrite E in H0. rewrite H0. rewrite E. auto. auto.
          inversion HI as [v0 HI1]. inversion HI1.
          eexists. econstructor. eapply lookup_extend; eauto. eapply valtp_extend; eauto.
Qed.

Inductive res_type: venv -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T,
      val_type venv v T ->
      res_type venv (Some v) T.

Lemma valtp_widen: forall vf H1 H2 T1 T2,
  val_type H1 vf T1 ->
  stp H1 T1 H2 T2 ->
  val_type H2 vf T2.
Proof.
  intros. inversion H; inversion H0; subst T2; subst; eauto.
Qed.

Lemma invert_abs: forall venv vf vx T1 n T2,
  val_type venv vf (TFun T1 n T2) ->
  exists env tenv y T3 T4,
    vf = (vabs env n y) /\
    wf_env env tenv /\
    has_type (expand_env (expand_env tenv (TFun T3 n T4) Second) T3 n) y First T4 /\
    stp venv T1 (expand_env (expand_env env vf Second) vx n) T3 /\
    stp (expand_env (expand_env env vf Second) vx n) T4 venv T2.
Proof. 
  intros. inversion H. repeat eexists; repeat eauto.
Qed.

Lemma invert_absrec: forall venv vf vx T1 n T2,
  val_type venv vf (TFunRec T1 n T2) ->
  exists env tenv y T3 T4,
    vf = (vabsrec env n y) /\
    wf_env env tenv /\
    has_type (expand_env (expand_env tenv (TFunRec T3 n T4) Second) T3 n) y First T4 /\
    stp venv T1 (expand_env (expand_env env vf Second) vx n) T3 /\
    stp (expand_env (expand_env env vf Second) vx n) T4 venv T2.
Proof. 
  intros. inversion H. repeat eexists; repeat eauto.
Qed.

Lemma ext_sanitize_commute : forall {T} n venv (v:T) c,
   expand_env (sanitize_any venv n) v c = sanitize_any (expand_env venv v c) n.
Proof.
  intros. destruct venv. destruct c; simpl; eauto. 
Qed.

Lemma val_type_sanitize_any : forall n venv res T,
  val_type venv res T ->
  val_type (sanitize_any venv n) res T.
Proof.
  intros. inversion H; eauto.
Qed.

Lemma val_type_sanitize : forall env res T n,
  val_type (sanitize_env n env) res T ->
  val_type env res T.
Proof.
  intros. inversion H; eauto.
Qed.

Lemma wf_sanitize_any : forall n venv tenv,
   wf_env venv tenv ->
   wf_env (sanitize_any venv n) (sanitize_any tenv n).
Proof.
  intros. induction H.
  - simpl. eapply wfe_nil.
  - eapply wfe_cons in IHwf_env.
    + rewrite <-ext_sanitize_commute. rewrite <-ext_sanitize_commute.
      eauto.
    + rewrite ext_sanitize_commute. eapply val_type_sanitize_any in H. eauto.
    + eapply wf_idx. eauto.
Qed.

Lemma wf_sanitize : forall n venv tenv,
   wf_env venv tenv ->
   wf_env (sanitize_env n venv) (sanitize_env n tenv).
Proof.
  intros. destruct n; unfold sanitize_env. destruct venv. destruct tenv.
  assert (length l0 = length l2). apply wf_length in H; destruct H as [L R]; eauto.
  rewrite H0. eapply wf_sanitize_any. eauto.
  eauto.
Qed.
  

Hint Immediate wf_sanitize.
   

Lemma abs_absrec : forall m n env y T1 T2,
  has_type (expand_env (expand_env (sanitize_env n env) (TFunRec T1 m T2) Second) T1 m) y First T2 ->
  has_type (expand_env (expand_env (sanitize_env n env) (TFun T1 m T2) Second) T1 m) y First T2.
Proof.
  intros. destruct y; inversion H; eauto. Admitted.

(* if result of STLC 1/2 evaluation is not a timeout, then *)
(* it is not stuck, and well-typed *)

Theorem full_safety : forall k e n tenv venv res T,
  teval k venv e n = Some res -> has_type tenv e n T -> wf_env venv tenv ->
  res_type venv res T.

Proof.
intros k. induction k.
  (* 0 *)   intros. inversion H.
  (* S n *) intros. destruct e; inversion H; inversion H0. 
  
  - Case "True".  eapply not_stuck. eapply v_bool.
  - Case "False". eapply not_stuck. eapply v_bool.

  - Case "Var".
    subst.
    destruct (lookup_safe_ex (sanitize_env n venv) (sanitize_env n tenv) T v) as [va [I V]]; eauto. 

    rewrite I. eapply not_stuck. eapply val_type_sanitize. eapply V.

  - Case "App".
    remember (teval k venv e1 Second) as tf.
    subst T. subst n0.
    
    destruct tf as [rf|] ; try solve by inversion.
    assert (res_type venv rf (TFun T1 m T2)) as HRF. SCase "HRF". subst. eapply IHk; eauto.
    inversion HRF as [? vf].

    subst rf. remember vf as rvf. destruct vf; try (subst rvf; solve by inversion).
    assert (c = m). destruct m; destruct c; try (subst rvf ; solve by inversion); eauto. subst c. subst rvf.
    remember (teval k venv e2 m) as tx.

    destruct tx as [rx|]; try solve by inversion.
    assert (res_type venv rx T1) as HRX. SCase "HRX". subst. eapply IHk; eauto.
    inversion HRX as [? vx]. 

    destruct (invert_abs venv (vabs e m t) vx T1 m T2) as
        [env1 [tenv1 [y0 [T3 [T4 [EF [WF [HTY [STX STY]]]]]]]]]. eauto.
    (* now we know it's a closure, and we have has_type evidence *)

    inversion EF. subst e. subst y0. clear EF.
    subst rx.

    assert (res_type (expand_env (expand_env env1 (vabs env1 m t) Second) vx m) res T4) as HRY.
        SSSCase "HRY".
          subst. eapply IHk; eauto.
        (* wf_env f x *) econstructor. eapply valtp_widen; eauto.
        (* wf_env f   *) econstructor. eapply v_abs; eauto.
          eauto.
          apply wf_idx. assumption.
          apply wf_idx. econstructor. eauto. assumption. apply wf_idx. assumption.

    inversion HRY as [? vy].

    eapply not_stuck. eapply valtp_widen; eauto.

  - Case "AppRec".
    (* e2 *)
    remember (teval k venv e2 Second) as tr.
    subst T. subst n0.
    destruct tr as [rr|]; try solve by inversion.
    assert (res_type venv rr TRec) as HRR. SCase "HRR". subst. eapply IHk; eauto.
    inversion HRR as [? vr].

    subst rr. remember vr as rvr.
    destruct vr; try (subst rvr; solve by inversion).
    subst rvr. 
    
    (* e1 *)
    remember (teval k venv e1 Second) as tf.
    subst T. 
    
    destruct tf as [rf|] ; try solve by inversion.
    assert (res_type venv rf (TFunRec T1 m T2)) as HRF. SCase "HRF". subst. eapply IHk; eauto.
    inversion HRF as [? vf].

    subst rf. remember vf as rvf. destruct vf; try (subst rvf; solve by inversion).
    assert (c = m). destruct m; destruct c; try (subst rvf ; solve by inversion); eauto. subst c. subst rvf.

    (* e3 *)
    remember (teval k venv e3 m) as tx.

    destruct tx as [rx|]; try solve by inversion.
    assert (res_type venv rx T1) as HRX. SCase "HRX". subst. eapply IHk; eauto.
    inversion HRX as [? vx]. 

    destruct (invert_absrec venv (vabsrec e m t) vx T1 m T2) as
        [env1 [tenv1 [y0 [T3 [T4 [EF [WF [HTY [STX STY]]]]]]]]]. eauto.
    (* now we know it's a closure, and we have has_type evidence *)

    inversion EF. subst e. subst y0. clear EF.
    subst rx.

    assert (res_type (expand_env (expand_env env1 (vabsrec env1 m t) Second) vx m) res T4) as HRY.
        SSSCase "HRY".
          subst. eapply IHk; eauto.
        (* wf_env f x *) econstructor. eapply valtp_widen; eauto.
        (* wf_env f   *) econstructor. eapply v_absrec; eauto.
          eauto.
          apply wf_idx. assumption.
          apply wf_idx. econstructor. eauto. assumption. apply wf_idx. assumption.

    inversion HRY as [? vy].

    eapply not_stuck. eapply valtp_widen; eauto.
    
  - Case "Abs". intros. inversion H. inversion H0.
    eapply not_stuck. eapply v_abs. eapply wf_sanitize. eauto.
    apply abs_absrec in H15. subst. rewrite H14 in H15. inversion H14. subst.
    eauto.
Qed.
(* From nano-total: *)

(* Lemma wf_length : forall vs ts, *)
(*                     wf_env vs ts -> *)
(*                     (length vs = length ts). *)
(* Proof. *)
(*   intros. induction H. auto. *)
(*   assert ((length (v::vs)) = 1 + length vs). constructor. *)
(*   assert ((length (t::ts)) = 1 + length ts). constructor. *)
(*   rewrite IHwf_env in H1. auto. *)
(* Qed. *)

(* Hint Immediate wf_length. *)

(* Lemma index_max : forall X vs n (T: X), *)
(*                        index n vs = Some T -> *)
(*                        n < length vs. *)
(* Proof. *)
(*   intros X vs. induction vs. *)
(*   Case "nil". intros. inversion H. *)
(*   Case "cons". *)
(*   intros. inversion H.  *)
(*   case_eq (beq_nat n (length vs)); intros E. *)
(*   SCase "hit". *)
(*   rewrite E in H1. inversion H1. subst. *)
(*   eapply beq_nat_true in E.  *)
(*   unfold length. unfold length in E. rewrite E. eauto. *)
(*   SCase "miss". *)
(*   rewrite E in H1. *)
(*   assert (n < length vs). eapply IHvs. apply H1. *)
(*   compute. eauto. *)
(* Qed. *)


(* Lemma index_extend : forall X vs n a (T: X), *)
(*                        index n vs = Some T -> *)
(*                        index n (a::vs) = Some T. *)

(* Proof. *)
(*   intros. *)
(*   assert (n < length vs). eapply index_max. eauto. *)
(*   assert (n <> length vs). omega. *)
(*   assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff; eauto. *)
(*   unfold index. unfold index in H. rewrite H. rewrite E. reflexivity. *)
(* Qed. *)


(* Lemma index_safe_ex: forall H1 G1 TF i, *)
(*              wf_env H1 G1 -> *)
(*              index i G1 = Some TF -> *)
(*              exists v, index i H1 = Some v /\ val_type v TF. *)
(* Proof. intros. induction H. *)
(*        Case "nil". inversion H0. *)
(*        Case "cons". inversion H0. *)
(*          case_eq (beq_nat i (length ts)). *)
(*            SCase "hit". *)
(*              intros E. *)
(*              rewrite E in H3. inversion H3. subst t. *)
(*              assert (beq_nat i (length vs) = true). eauto. *)
(*              assert (index i (v :: vs) = Some v). eauto.  unfold index. rewrite H2. eauto. *)
(*              eauto. *)
(*            SCase "miss". *)
(*              intros E. *)
(*              assert (beq_nat i (length vs) = false). eauto. *)
(*              rewrite E in H3. *)
(*              assert (exists v0, index i vs = Some v0 /\ val_type v0 TF) as HI. eapply IHwf_env. eauto. *)
(*            inversion HI as [v0 HI1]. inversion HI1.  *)
(*            eexists. econstructor. eapply index_extend; eauto.  eauto. *)
(* Qed. *)

  
(* Lemma invert_abs: forall vf T1 T2, *)
(*   val_type vf (TFun T1 T2) -> *)
(*   exists env y, *)
(*     vf = (vabs env y) /\  *)
(*     (forall vx, val_type vx T1 -> *)
(*        exists v, tevaln (vx::env) y v /\ val_type v T2). *)
(* Proof. *)
(*   intros. simpl in H. destruct vf. inversion H. eauto.  *)
(* Qed. *)

(* if not a timeout, then result not stuck and well-typed *)

(* Theorem full_safety : forall n e tenv venv res T, *)
(*   teval n venv e = Some res -> has_type tenv e T -> wf_env venv tenv -> *)
(*   exists v, res = Some v /\ val_type v T. *)

(* Proof. *)
(*   intros n. induction n. *)
(*   (* 0   *) intros. inversion H. *)
(*   (* S n *) intros. destruct e; inversion H; inversion H0. *)

(*   Case "True".  eexists. split. eauto. simpl. eauto. *)
(*   Case "False". eexists. split. eauto. simpl. eauto. *)

(*   Case "Var". *)
(*     destruct (index_safe_ex venv0 tenv0 T i) as [v IV]. eauto. eauto. *)
(*     inversion IV as [I V]. *)

(*     rewrite I. eexists. split. eauto. eapply V. *)

(*   Case "App". *)
(*     remember (teval n venv0 e1) as tf. (* not stuck *) *)
(*     remember (teval n venv0 e2) as tx.  *)
(*     subst T. *)

(*     destruct tf as [rf|]; destruct tx as [rx|]; try solve by inversion. *)

(*     (* eval f is not stuck and well-typed *) *)
(*     assert (exists vf, rf = Some vf /\ val_type vf (TFun T1 T2)) as HRF. subst. eapply IHn; eauto. *)


(*     (* eval x is not stuck and well-typed *) *)
(*     assert (exists vx, rx = Some vx /\ val_type vx T1) as HRX. subst. eapply IHn; eauto. *)

(*     (* body *) *)
(*     inversion HRF as [vf [EF HVF]].  *)
(*     inversion HRX as [vx [EX HVX]]. subst. eapply invert_abs in HVF. *)
(*     destruct HVF as [venv1 [y [HF IHF]]]. destruct (IHF vx). eauto. inversion H2. *)

(*     (* first attempt *) *)
(*     eapply IHn. *)

(*     (* not stuck *) *)
(*     simpl in H. subst. eauto. *)
(*     (* well-typed *) *)
(*     admit. *)
(*     (* well-formed env *) *)
(*     admit.  *)

(*     (* first attempt ends*) *)

(*     (* second attempt *) *)
(*     (* will need "tevaln (vx::venv1) y v -> teval n (vx::venv1) y v" *) *)

(*     (*    inversion HVF. (* now we know it's a closure, and we have has_type evidence *)  *) *)

(*     (* other case: tx = None *) *)
(*     assert (exists vf, rf = Some vf /\ val_type vf (TFun T1 T2)) as HRF. subst. eapply IHn; eauto. *)

(*     inversion HRF as [vf [EF HVF]]. subst. *)
(*     (* TODO: HVF is not inductive here *) *)
(*     destruct HVF. subst. inversion H3. (* contradiction *) *)


(*   Case "Abs". *)
(*     eexists. split. eauto. eapply v_abs; eauto. *)
(* Qed. *)

(* (* if well-typed, then result is an actual value (not stuck and not a timeout), *)
(*    for large enough n *) *)

(* Theorem full_total_safety : forall e tenv T, *)
(*   has_type tenv e T -> forall venv, wf_env venv tenv -> *)
(*   exists v, tevaln venv e v /\ val_type v T. *)

(* Proof. *)
(*   intros ? ? ? W. *)
(*   induction W; intros ? WFE. *)
  
(*   - Case "True". eexists. split. *)
(*     exists 0. intros. destruct n. omega. simpl. eauto. simpl. eauto.  *)
(*   - Case "False". eexists. split. *)
(*     exists 0. intros. destruct n. omega. simpl. eauto. simpl. eauto.  *)

(*   - Case "Var".  *)
(*     destruct (index_safe_ex venv0 env T1 x) as [v IV]. eauto. eauto.  *)
(*     inversion IV as [I V].  *)

(*     exists v. split. exists 0. intros. destruct n. simpl. omega. simpl. rewrite I. eauto. eapply V. *)

(*   - Case "App". *)
(*     destruct (IHW1 venv0 WFE) as [vf [IW1 HVF]]. *)
(*     destruct (IHW2 venv0 WFE) as [vx [IW2 HVX]]. *)
    
(*     eapply invert_abs in HVF. *)
(*     destruct HVF as [venv1 [y [HF IHF]]]. *)

(*     destruct (IHF vx HVX) as [vy [IW3 HVY]]. *)

(*     exists vy. split. { *)
(*       (* pick large enough n. nf+nx+ny will do. *) *)
(*       destruct IW1 as [nf IWF]. *)
(*       destruct IW2 as [nx IWX]. *)
(*       destruct IW3 as [ny IWY]. *)
(*       exists (S (nf+nx+ny)). intros. destruct n. omega. simpl. *)
(*       rewrite IWF. subst vf. rewrite IWX. rewrite IWY. eauto. *)
(*       omega. omega. omega. *)
(*     }  *)
(*     eapply HVY. *)
    
(*   - Case "Abs". *)
(*     eexists. split. exists 0. intros. destruct n. omega. simpl. eauto. simpl. *)
(*     intros. eapply IHW. eapply wfe_cons; eauto. *)
(* Qed. *)

(* Theorem  *)
