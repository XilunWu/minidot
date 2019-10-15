(* Full safety for STLC *)

(* copied from nano0.v *)

(* This version prohibits recursion, and we prove that   *)
(* evaluation always terminates with a well-typed value. *)
(* From this follows both type soundness and strong      *)
(* normalization for STLC.                               *)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.
Require Export Omega.

Module STLC.

Definition id := nat.

(* cap: using DeBrujin levels *)
Inductive cap : Type :=
  | canRec : id -> cap
.

Inductive ty : Type :=
  | TBool   : ty
  | TFun1   : ty -> ty -> ty
  | TFun2   : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs1 : tm -> tm (* \f x.y *)
  (* list of capabilities required by the abstration to apply *)                    
  | tabs2 : list cap -> tm -> tm (* rec \f x.y *)
.

Inductive vl : Type :=
| vbool : bool -> vl
| vabs1 : list vl -> tm -> vl
(* list of capabilities in the environment *)
| vabs2 : list cap -> list vl -> tm -> vl
.

Definition venv := list vl.
Definition tenv := list ty.
Definition cenv := ((list cap) * nat) % type.

Hint Unfold venv.
Hint Unfold tenv.
Hint Unfold cenv.

Fixpoint length {X: Type} (l : list X): nat :=
  match l with
    | [] => 0
    | _::l' => 1 + length l'
  end.

Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.

Definition lookup (n : id) (env: cenv) : option cap :=
  match env with
    (* if idx the level is less than or equal to the depth n, the variable n is free *)
    | (l, idx) => if ble_nat idx n then index n l else None
  end
.


Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
           has_type env ttrue TBool
| t_false: forall env,
           has_type env tfalse TBool
| t_var: forall x env T1,
           index x env = Some T1 ->
           has_type env (tvar x) T1
| t_app1: forall env f x T1 T2,
           has_type env f (TFun1 T1 T2) ->
           has_type env x T1 ->
           has_type env (tapp f x) T2
| t_app2: forall env f x T1 T2,
           has_type env f (TFun2 T1 T2) ->
           has_type env x T1 ->
           has_type env (tapp f x) T2
(* Add function type to the tenv of body *)
| t_abs_term: forall env y T1 T2,
           has_type (T1::env) y T2 ->
           has_type env (tabs1 y) (TFun1 T1 T2)
| t_abs_nonterm: forall env n y T1 T2 capenv idx,
           lookup n capenv = Some (canRec idx) -> 
           has_type (T1::(TFun2 T1 T2)::env) y T2 -> 
           has_type env (tabs2 n y) (TFun2 T1 T2)
.

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
*)

Fixpoint teval(n: nat)(env: venv)(capenv: cenv)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | ttrue      => Some (Some (vbool true))
        | tfalse     => Some (Some (vbool false))
        | tvar x     => Some (index x env)
        | tabs1 y    => Some (Some (vabs env y))
        | tabs2 n y  => 
        | tapp ef ex   =>
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some (vabs env2 ey)) =>
              match teval n env ex with
                | None => None
                | Some None => Some None
                | Some (Some vx) =>
(* f value is not in the venv of body so no recursive calls *)                  
                  teval n (vx::env2) ey
              end
          end
      end
  end.


Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).


(* need to use Fixpoint because of positivity restriction *)
Fixpoint val_type (v:vl) (T:ty): Prop := match v, T with
| vbool b, TBool => True
| vabs env y, TFun T1 T2 =>
  (forall vx, val_type vx T1 ->
              exists v, tevaln (vx::env) y v /\ val_type v T2)
(*     exists v, tevaln (vx::(vabs env y)::env) y v /\ val_type v T2)   *)
| _,_ => False
end.


Inductive wf_env : venv -> tenv -> Prop := 
| wfe_nil : wf_env nil nil
| wfe_cons : forall v t vs ts,
    val_type v t ->
    wf_env vs ts ->
    wf_env (cons v vs) (cons t ts)
.


Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.
(* Hint Constructors val_type. *)
Hint Constructors wf_env.

Hint Constructors option.
Hint Constructors list.

Hint Unfold index.
Hint Unfold length.

Hint Resolve ex_intro.

Lemma wf_length : forall vs ts,
                    wf_env vs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
  assert ((length (v::vs)) = 1 + length vs). constructor.
  assert ((length (t::ts)) = 1 + length ts). constructor.
  rewrite IHwf_env in H1. auto.
Qed.

Hint Immediate wf_length.

Lemma index_max : forall X vs n (T: X),
                       index n vs = Some T ->
                       n < length vs.
Proof.
  intros X vs. induction vs.
  Case "nil". intros. inversion H.
  Case "cons".
  intros. inversion H. 
  case_eq (beq_nat n (length vs)); intros E.
  SCase "hit".
  rewrite E in H1. inversion H1. subst.
  eapply beq_nat_true in E. 
  unfold length. unfold length in E. rewrite E. eauto.
  SCase "miss".
  rewrite E in H1.
  assert (n < length vs). eapply IHvs. apply H1.
  compute. eauto.
Qed.


Lemma index_extend : forall X vs n a (T: X),
                       index n vs = Some T ->
                       index n (a::vs) = Some T.

Proof.
  intros.
  assert (n < length vs). eapply index_max. eauto.
  assert (n <> length vs). omega.
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff; eauto.
  unfold index. unfold index in H. rewrite H. rewrite E. reflexivity.
Qed.


Lemma index_safe_ex: forall H1 G1 TF i,
             wf_env H1 G1 ->
             index i G1 = Some TF ->
             exists v, index i H1 = Some v /\ val_type v TF.
Proof. intros. induction H.
       Case "nil". inversion H0.
       Case "cons". inversion H0.
         case_eq (beq_nat i (length ts)).
           SCase "hit".
             intros E.
             rewrite E in H3. inversion H3. subst t.
             assert (beq_nat i (length vs) = true). eauto.
             assert (index i (v :: vs) = Some v). eauto.  unfold index. rewrite H2. eauto.
             eauto.
           SCase "miss".
             intros E.
             assert (beq_nat i (length vs) = false). eauto.
             rewrite E in H3.
             assert (exists v0, index i vs = Some v0 /\ val_type v0 TF) as HI. eapply IHwf_env. eauto.
           inversion HI as [v0 HI1]. inversion HI1. 
           eexists. econstructor. eapply index_extend; eauto.  eauto.
Qed.

  
Lemma invert_abs: forall vf T1 T2,
  val_type vf (TFun T1 T2) ->
  exists env y,
    vf = (vabs env y) /\ 
    (forall vx, val_type vx T1 ->
       exists v, tevaln (vx::env) y v /\ val_type v T2).
Proof.
  intros. simpl in H. destruct vf. inversion H. eauto. 
Qed.

(* if not a timeout, then result not stuck and well-typed *)

Theorem full_safety : forall n e tenv venv res T,
  teval n venv e = Some res -> has_type tenv e T -> wf_env venv tenv ->
  exists v, res = Some v /\ val_type v T.

Proof.
  intros n. induction n.
  (* 0   *) intros. inversion H.
  (* S n *) intros. destruct e; inversion H; inversion H0.

  Case "True".  eexists. split. eauto. simpl. eauto.
  Case "False". eexists. split. eauto. simpl. eauto.

  Case "Var".
    destruct (index_safe_ex venv0 tenv0 T i) as [v IV]. eauto. eauto.
    inversion IV as [I V].

    rewrite I. eexists. split. eauto. eapply V.

  Case "App".
    remember (teval n venv0 e1) as tf. (* not stuck *)
    remember (teval n venv0 e2) as tx. 
    subst T.

    destruct tf as [rf|]; destruct tx as [rx|]; try solve by inversion.

    (* eval f is not stuck and well-typed *)
    assert (exists vf, rf = Some vf /\ val_type vf (TFun T1 T2)) as HRF. subst. eapply IHn; eauto.


    (* eval x is not stuck and well-typed *)
    assert (exists vx, rx = Some vx /\ val_type vx T1) as HRX. subst. eapply IHn; eauto.

    (* body *)
    inversion HRF as [vf [EF HVF]]. 
    inversion HRX as [vx [EX HVX]]. subst. eapply invert_abs in HVF.
    destruct HVF as [venv1 [y [HF IHF]]]. destruct (IHF vx). eauto. inversion H2.

    (* first attempt *)
    eapply IHn.

    (* not stuck *)
    simpl in H. subst. eauto.
    (* well-typed *)
    admit.
    (* well-formed env *)
    admit. 

    (* first attempt ends*)

    (* second attempt *)
    (* will need "tevaln (vx::venv1) y v -> teval n (vx::venv1) y v" *)

    (*    inversion HVF. (* now we know it's a closure, and we have has_type evidence *)  *)

    (* other case: tx = None *)
    assert (exists vf, rf = Some vf /\ val_type vf (TFun T1 T2)) as HRF. subst. eapply IHn; eauto.

    inversion HRF as [vf [EF HVF]]. subst.
    (* TODO: HVF is not inductive here *)
    destruct HVF. subst. inversion H3. (* contradiction *)


  Case "Abs".
    eexists. split. eauto. eapply v_abs; eauto.
Qed.

(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall e tenv T,
  has_type tenv e T -> forall venv, wf_env venv tenv ->
  exists v, tevaln venv e v /\ val_type v T.

Proof.
  intros ? ? ? W.
  induction W; intros ? WFE.
  
  - Case "True". eexists. split.
    exists 0. intros. destruct n. omega. simpl. eauto. simpl. eauto. 
  - Case "False". eexists. split.
    exists 0. intros. destruct n. omega. simpl. eauto. simpl. eauto. 

  - Case "Var". 
    destruct (index_safe_ex venv0 env T1 x) as [v IV]. eauto. eauto. 
    inversion IV as [I V]. 

    exists v. split. exists 0. intros. destruct n. simpl. omega. simpl. rewrite I. eauto. eapply V.

  - Case "App".
    destruct (IHW1 venv0 WFE) as [vf [IW1 HVF]].
    destruct (IHW2 venv0 WFE) as [vx [IW2 HVX]].
    
    eapply invert_abs in HVF.
    destruct HVF as [venv1 [y [HF IHF]]].

    destruct (IHF vx HVX) as [vy [IW3 HVY]].

    exists vy. split. {
      (* pick large enough n. nf+nx+ny will do. *)
      destruct IW1 as [nf IWF].
      destruct IW2 as [nx IWX].
      destruct IW3 as [ny IWY].
      exists (S (nf+nx+ny)). intros. destruct n. omega. simpl.
      rewrite IWF. subst vf. rewrite IWX. rewrite IWY. eauto.
      omega. omega. omega.
    } 
    eapply HVY.
    
  - Case "Abs".
    eexists. split. exists 0. intros. destruct n. omega. simpl. eauto. simpl.
    intros. eapply IHW. eapply wfe_cons; eauto.
Qed.

Theorem 

End STLC.