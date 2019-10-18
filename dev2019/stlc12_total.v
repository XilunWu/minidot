(* Full safety for STLC *)

(* copied from nano0.v *)

(* This version prohibits recursion, and we prove that   *)
(* evaluation always terminates with a well-typed value. *)
(* From this follows both type soundness and strong      *)
(* normalization for STLC.                               *)

(* Introduce the STLC1/2 style *)
Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.
Require Export Omega.

Module STLC.

  Definition id := nat.

  Inductive class : Type :=
  | First  : class
  | Second : class
  .

  (* types *)
  Inductive ty : Type :=
  | TBool  : ty
  | TRec   : ty (* the capability for recursion *)
  | TFun   : ty -> class -> ty -> ty
  (* \f x.y; Rec fun has type (TFunRec T1 T2) *)                                    
  | TFunRec: ty -> class -> ty -> ty
  .

  (* variables: 1st or 2nd class, using DeBrujin levels *)
  Inductive var : Type :=
  | V : class -> id -> var
  .

  Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tapp : tm -> tm -> tm (* f(x) *)
  | tapprec : tm -> tm -> tm -> tm (* f(rcap)(x) *)
  | tabs : class -> tm -> tm (* \f x.y *)
  .

  (* environments, split according to 1st/2nd class *)
  Inductive env (X: Type) :=
  | Def : list X -> list X -> nat -> env X.

  Inductive vl : Type :=
  | vbool : bool -> vl
  | vrec : vl
  | vabs : env vl -> class -> tm -> vl
  | vabsrec : env vl -> class -> tm -> vl
  .

  (* For functions, itself is always passed as an implicit arugment *)
  (* Recursive function example:
     // f: T => U
     def f(x: T): U = {
       // f: TRec => (T=>U)
       f(cap)(x-1)  // tapprec f r x
     }

     f(10) // tapp f 10
   *)
  Definition venv := env vl.  (* value environments *)
  Definition tenv := env ty.  (* type environments  *)

  Hint Unfold venv.
  Hint Unfold tenv.

  (* environment lookup *)
  Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
    match l with
    | [] => None
    | a :: l'  => if beq_nat n (length l') then Some a else index n l'
    end.

  Definition lookup {X : Type} (n : var) (l : env X) : option X :=
    match l with
    | Def _ l1 l2 m =>
      match n with
      | V First idx  => index idx l1
      | V Second idx => if ble_nat m idx then index idx l2 else None
      end
    end
  .

  (* restrict visible bindings in environment *)
  Definition sanitize_any {X : Type} (l : env X) (n:nat): env X :=
    match l with
    | Def _ l1 l2 _ => Def X l1 l2 n
    end.

  Definition sanitize_env {X : Type} (c : class) (l : env X) : env X :=
    match c,l  with
    | First, Def _ _ l2 _ => sanitize_any l (length l2)
    | Second, _ => l
    end.

  (* add new binding to environment *)
  Definition expand_env {X : Type} (l : env X) (x : X) (c : class) : (env X) :=
    match l with
    | Def _ l1 l2 m =>
      match c with
      | First => Def X (x::l1) l2 m
      | Second => Def X l1 (x::l2) m
      end
    end
  .

  Inductive has_type : tenv -> tm -> class -> ty -> Prop :=
  | t_true: forall env n,
      has_type env ttrue n TBool
  | t_false: forall env n,
      has_type env tfalse n TBool
  | t_var: forall x env n T1,
      lookup (V n x) (sanitize_env n env) = Some T1 ->
      has_type env (tvar x) n T1
  | t_app: forall m n env f x T1 T2,
      has_type env f Second (TFun T1 m T2) ->
      has_type env x m T1 ->
      has_type env (tapp f x) n T2
  | t_apprec: forall m n env f r x T1 T2,
      (* Second-class recursion cap is in env *)
      has_type env r Second TRec ->
      (* Any-class argument x *)
      has_type env x m T1 ->
      (* Secon-class recursive function f *)
      has_type env f Second (TFunRec T1 m T2) ->
      has_type env (tapprec f r x) n T2
  (* General induction principle for recursive and non-recursive function *)
  | t_abs: forall m n env y T1 T2,
      has_type (expand_env (expand_env (sanitize_env n env) (TFunRec T1 m T2) Second) T1 m) y First T2 ->
      has_type env (tabs m y) n (TFun T1 m T2)
  .

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
 *)

Fixpoint teval(k: nat)(env: venv)(t: tm)(n: class){struct k}: option (option vl) :=
  match k with
    | 0 => None
    | S k' =>
      match t with
        | ttrue      => Some (Some (vbool true))
        | tfalse     => Some (Some (vbool false))
        | tvar x     => Some (lookup (V n x) (sanitize_env n env))
        | tabs m y   => Some (Some (vabs (sanitize_env n env) m y))
        | tapp ef ex   =>
           match teval k' env ef Second with
             | None => None
             | Some None => Some None
             | Some (Some (vbool _)) => Some None
             | Some (Some vrec) => Some None
             | Some (Some (vabsrec _ _ _)) => Some None
             | Some (Some (vabs env2 m ey)) =>
                match teval k' env ex m with
                  | None => None
                  | Some None => Some None
                  | Some (Some vx) =>
                       teval k' (expand_env (expand_env env2 (vabs env2 m ey) Second) vx m) ey First
                end
           end
        | tapprec ef er ex =>
          match teval k' env er Second with
          | None => None
          | Some None => Some None
          | Some (Some (vbool _)) => Some None
          | Some (Some (vabsrec _ _ _)) => Some None
          | Some (Some (vabs _ _ _)) => Some None
          | Some (Some vrec) =>
            match teval k' env ef Second with
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some vrec) => Some None
            | Some (Some (vabs env2 m ey)) =>
              match teval k' env ex m with
              | None => None
              | Some None => Some None
              | Some (Some vx) =>
                teval k' (expand_env (expand_env env2 (vabsrec env2 m ey) Second) vx m) ey First
              end
            | Some (Some (vabsrec env2 m ey)) =>
              match teval k' env ex m with
              | None => None
              | Some None => Some None
              | Some (Some vx) =>
                teval k' (expand_env (expand_env env2 (vabsrec env2 m ey) Second) vx m) ey First
              end
            end
          end
      end      
  end.
(*
Fixpoint teval(n: nat)(env: venv)(capenv: cenv)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | ttrue      => Some (Some (vbool true))
        | tfalse     => Some (Some (vbool false))
        | tvar x     => Some (index x env)
        | tabs y    => Some (Some (vabs env y))
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
*)

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