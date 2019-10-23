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
| tvar : var -> tm
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
     // rec cap has to be present here.
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
    lookup x (sanitize_env n env) = Some T1 ->
    has_type env (tvar x) n T1
| t_app: forall m n env f x T1 T2,
    has_type env f Second (TFun T1 m T2) ->
    has_type env x m T1 ->
    has_type env (tapp f x) n T2
| t_apprec: forall m n env f r x T1 T2,
    (* Second-class recursion cap variable is in env *)
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
    | tvar x     => Some (lookup x (sanitize_env n env))
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

(* evaluation on term e is terminating *)
Definition tevaln env e c v := exists nm, forall n, n > nm -> teval n env c e = Some (Some v).


(* need to use Fixpoint because of positivity restriction *)
(* From nano-total. val_type Definition based on operational semantics *)
(*
Fixpoint val_type (v:vl) (T:ty): Prop := match v, T with
| vbool b, TBool => True
| vrec, TRec => True
| vabs env Second y, TFun T1 m T2 =>
  (forall vx, val_type vx T1 ->
              exists v, tevaln (expand_env (expand_env env v Second) vx m) Second y v /\ val_type v T2)
(*     exists v, tevaln (vx::(vabs env y)::env) y v /\ val_type v T2)   *)
| vabsrec env Second y, TFunRec T1 m T2 =>
  (forall vx, val_type vx T1 ->
              exists v, tevaln (expand_env (expand_env (expand_env env v Second) vx m) vrec Second) y v /\ val_type v T2)
| _,_ => False
end.


Inductive wf_env : venv -> tenv -> Prop := 
| wfe_nil : wf_env nil nil
| wfe_cons : forall v t vs ts,
    val_type v t ->
    wf_env vs ts ->
    wf_env (cons v vs) (cons t ts)
.

 *)

(* ### Value typing and well-typed runtime environments ### *)

Definition get_inv_idx {X : Type} (env : env X) :=
  match env with
  | Def _ l1 l2 idx => idx
  end
.

(* ### Variable binding helpers ### *)

Definition length_env {X : Type} (c : class) (env : env X): nat :=
match env, c with
| Def _ l1 l2 n, First => length l1
| Def _ l1 l2 n, Second => length l2
end
.

Definition get_class (x : var): class :=
match x with
| V c _ => c
end
.

Definition get_idx (x : var): nat :=
match x with
| V _ n => n
end
.

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

Hint Immediate index_max.

Lemma lookup_max : forall X vs x (T: X),
                       lookup x vs = Some T ->
                       get_idx x < length_env (get_class x) vs.
Proof.
  intros X vs; destruct vs as [l1 l2 n].
  intros x T H.
  destruct x. destruct c; simpl.
  Case "VFst". inversion H; eauto.
  Case "VSnd". inversion H.
    destruct (ble_nat n i); inversion H1; eauto.
Qed.
