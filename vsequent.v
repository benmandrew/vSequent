Require Import Bool.
Require Import FunInd.

Inductive ctx : Set :=
  | ctx_nil : ctx
  | ctx_cons : (nat * bool) -> ctx -> ctx.

Fixpoint ctx_v (n : nat) (c : ctx) {struct c} : option bool :=
  match c with
  | ctx_nil => None
  | ctx_cons (n', v) c => if Nat.eqb n n' then Some v else ctx_v n c
  end.

Inductive prop : Set :=
  | p_sym : nat -> prop
  | p_neg : prop -> prop
  | p_and : prop -> prop -> prop
  | p_or : prop -> prop -> prop
  | p_impl : prop -> prop -> prop.

Function prop_val (c : ctx) (p : prop) {struct p} : option bool :=
  match p with
  | p_sym n => ctx_v n c
  | p_neg p =>
      match prop_val c p with
      | None => None
      | Some b => Some (negb b)
      end
  | p_and p1 p2 =>
      match prop_val c p1 with
      | None => None
      | Some b1 =>
          match prop_val c p2 with
          | None => None
          | Some b2 => Some (andb b1 b2)
          end
      end
  | p_or p1 p2 =>
      match prop_val c p1 with
      | None => None
      | Some b1 =>
          match prop_val c p2 with
          | None => None
          | Some b2 => Some (orb b1 b2)
          end
      end
  | p_impl p1 p2 =>
      match prop_val c p1 with
      | None => None
      | Some b1 =>
          match prop_val c p2 with
          | None => None
          | Some b2 => Some (implb b1 b2)
          end
      end
  end.

Lemma prop_val_neg_b : forall c p b,
  prop_val c p = Some b -> prop_val c (p_neg p) = Some (negb b).
Proof.
  intros c p b H.
  rewrite prop_val_equation. rewrite H. reflexivity.
Qed.

Lemma prop_val_neg_n : forall c p,
  prop_val c p = None -> prop_val c (p_neg p) = None.
Proof.
  intros c p H.
  rewrite prop_val_equation. rewrite H. reflexivity.
Qed.

Lemma prop_val_or_b : forall c p0 p1 b0 b1,
  prop_val c p0 = Some b0 -> prop_val c p1 = Some b1 ->
  prop_val c (p_or p0 p1) = Some (orb b0 b1).
Proof.
  intros c p0 p1 b0 b1 Hprop0 Hprop1.
  rewrite prop_val_equation. rewrite Hprop0. rewrite Hprop1. reflexivity.
Qed.

Lemma prop_val_or_n_l : forall c p0 p1,
  prop_val c p0 = None -> prop_val c (p_or p0 p1) = None.
Proof.
  intros c p0 p1 Hprop.
  rewrite prop_val_equation. rewrite Hprop. reflexivity.
Qed.

Lemma prop_val_or_n_r : forall c p0 p1,
  prop_val c p1 = None -> prop_val c (p_or p0 p1) = None.
Proof.
  intros c p0 p1 Hprop0.
  rewrite prop_val_equation. rewrite Hprop0.
  case_eq (prop_val c p0); auto.
Qed.

Lemma prop_val_and_b : forall c p0 p1 b0 b1,
  prop_val c p0 = Some b0 -> prop_val c p1 = Some b1 ->
  prop_val c (p_and p0 p1) = Some (andb b0 b1).
Proof.
  intros c p0 p1 b0 b1 Hprop0 Hprop1.
  rewrite prop_val_equation. rewrite Hprop0. rewrite Hprop1. reflexivity.
Qed.

Lemma prop_val_and_n_l : forall c p0 p1,
  prop_val c p0 = None -> prop_val c (p_and p0 p1) = None.
Proof.
  intros c p0 p1 Hprop.
  rewrite prop_val_equation. rewrite Hprop. reflexivity.
Qed.

Lemma prop_val_and_n_r : forall c p0 p1,
  prop_val c p1 = None -> prop_val c (p_and p0 p1) = None.
Proof.
  intros c p0 p1 Hprop0.
  rewrite prop_val_equation. rewrite Hprop0.
  case_eq (prop_val c p0); auto.
Qed.

Lemma prop_val_impl_b : forall c p0 p1 b0 b1,
  prop_val c p0 = Some b0 -> prop_val c p1 = Some b1 ->
  prop_val c (p_impl p0 p1) = Some (implb b0 b1).
Proof.
  intros c p0 p1 b0 b1 Hprop0 Hprop1.
  rewrite prop_val_equation. rewrite Hprop0. rewrite Hprop1. reflexivity.
Qed.

Lemma prop_val_impl_n_l : forall c p0 p1,
  prop_val c p0 = None -> prop_val c (p_impl p0 p1) = None.
Proof.
  intros c p0 p1 Hprop.
  rewrite prop_val_equation. rewrite Hprop. reflexivity.
Qed.

Lemma prop_val_impl_n_r : forall c p0 p1,
  prop_val c p1 = None -> prop_val c (p_impl p0 p1) = None.
Proof.
  intros c p0 p1 Hprop0.
  rewrite prop_val_equation. rewrite Hprop0.
  case_eq (prop_val c p0); auto.
Qed.

Inductive seq_l : Set :=
  | seq_l_nil : seq_l
  | seq_l_cons : prop -> seq_l -> seq_l.

Function seq_l_val (c : ctx) (s : seq_l) {struct s} : option bool :=
  match s with
  | seq_l_nil => Some true
  | seq_l_cons p s =>
      match prop_val c p with
      | None => None
      | Some b1 =>
          match seq_l_val c s with
          | None => None
          | Some b2 => Some (andb b1 b2)
          end
      end
  end.

Lemma seq_l_val_lem : forall c p s b0 b1,
  seq_l_val c s = Some b0 -> prop_val c p = Some b1 ->
  seq_l_val c (seq_l_cons p s) = Some (andb b1 b0).
Proof.
  intros c p s b0 b1 Hs Hp.
  rewrite (seq_l_val_equation c (seq_l_cons p s)).
  rewrite Hp. rewrite Hs. reflexivity.
Qed.

Inductive seq_r : Set :=
  | seq_r_nil : seq_r
  | seq_r_cons : prop -> seq_r -> seq_r.

Function seq_r_val (c : ctx) (s : seq_r) {struct s} : option bool :=
  match s with
  | seq_r_nil => Some false
  | seq_r_cons p s =>
      match prop_val c p with
      | None => None
      | Some b1 =>
          match seq_r_val c s with
          | None => None
          | Some b2 => Some (orb b1 b2)
          end
      end
  end.

Lemma seq_r_val_lem : forall c p s b0 b1,
  seq_r_val c s = Some b0 -> prop_val c p = Some b1 ->
  seq_r_val c (seq_r_cons p s) = Some (orb b1 b0).
Proof.
  intros c p s b0 b1 Hs Hp.
  rewrite (seq_r_val_equation c (seq_r_cons p s)).
  rewrite Hp. rewrite Hs. reflexivity.
Qed.

Inductive seq_t : Set :=
  | seq : seq_l -> seq_r -> seq_t.

Definition seq_val (c : ctx) (s : seq_t) : option bool :=
  match s with
  | seq l r =>
      match seq_l_val c l with
      | None => None
      | Some b1 =>
          match seq_r_val c r with
          | None => None
          | Some b2 => Some (implb b1 b2)
          end
      end
  end.

Lemma satisfying_ctx_r : forall c l r b b1 b2,
  (seq_l_val c l = Some b1 /\ seq_r_val c r = Some b2 /\ b = implb b1 b2) ->
  (seq_val c (seq l r) = Some b).
Proof.
  intros c l r b b1 b2 [ Hbl [ Hbr Himpl ] ].
  unfold seq_val. rewrite Hbl. rewrite Hbr. rewrite Himpl. reflexivity.
Qed.

(* `exists` is required as implies is not an injective function *)
Lemma satisfying_ctx_l : forall c l r b,
  (seq_val c (seq l r) = Some b) ->
  (exists b1 b2, seq_l_val c l = Some b1 /\ seq_r_val c r = Some b2 /\ b = implb b1 b2).
Proof.
  intros c l r b.
  unfold seq_val. destruct (seq_l_val c l). destruct (seq_r_val c r).
  - intros H. inversion H. exists b0. exists b1. repeat split.
  - intros H. discriminate.
  - intros H. discriminate.
Qed.

Inductive eval_unary : seq_t -> seq_t -> Prop :=
  | neg_l : forall p l r,
      eval_unary (seq (seq_l_cons (p_neg p) l) r)
           (seq l (seq_r_cons p r))
  | neg_r : forall p l r,
      eval_unary (seq l (seq_r_cons (p_neg p) r))
           (seq (seq_l_cons p l) r)
  | or_r : forall p0 p1 l r,
      eval_unary (seq l (seq_r_cons (p_or p0 p1) r))
           (seq l (seq_r_cons p0 (seq_r_cons p1 r)))
  | impl_r : forall p0 p1 l r,
      eval_unary (seq l (seq_r_cons (p_impl p0 p1) r))
          (seq (seq_l_cons p0 l) (seq_r_cons p1 r)).

Inductive eval_binary : seq_t -> seq_t -> seq_t -> Prop :=
  | or_l : forall p0 p1 l r,
      eval_binary (seq (seq_l_cons (p_or p0 p1) l) r)
           (seq (seq_l_cons p0 l) r)
           (seq (seq_l_cons p1 l) r).

