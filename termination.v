Require Import Bool.
Require Import FunInd.
Require Import vsequent.

Function measure (p : prop) : nat :=
  match p with
  | p_sym _ => O
  | p_neg p0 => S (measure p0)
  | p_and p0 p1
  | p_or p0 p1
  | p_impl p0 p1 => S (measure p0 + measure p1)
  end.

Function measure_l (s : seq_l) : nat :=
  match s with
  | seq_l_nil => O
  | seq_l_cons p s0 => measure p + measure_l s0
  end.

Function measure_r (s : seq_r) : nat :=
  match s with
  | seq_r_nil => O
  | seq_r_cons p s0 => measure p + measure_r s0
  end.

Function measure_seq (s : seq_t) : nat :=
  match s with
  | seq l r => measure_l l + measure_r r
  end.

Lemma measure_seq_break : forall l r n,
  measure_seq (seq l r) = n -> exists n0 n1,
  measure_l l = n0 /\ measure_r r = n1 /\ n = n0 + n1.
Proof.
  intros l r n.
  unfold measure_seq. destruct (measure_l l); destruct (measure_r r).
  - intros H. exists O. exists O. auto.
  - intros H. exists O. exists (S n0). auto.
  - intros H. exists (S n0). exists O. auto.
  - intros H. exists (S n0). exists (S n1). auto.
Qed.

Lemma eval_unary_decreases : forall s0 s1 n0 n1,
  eval_unary s0 s1 -> measure_seq s0 = n0 ->
  measure_seq s1 = n1 -> n1 < n0.
Proof.
  intros s0 s1 n0 n1 Heval. induction Heval.
  - unfold measure_seq. rewrite measure_l_equation.
    rewrite (measure_r_equation (seq_r_cons p r)).
    intros Heq0 Heq1. subst. simpl.

(* Lemma measure_neg : forall p n,
  measure p = n -> measure (p_neg p) = S n.
Proof.
  intros p n Heq.
  rewrite measure_equation. rewrite Heq. reflexivity.
Qed.

Lemma measure_and : forall p0 p1 n0 n1,
  measure p0 = n0 -> measure p1 = n1 ->
  measure (p_and p0 p1) = S (n0 + n1).
Proof.
  intros p0 p1 n0 n1 Heq0 Heq1.
  rewrite measure_equation.
  rewrite Heq0. rewrite Heq1. reflexivity.
Qed.

Lemma measure_or : forall p0 p1 n0 n1,
  measure p0 = n0 -> measure p1 = n1 ->
  measure (p_or p0 p1) = S (n0 + n1).
Proof.
  intros p0 p1 n0 n1 Heq0 Heq1.
  rewrite measure_equation.
  rewrite Heq0. rewrite Heq1. reflexivity.
Qed.

Lemma measure_impl : forall p0 p1 n0 n1,
  measure p0 = n0 -> measure p1 = n1 ->
  measure (p_impl p0 p1) = S (n0 + n1).
Proof.
  intros p0 p1 n0 n1 Heq0 Heq1.
  rewrite measure_equation.
  rewrite Heq0. rewrite Heq1. reflexivity.
Qed. *)




