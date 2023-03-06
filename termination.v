Require Import Bool.
Require Import FunInd.
Require Import Psatz.
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
    intros Heq0 Heq1. subst. simpl. lia.
  - unfold measure_seq. rewrite measure_r_equation.
    rewrite (measure_l_equation (seq_l_cons p l)).
    intros Heq0 Heq1. subst. simpl. lia.
  - unfold measure_seq. rewrite measure_r_equation.
    rewrite (measure_r_equation (seq_r_cons p0 (seq_r_cons p1 r))).
    rewrite (measure_r_equation (seq_r_cons p1 r)).
    intros Heq0 Heq1. subst. simpl. lia.
    - unfold measure_seq. rewrite measure_r_equation.
    rewrite (measure_l_equation (seq_l_cons p0 l)).
    rewrite (measure_r_equation (seq_r_cons p1 r)).
    intros Heq0 Heq1. subst. simpl. lia.
Qed.
