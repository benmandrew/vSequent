Require Import Bool Psatz Arith.PeanoNat.
Require Import FunInd.
Require Import vsequent.

Function measure_p (p : prop) : nat :=
  match p with
  | p_sym _ => O
  | p_neg p0 => S (measure_p p0)
  | p_and p0 p1
  | p_or p0 p1
  | p_impl p0 p1 => S (measure_p p0 + measure_p p1)
  end.

Function measure_l (s : seq_l) : nat :=
  match s with
  | seq_l_nil => O
  | seq_l_cons p s0 => measure_p p + measure_l s0
  end.

Function measure_r (s : seq_r) : nat :=
  match s with
  | seq_r_nil => O
  | seq_r_cons p s0 => measure_p p + measure_r s0
  end.

Function measure (s : seq_t) : nat :=
  match s with
  | seq l r => measure_l l + measure_r r
  end.

Lemma measure_break : forall l r n,
  measure (seq l r) = n -> exists n0 n1,
  measure_l l = n0 /\ measure_r r = n1 /\ n = n0 + n1.
Proof.
  intros l r n.
  unfold measure. destruct (measure_l l); destruct (measure_r r).
  - intros H. exists O. exists O. auto.
  - intros H. exists O. exists (S n0). auto.
  - intros H. exists (S n0). exists O. auto.
  - intros H. exists (S n0). exists (S n1). auto.
Qed.

Lemma eval_unary_decreases : forall s0 s1 n0 n1,
  eval_unary s0 s1 -> measure s0 = n0 ->
  measure s1 = n1 -> n1 < n0.
Proof.
  intros s0 s1 n0 n1 Heval. induction Heval.
  - unfold measure. rewrite measure_l_equation.
    rewrite (measure_r_equation (seq_r_cons p r)).
    intros Heq0 Heq1. subst. simpl. lia.
  - unfold measure. rewrite measure_r_equation.
    rewrite (measure_l_equation (seq_l_cons p l)).
    intros Heq0 Heq1. subst. simpl. lia.
  - unfold measure. rewrite measure_r_equation.
    rewrite (measure_r_equation (seq_r_cons p0 (seq_r_cons p1 r))).
    rewrite (measure_r_equation (seq_r_cons p1 r)).
    intros Heq0 Heq1. subst. simpl. lia.
    - unfold measure. rewrite measure_r_equation.
    rewrite (measure_l_equation (seq_l_cons p0 l)).
    rewrite (measure_r_equation (seq_r_cons p1 r)).
    intros Heq0 Heq1. subst. simpl. lia.
Qed.

Lemma eval_binary_decreases : forall s0 s1 s2 n0 n1 n2,
  eval_binary s0 s1 s2 -> measure s0 = n0 ->
  measure s1 = n1 -> measure s2 = n2 -> n1 < n0 /\ n2 < n0.
Proof.
  intros s0 s1 s2 n0 n1 n2 Heval. induction Heval.
  - unfold measure. rewrite measure_l_equation.
    rewrite (measure_l_equation (seq_l_cons p0 l)).
    rewrite (measure_l_equation (seq_l_cons p1 l)).
    intros Heq0 Heq1 Heq2. subst. simpl. lia.
Qed.

Definition normal_form_unary (s : seq_t) : Prop :=
  ~ exists s', eval_unary s s'.

Definition normal_form_binary (s : seq_t) : Prop :=
  ~ exists s' s'', eval_binary s s' s''.

Definition normal_form (s : seq_t) : Prop :=
  normal_form_unary s /\ normal_form_binary s.

Lemma prop_zero_measure : forall p,
  measure_p p = O -> exists n, p = p_sym n.
Proof.
  intros p Hm. rewrite measure_p_equation in Hm. induction p.
  - exists n. reflexivity.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
Qed.

Lemma seq_l_zero_measure : forall p l,
  measure_l (seq_l_cons p l) = O -> exists n, p = p_sym n.
Proof.
  intros p l. rewrite measure_l_equation. induction l.
  - unfold measure_l. rewrite Plus.plus_0_r.
    apply prop_zero_measure.
  - rewrite measure_l_equation.
    rewrite (Plus.plus_comm (measure_p p0) (measure_l l)).
    rewrite (Plus.plus_assoc). intros Hm.
    apply (Plus.plus_is_O (measure_p p + measure_l l) (measure_p p0)) in Hm as [ Hm Hp ].
    apply IHl in Hm. assumption.
Qed.

Lemma seq_r_zero_measure : forall p r,
  measure_r (seq_r_cons p r) = O -> exists n, p = p_sym n.
Proof.
  intros p r. rewrite measure_r_equation. induction r.
  - unfold measure_r. rewrite Plus.plus_0_r.
    apply prop_zero_measure.
  - rewrite measure_r_equation.
    rewrite (Plus.plus_comm (measure_p p0) (measure_r r)).
    rewrite (Plus.plus_assoc). intros Hm.
    apply (Plus.plus_is_O (measure_p p + measure_r r) (measure_p p0)) in Hm as [ Hm Hp ].
    apply IHr in Hm. assumption.
Qed.

Lemma plus_to_O : forall n0 n1,
  n0 = O -> n1 = O -> n0 + n1 = O.
Proof.
  lia.
Qed.

Lemma measure_zero_iff_normal_form : forall s,
  measure s = O <-> normal_form s.
Proof.
  intros s.
  split.
  - intros Hm. split.
    + intros [ s' Hex ].
      remember (measure s') as n1.
      apply (eval_unary_decreases s s' 0 n1) in Hex.
      * lia.
      * assumption.
      * auto.
    + intros [ s' [ s'' Hex ] ].
      remember (measure s') as n1.
      remember (measure s'') as n2.
      apply (eval_binary_decreases s s' s'' 0 n1 n2) in Hex.
      * lia.
      * assumption.
      * auto.
      * auto.
  - intros [ Hu Hb ].
    unfold measure. destruct s as [ l r ]. induction l; induction r.
    + rewrite measure_l_equation. rewrite measure_r_equation. auto.
    + rewrite measure_l_equation. rewrite measure_r_equation. simpl.
       apply plus_to_O.
