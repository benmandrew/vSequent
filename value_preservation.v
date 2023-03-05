Require Import Bool.
Require Import vsequent.

Lemma negl_preserves_val : forall b0 b1 b2,
implb (andb (negb b0) b1) b2 = implb b1 (orb b0 b2).
Proof.
intros b0 b1 b2.
destruct b0; destruct b1; destruct b2; auto.
Qed.

Lemma negr_preserves_val : forall b0 b1 b2,
implb (andb b0 b1) b2 = implb b1 (orb (negb b0) b2).
Proof.
intros b0 b1 b2.
destruct b0; destruct b1; destruct b2; auto.
Qed.

Lemma eval_preserves_val_neg_l : forall c p l r b,
seq_val c (seq (seq_l_cons (p_neg p) l) r) = Some b ->
seq_val c (seq l (seq_r_cons p r)) = Some b.
Proof.
intros c p l r b Heq.
apply (satisfying_ctx_l c (seq_l_cons (p_neg p) l) r b) in Heq.
destruct Heq as [ b1 [ b2 [ Hl [ Hr Himpl ] ] ] ].
case_eq (prop_val c p).
- intros b0 Hprop.
  apply prop_val_neg_b in Hprop as Hprop_neg.
  rewrite seq_l_val_equation in Hl.
  rewrite Hprop_neg in Hl.
  unfold seq_val.
  rewrite (seq_r_val_lem c p r b2 b0).
  + case_eq (seq_l_val c l).
    * intros b3 Hl'.
      rewrite Hl' in Hl. inversion Hl. subst.
      rewrite negl_preserves_val. reflexivity.
    * intro. rewrite H in Hl. discriminate.
  + assumption.
  + assumption.
- intros Hprop. rewrite seq_l_val_equation in Hl.
  apply prop_val_neg_n in Hprop.
  rewrite Hprop in Hl. discriminate.
Qed.

Lemma eval_preserves_val_neg_r : forall c p l r b,
seq_val c (seq l (seq_r_cons (p_neg p) r)) = Some b ->
seq_val c (seq (seq_l_cons p l) r) = Some b.
Proof.
intros c p l r b Heq.
apply (satisfying_ctx_l c l (seq_r_cons (p_neg p) r) b) in Heq.
destruct Heq as [ b1 [ b2 [ Hl [ Hr Himpl ] ] ] ].
case_eq (prop_val c p).
- intros b0 Hprop.
  apply prop_val_neg_b in Hprop as Hprop_neg.
  rewrite seq_r_val_equation in Hr.
  rewrite Hprop_neg in Hr.
  unfold seq_val.
  rewrite (seq_l_val_lem c p l b1 b0).
  + case_eq (seq_r_val c r).
    * intros b3 Hr'.
      rewrite Hr' in Hr. inversion Hr. subst.
      rewrite negr_preserves_val. reflexivity.
    * intro. rewrite H in Hr. discriminate.
  + assumption.
  + assumption.
- intros Hprop. rewrite seq_r_val_equation in Hr.
  apply prop_val_neg_n in Hprop.
  rewrite Hprop in Hr. discriminate.
Qed.

Lemma eval_preserves_val_or_r : forall c p0 p1 l r b,
seq_val c (seq l (seq_r_cons (p_or p0 p1) r)) = Some b ->
seq_val c (seq l (seq_r_cons p0 (seq_r_cons p1 r))) = Some b.
Proof.
intros c p0 p1 l r b Heq.
apply (satisfying_ctx_l c l (seq_r_cons (p_or p0 p1) r)) in Heq.
destruct Heq as [ b0 [ b1 [ Hl [ Hr Himpl ] ] ] ].
apply (satisfying_ctx_r c l (seq_r_cons p0 (seq_r_cons p1 r)) b b0 b1).
repeat split.
- assumption.
- case_eq (prop_val c p1); case_eq (prop_val c p0).
  + intros b2 Hprop0 b3 Hprop1.
    apply (prop_val_or_b c p0 p1 b2 b3) in Hprop0 as Hprop2.
    rewrite seq_r_val_equation. rewrite seq_r_val_equation.
    rewrite Hprop0. rewrite Hprop1.
    rewrite seq_r_val_equation in Hr. rewrite Hprop2 in Hr.
    revert Hr. case_eq (seq_r_val c r).
    * intros b4 Hr Hor.
      inversion Hor. rewrite <- (orb_assoc b2 b3 b4). reflexivity.
    * auto.
    * assumption.
  + intros Hprop0. apply (prop_val_or_n_l c p0 p1) in Hprop0.
    rewrite seq_r_val_equation in Hr. rewrite Hprop0 in Hr. discriminate.
  + intros Hprop0 b2 Hprop1. apply (prop_val_or_n_r c p0 p1) in Hprop1.
    rewrite seq_r_val_equation in Hr. rewrite Hprop1 in Hr. discriminate.
  + intros Hprop0. apply (prop_val_or_n_l c p0 p1) in Hprop0.
    rewrite seq_r_val_equation in Hr. rewrite Hprop0 in Hr. discriminate.
- assumption.
Qed.

Lemma eval_preserves_val_or_l : forall c p0 p1 l r b0 b1 b2,
seq_val c (seq (seq_l_cons (p_or p0 p1) l) r) = Some b0 ->
seq_val c (seq (seq_l_cons p0 l) r) = Some b1 ->
seq_val c (seq (seq_l_cons p1 l) r) = Some b2 ->
b0 = andb b1 b2.
Proof.
intros c p0 p1 l r b0 b1 b2 Heq0 Heq1 Heq2.
apply (satisfying_ctx_l c (seq_l_cons (p_or p0 p1) l) r) in Heq0.
destruct Heq0 as [ b00 [ b01 [ Hl0 [ Hr0 Himpl0 ] ] ] ].
apply (satisfying_ctx_l c (seq_l_cons p0 l) r) in Heq1.
destruct Heq1 as [ b10 [ b11 [ Hl1 [ Hr1 Himpl1 ] ] ] ].
apply (satisfying_ctx_l c (seq_l_cons p1 l) r) in Heq2.
destruct Heq2 as [ b20 [ b21 [ Hl2 [ Hr2 Himpl2 ] ] ] ].
subst. rewrite Hr0 in Hr1. inversion Hr1. rewrite Hr2 in Hr0. inversion Hr0. rewrite H0.
clear H0 H1 Hr0 Hr1 Hr2.
case_eq (prop_val c p1); case_eq (prop_val c p0).
- intros b0 Hprop0 b1 Hprop1.
  apply (prop_val_or_b c p0 p1 b0 b1) in Hprop0 as Hprop2.
  rewrite seq_l_val_equation in Hl0. rewrite Hprop2 in Hl0.
  rewrite seq_l_val_equation in Hl1. rewrite Hprop0 in Hl1.
  rewrite seq_l_val_equation in Hl2. rewrite Hprop1 in Hl2.
  case_eq (seq_l_val c l).
  + intros b Hseql. rewrite Hseql in Hl0. rewrite Hseql in Hl1. rewrite Hseql in Hl2.
    inversion Hl0. inversion Hl1. inversion Hl2. clear Hl0 Hl1 Hl2.
    destruct b00; destruct b01; destruct b0; destruct b1;
    destruct b; destruct b21; destruct b10; destruct b11; auto.
  + intros Hseql. rewrite Hseql in Hl0. discriminate.
  + assumption.
- intros Hprop.
  rewrite seq_l_val_equation in Hl1. rewrite Hprop in Hl1. discriminate.
- intros b Hprop0 Hprop1.
  rewrite seq_l_val_equation in Hl2. rewrite Hprop1 in Hl2. discriminate.
- intros Hprop.
  rewrite seq_l_val_equation in Hl1. rewrite Hprop in Hl1. discriminate.
Qed.

Lemma eval_preserves_val_impl_r : forall c p0 p1 l r b,
seq_val c (seq l (seq_r_cons (p_impl p0 p1) r)) = Some b ->
seq_val c (seq (seq_l_cons p0 l) (seq_r_cons p1 r)) = Some b.
Proof.
intros c p0 p1 l r b Heq.
apply (satisfying_ctx_l c l (seq_r_cons (p_impl p0 p1) r)) in Heq.
destruct Heq as [ b0 [ b1 [ Hl [ Hr Himpl ] ] ] ].
case_eq (prop_val c p0); case_eq (prop_val c p1).
- intros b2 Hprop0 b3 Hprop1.
  rewrite seq_r_val_equation in Hr.
  apply (prop_val_impl_b c p0 p1 b3 b2) in Hprop0 as Hprop2.
  rewrite Hprop2 in Hr.
  case_eq (seq_r_val c r).
  + intros b4 Hseqr.
    rewrite Hseqr in Hr. inversion Hr. clear Hr.
    apply (satisfying_ctx_r c (seq_l_cons p0 l) (seq_r_cons p1 r) b (andb b3 b0) (orb b2 b4)).
    repeat split.
    * rewrite seq_l_val_equation. rewrite Hprop1. rewrite Hl. reflexivity.
    * rewrite seq_r_val_equation. rewrite Hprop0. rewrite Hseqr. reflexivity.
    * subst. destruct b0; destruct b2; destruct b3; destruct b4; auto.
  + intros Hseqr. rewrite Hseqr in Hr. discriminate.
  + assumption.
- intros Hprop.
  rewrite seq_r_val_equation in Hr. rewrite prop_val_impl_n_r in Hr.
  + discriminate.
  + assumption.
- intros b2 Hprop0 Hprop1.
  rewrite seq_r_val_equation in Hr. rewrite prop_val_impl_n_l in Hr.
  + discriminate.
  + assumption.
- intros Hprop.
  rewrite seq_r_val_equation in Hr. rewrite prop_val_impl_n_r in Hr.
  + discriminate.
  + assumption.
Qed.

Lemma eval_preserves_val_unary : forall c s0 s1 b,
eval_unary s0 s1 -> seq_val c s0 = Some b -> seq_val c s1 = Some b.
Proof.
intros c s0 s1 b Hev Heq. induction Hev.
- apply eval_preserves_val_neg_l. assumption.
- apply eval_preserves_val_neg_r. assumption.
- apply eval_preserves_val_or_r. assumption.
- apply eval_preserves_val_impl_r. assumption.
Qed.

Lemma eval_preserves_val_binary : forall c s0 s1 s2 b0 b1 b2,
eval_binary s0 s1 s2 -> seq_val c s0 = Some b0 ->
seq_val c s1 = Some b1 -> seq_val c s2 = Some b2 -> b0 = andb b1 b2.
Proof.
intros c s0 s1 s2 b0 b1 b2 Hev Heq1 Heq2 Heq3. induction Hev.
- apply (eval_preserves_val_or_l c p0 p1 l r b0 b1 b2); assumption.
Qed.
