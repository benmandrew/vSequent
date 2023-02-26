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
  rewrite -> (seq_l_val_equation c (seq_l_cons p s)).
  rewrite -> Hp. rewrite -> Hs. reflexivity.
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
  rewrite -> (seq_r_val_equation c (seq_r_cons p s)).
  rewrite -> Hp. rewrite -> Hs. reflexivity.
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
  intros c l r b Hs.
  generalize dependent Hs.
  unfold seq_val. destruct (seq_l_val c l). destruct (seq_r_val c r).
  - intros H. inversion H. exists b0. exists b1. repeat (try split).
  - intros H. discriminate.
  - intros H. discriminate.
Qed.

Inductive eval : seq_t -> seq_t -> Prop :=
  | neg_l : forall p l r,
      eval (seq (seq_l_cons (p_neg p) l) r)
           (seq l (seq_r_cons p r))
  | neg_r : forall p l r,
      eval (seq l (seq_r_cons (p_neg p) r))
           (seq (seq_l_cons p l) r)
  | or_r : forall p0 p1 l r,
      eval (seq l (seq_r_cons (p_or p0 p1) r))
           (seq l (seq_r_cons p0 (seq_r_cons p1 r))).

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

Lemma eval_preserves_val_neg_r : forall c p l r b,
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
    rewrite -> (seq_r_val_lem c p r b2 b0).
    + case_eq (seq_l_val c l).
        intros b3 Hl'.
        rewrite Hl' in Hl. inversion Hl. subst.
        rewrite negl_preserves_val. reflexivity.
      intro. rewrite H in Hl. discriminate.
    + assumption.
    + assumption.
  - intros Hprop. rewrite seq_l_val_equation in Hl.
    apply prop_val_neg_n in Hprop.
    rewrite Hprop in Hl. discriminate.
Qed.

Lemma eval_preserves_val_neg_l : forall c p l r b,
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
        intros b3 Hr'.
        rewrite Hr' in Hr. inversion Hr. subst.
        rewrite negr_preserves_val. reflexivity.
      intro. rewrite H in Hr. discriminate.
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
  repeat (try split).
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

Lemma eval_preserves_val : forall c s1 s2 b,
  eval s1 s2 -> seq_val c s1 = Some b -> seq_val c s2 = Some b.
Proof.
  intros c s1 s2 b Hev Heq. induction Hev.
  - apply eval_preserves_val_neg_r. assumption.
  - apply eval_preserves_val_neg_l. assumption.
  - apply eval_preserves_val_or_r. assumption.
Qed.
