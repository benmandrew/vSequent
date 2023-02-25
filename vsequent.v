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
  rewrite prop_val_equation. rewrite -> H. reflexivity.
Qed.

Lemma prop_val_neg_n : forall c p,
  prop_val c p = None -> prop_val c (p_neg p) = None.
Proof.
  intros c p H.
  rewrite prop_val_equation. rewrite -> H. reflexivity.
Qed.

Inductive s_l : Set :=
  | s_l_nil : s_l
  | s_l_cons : prop -> s_l -> s_l.

Function s_l_val (c : ctx) (s : s_l) {struct s} : option bool :=
  match s with
  | s_l_nil => Some true
  | s_l_cons p s =>
      match prop_val c p with
      | None => None
      | Some b1 =>
          match s_l_val c s with
          | None => None
          | Some b2 => Some (andb b1 b2)
          end
      end
  end.

Lemma s_l_val_lem : forall c p s b0 b1,
  s_l_val c s = Some b0 -> prop_val c p = Some b1 ->
  s_l_val c (s_l_cons p s) = Some (andb b1 b0).
Proof.
  intros c p s b0 b1 Hs Hp.
  rewrite -> (s_l_val_equation c (s_l_cons p s)).
  rewrite -> Hp. rewrite -> Hs. reflexivity.
Qed.

Inductive s_r : Set :=
  | s_r_nil : s_r
  | s_r_cons : prop -> s_r -> s_r.

Function s_r_val (c : ctx) (s : s_r) {struct s} : option bool :=
  match s with
  | s_r_nil => Some false
  | s_r_cons p s =>
      match prop_val c p with
      | None => None
      | Some b1 =>
          match s_r_val c s with
          | None => None
          | Some b2 => Some (orb b1 b2)
          end
      end
  end.

Lemma s_r_val_lem : forall c p s b0 b1,
  s_r_val c s = Some b0 -> prop_val c p = Some b1 ->
  s_r_val c (s_r_cons p s) = Some (orb b1 b0).
Proof.
  intros c p s b0 b1 Hs Hp.
  rewrite -> (s_r_val_equation c (s_r_cons p s)).
  rewrite -> Hp. rewrite -> Hs. reflexivity.
Qed.

Inductive seq_t : Set :=
  | seq : s_l -> s_r -> seq_t.

Definition seq_val (c : ctx) (s : seq_t) : option bool :=
  match s with
  | seq l r =>
      match s_l_val c l with
      | None => None
      | Some b1 =>
          match s_r_val c r with
          | None => None
          | Some b2 => Some (implb b1 b2)
          end
      end
  end.

Lemma satisfying_ctx_r : forall c l r b b1 b2,
  (s_l_val c l = Some b1 /\ s_r_val c r = Some b2 /\ b = implb b1 b2) ->
  (seq_val c (seq l r) = Some b).
Proof.
  intros c l r b b1 b2 [ Hbl [ Hbr Himpl ] ].
  unfold seq_val. destruct (s_l_val c l). destruct (s_r_val c r).
    inversion Hbl. inversion Hbr. subst b. reflexivity.
    discriminate.
    discriminate.
Qed.

(* `exists` is required as implies is not an injective function *)
Lemma satisfying_ctx_l : forall c l r b,
  (seq_val c (seq l r) = Some b) ->
  (exists b1 b2, s_l_val c l = Some b1 /\ s_r_val c r = Some b2 /\ b = implb b1 b2).
Proof.
  intros c l r b Hs.
  generalize dependent Hs.
  unfold seq_val. destruct (s_l_val c l). destruct (s_r_val c r).
    intro H. inversion H. exists b0. exists b1. split. reflexivity. split; reflexivity.
    intro H. discriminate.
    intro H. discriminate.
Qed.

Inductive eval : seq_t -> seq_t -> Prop :=
  | neg_l : forall p l r,
      eval (seq (s_l_cons (p_neg p) l) r)
           (seq l (s_r_cons p r))
  | neg_r : forall p l r,
      eval (seq l (s_r_cons (p_neg p) r))
           (seq (s_l_cons p l) r).

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

Lemma eval_preserves_val : forall c s1 s2 b,
  eval s1 s2 -> seq_val c s1 = Some b -> seq_val c s2 = Some b.
Proof.
  intros c s1 s2 b Hev Heq. induction Hev.
    apply (satisfying_ctx_l c (s_l_cons (p_neg p) l) r b) in Heq.
    destruct Heq as [ b1 [ b2 [ Hl [ Hr Himpl ] ] ] ].
    case_eq (prop_val c p).
      intros b0 Hprop.
      apply prop_val_neg_b in Hprop as Hprop_neg.
      rewrite s_l_val_equation in Hl.
      rewrite Hprop_neg in Hl.
      unfold seq_val.
      rewrite -> (s_r_val_lem c p r b2 b0).
        case_eq (s_l_val c l).
          intros b3 Hl'.
          rewrite Hl' in Hl. inversion Hl. subst.
          rewrite negl_preserves_val. reflexivity.
        intro. rewrite H in Hl. discriminate.
        assumption.
        assumption.
      intros Hprop. rewrite s_l_val_equation in Hl.
      apply prop_val_neg_n in Hprop.
      rewrite Hprop in Hl. discriminate.
    apply (satisfying_ctx_l c l (s_r_cons (p_neg p) r) b) in Heq.
    destruct Heq as [ b1 [ b2 [ Hl [ Hr Himpl ] ] ] ].
    case_eq (prop_val c p).
      intros b0 Hprop.
      apply prop_val_neg_b in Hprop as Hprop_neg.
      rewrite s_r_val_equation in Hr.
      rewrite Hprop_neg in Hr.
      unfold seq_val.
      rewrite (s_l_val_lem c p l b1 b0).
        case_eq (s_r_val c r).
          intros b3 Hr'.
          rewrite Hr' in Hr. inversion Hr. subst.
          rewrite negr_preserves_val. reflexivity.
        intro. rewrite H in Hr. discriminate.
        assumption.
        assumption.
      intros Hprop. rewrite s_r_val_equation in Hr.
      apply prop_val_neg_n in Hprop.
      rewrite Hprop in Hr. discriminate.
Qed.
