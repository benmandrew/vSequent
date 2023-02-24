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

Fixpoint prop_val (c : ctx) (p : prop) {struct p} : option bool :=
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

Inductive s_l : Set :=
  | s_l_nil : s_l
  | s_l_cons : prop -> s_l -> s_l.

Fixpoint s_l_val (c : ctx) (s : s_l) {struct s} : option bool :=
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

Lemma s_l_val_ind : forall c p s b,
  s_l_val c (s_l_cons p s) = Some b -> (exists b1 b2,
  (b = andb b1 b2) /\ prop_val c p = Some b1 /\ s_l_val c s = Some b2).
Proof.
  intros c p s b Heq.
  induction s.
    case_eq (prop_val c p).
      intros b1 Hprop. exists b1. exists true.
      unfold s_l_val in Heq. rewrite -> Hprop in Heq. inversion Heq. auto.
      intros Hprop. unfold s_l_val in Heq. rewrite -> Hprop in Heq. discriminate.
Admitted.
    

Inductive s_r : Set :=
  | s_r_nil : s_r
  | s_r_cons : prop -> s_r -> s_r.

Fixpoint s_r_val (c : ctx) (s : s_r) {struct s} : option bool :=
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


Lemma eval_preserves_val : forall c s1 s2 b,
  eval s1 s2 -> seq_val c s1 = Some b -> seq_val c s2 = Some b.
Proof.
  intros c s1 s2 b Hev Heq. induction Hev.
    apply (satisfying_ctx_l c (s_l_cons (p_neg p) l) r b) in Heq.
    destruct Heq as [ b1 [ b2 [ Hl [ Hr Himpl ] ] ] ].

    (* apply (satisfying_ctx_l c (s_l_cons (p_neg p) l) r b1) in Hl. *)
    (* pose proof (s_l_val_ind c) as Hind. *)
    (* destruct b; destruct b1; destruct b2. *)
      (* pose proof (s_l_val_ind c) as Hind. *)
      (* pose proof (s_l_val_ind c) as Hind.
    apply (satisfying_ctx_r c l (s_r_cons p r) true true true). *)
Admitted.
