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

Inductive s_r : Set :=
  | s_r_nil : s_r
  | s_r_cons : prop -> s_r -> s_r.

Inductive seq_t : Set :=
  | seq : s_l -> s_r -> seq_t.

Inductive eval : seq_t -> seq_t -> Prop :=
  | neg_l : forall p l r,
      eval (seq (s_l_cons (p_neg p) l) r)
           (seq l (s_r_cons p r))
  | neg_r : forall p l r,
      eval (seq l (s_r_cons (p_neg p) r))
           (seq (s_l_cons p l) r).
