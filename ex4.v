Require Import Arith.

Fixpoint sum_n (n:nat) : nat :=
  match n with 0 => 0 | S p => S p + sum_n p end.

Theorem P : forall n:nat, 2 * sum_n n = n * n + n.
Proof.
  intros n0.
  elim n0.
  auto.
  intros n1.
  intros IHn1.
  simpl sum_n.
  apply Nat.mul_add_distr_l.
