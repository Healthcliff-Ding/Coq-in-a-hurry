Require Import Coq.Arith.Arith.

Inductive even : nat -> Prop :=
| even0 : even 0
| evenS : forall x:nat, even x -> even (S (S x)).

Theorem even_mult : forall x, even x -> exists y, x = 2 * y.
Proof.
  intros x.
  intros H.
  elim H.
  exists 0.
  auto.
  intros x0.
  intros Hevenx0.
  intros IHx0.
  destruct IHx0 as [y Heq].
  rewrite Heq.
  exists (S y).
  ring.

Theorem even_mult' : forall x, even x -> exists y, x = 2 * y.
Proof.
  intros x.
  assert (lemma: (even x -> exists y, x = 2 * y) /\ 
          (even (S x) -> exists y, S x = 2 * y)).
  elim x.
  split.
  exists 0.
  ring.
  intros Heven1.
  inversion Heven1.
  intros x0 IHx0.
  destruct IHx0 as [IHx0 IHSx0].
  split.
  apply IHSx0.
  intros HevenSSx0.
  assert (Hevenx0 : even x0).
  inversion HevenSSx0.
  apply H0.
  destruct (IHx0 Hevenx0) as [y Heq].
  exists (S y).
  rewrite Heq.
  ring.
  destruct lemma as [Hx0 HSx0].
  assumption.