Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Lemma inversion_example : forall l, l = cons 0 nil -> exists n, l = cons n nil.
Proof.
  intros l H.
  inversion H.
  exists 0.
  reflexivity.
Qed.