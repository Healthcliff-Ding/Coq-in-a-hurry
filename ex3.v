Theorem P1 : forall A : Set, forall P Q : A -> Prop,
  (forall x, P x) \/ (forall y, Q y) -> forall x, P x \/ Q x.
Proof.
  intros A0 P0 Q0.
  intros H.
  destruct H as [HP | HQ].
  left.
  apply HP.
  right.
  apply HQ.
Qed.

Theorem P2 : ~(forall A : Set, forall P Q : A -> Prop,
  (forall x, P x \/ Q x) -> (forall x, P x) \/ (forall y, Q y)).
Proof.
