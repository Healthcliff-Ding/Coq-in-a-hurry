Theorem P1 : forall A B C : Prop, A/\(B/\C) -> (A/\B)/\C.
Proof.
  intros A0 B0 C0.
  intros H.
  split.
  destruct H.
  destruct H0.
  split.
  apply H.
  apply H0.
  destruct H as [HA HB].
  destruct HB as [HB HC].
  apply HC.
Qed.

Theorem P2 : forall A B C D : Prop, (A->B) /\ (C->D) /\ A /\ C -> B /\ D.
Proof.
  intros A0 B0 C0 D0.
  intros H.
  destruct H.
  destruct H0.
  destruct H1.
  split.
  apply H.
  apply H1.
  apply H0.
  apply H2.
Qed.

Theorem P3 : forall A : Prop, ~(A /\ ~A).
Proof.
  intros A0.
  intro C.
  elim C.
  intros.
  elim H0.
  apply H.
Qed.

Theorem P4 : forall A B C : Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
  intros A0 B0 C0.
  intros H.
  elim H.
  left.
  left.
  apply H0.
  intros H0.
  elim H0.
  intros HB.
  left.
  right.
  apply HB.
  intro HC.
  right.
  apply HC.
Qed.
