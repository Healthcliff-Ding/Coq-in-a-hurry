Inductive bin : Set :=
  L : bin
| N : bin -> bin -> bin.

Check bin_ind.

Definition example3 (t : bin): bool :=
  match t with N L L => false | _ => true end.

Fixpoint flatten_aux (t1 t2:bin) {struct t1} : bin :=
  match t1 with
    L => N L t2
  | N t'1 t'2 => flatten_aux t'1 (flatten_aux t'2 t2)
  end.

Fixpoint flatten (t:bin) : bin :=
  match t with
    L => L
  | N t1 t2 => flatten_aux t1 (flatten t2)
  end.

Fixpoint size (t:bin) : nat :=
  match t with
    L => 1
  | N t1 t2 => 1 + size t1 + size t2
  end.

Theorem example3_size :
  forall t, example3 t = false -> size t = 3.

Proof.
intros t.
destruct t.
simpl.
intros H.
discriminate H.
destruct t1.
destruct t2.
auto.
intros H.
discriminate H.
intros H.
discriminate H.
Qed.