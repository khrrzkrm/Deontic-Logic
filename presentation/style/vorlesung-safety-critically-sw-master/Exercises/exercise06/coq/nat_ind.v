Inductive even : nat -> Prop :=
| evenO: even O
| evenSS: forall (n: nat), even n ->
                      even (S(S n)).

Lemma plus_assoc: forall (a b c: nat), (a + b) + c = a + (b + c).
Proof.
  intros a b c. induction a.
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite IHa.
    reflexivity.
Qed.