(*  Propositions *)

Inductive even : nat -> Prop :=
| evenO : even O
| evenSS : forall n, even n -> even (S (S n)).

Lemma zero_even: even 0.
  exact evenO.
Qed.

Lemma two_even : even 2.
Proof.
  apply evenSS. apply evenO.
Qed.

Definition two_even' : even 2 :=
  evenSS O evenO.
