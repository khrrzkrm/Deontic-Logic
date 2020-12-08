Lemma O_plus_n: forall (n: nat), 0 +n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.