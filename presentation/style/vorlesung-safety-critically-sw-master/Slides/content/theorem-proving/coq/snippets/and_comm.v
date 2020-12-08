Lemma and_comm:
  forall (P Q: Prop), P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  destruct H as [p q].
  split.
  - apply q.
  - apply p.
Qed.