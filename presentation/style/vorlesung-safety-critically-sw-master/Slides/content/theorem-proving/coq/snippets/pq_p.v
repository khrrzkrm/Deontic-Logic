Lemma pq_p: forall (P Q: Prop), P /\ Q -> P.
Proof.
  intros P Q H.
  destruct H as [p q].
  apply p.
Qed.  