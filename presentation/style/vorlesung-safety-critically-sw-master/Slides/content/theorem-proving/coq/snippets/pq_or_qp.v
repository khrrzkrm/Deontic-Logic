Lemma pq_or_qp:
  forall (P Q: Prop), P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  destruct H as [p | q].
  - right. apply p.
  - left. apply q.
Qed.