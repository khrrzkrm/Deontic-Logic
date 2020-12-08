Lemma not_not:
  forall (P: Prop), P -> ~(~P).
Proof.
  intros P p.
  intros H.
  apply H.
  exact p.
Qed.