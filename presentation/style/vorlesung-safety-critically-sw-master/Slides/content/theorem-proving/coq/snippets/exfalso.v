Lemma false_proves_anything:
  forall (P: Prop), False -> P.
Proof.
  intros P f.
  exfalso.
  exact f.
Qed.