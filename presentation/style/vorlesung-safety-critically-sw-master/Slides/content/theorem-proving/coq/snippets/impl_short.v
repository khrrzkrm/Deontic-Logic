Definition true_p:
  forall (P: Prop), P -> (True /\ P) :=
  fun P p => conj I p.