Definition true_p:
  forall (P: Prop), P -> (True /\ P) :=
  fun (P: Prop) (p: P) => conj I p.