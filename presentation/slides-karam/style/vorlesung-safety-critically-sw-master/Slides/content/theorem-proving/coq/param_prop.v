Definition t_or_p: forall (P: Prop), True \/ P :=
  fun (_: Prop) => or_introl I.