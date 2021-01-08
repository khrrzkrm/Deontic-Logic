Inductive or (A B: Prop) : Prop :=
  | or_introl : A -> or A B
  | or_intror : B -> or A B.
