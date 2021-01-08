(*  Lists *)

Inductive True : Prop :=
  I : True.

Inductive False : Prop :=.

Inductive and (A B:Prop) : Prop :=
  conj : A -> B -> and A B.
