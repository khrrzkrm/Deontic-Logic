Set Implicit Arguments.
Set Contextual Implicit.
Inductive list (X: Type) : Type :=
| nil:  list X
| cons: X -> list X -> list X.