Inductive list : Type -> Type :=
| nil:  forall (X: Type), list X
| cons: forall (X: Type), X -> list X -> list X.