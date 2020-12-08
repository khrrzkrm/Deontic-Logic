Inductive even : nat -> Prop :=
| evenO:  even O
| evenSS: forall (n: nat), even n ->
                      even (S(S n)).