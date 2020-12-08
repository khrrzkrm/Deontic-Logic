Inductive weekday :=
| Mon | Tue | Wed | Thu | Fri | Sat | Sun.


Definition is_weekend (w: weekday): bool :=
  match w with | Sat => true
               | Sun => true
               | _ => false end.

Definition is_ (w: weekday): bool :=
  match w with | Sun => true
          | _ => false end.

