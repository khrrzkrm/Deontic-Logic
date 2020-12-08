Inductive bool : Type :=
| true  : bool
| false : bool.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.