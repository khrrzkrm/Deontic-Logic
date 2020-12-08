Inductive prod (A B:Type) : Type :=
  pair : A -> B -> prod A B.

Definition myprod: prod nat bool := pair nat bool 3 false.

Definition swap (A B: Type): prod A B -> prod B A :=
  fun p => match p with
           | pair _ _ a b => pair B A b a end.