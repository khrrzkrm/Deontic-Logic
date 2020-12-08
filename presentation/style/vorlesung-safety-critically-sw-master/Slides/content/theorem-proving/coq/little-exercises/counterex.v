Definition contrad: P :=
  fix f (P: Prop) := f P

Fixpoint prove_anything (P: Prop): P := prove_anything P.