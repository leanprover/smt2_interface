import smt2

lemma refl_should_pass (x : int) : x = x :=
by z3
