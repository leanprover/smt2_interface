import smt2
import .test_tactics

lemma false_should_fail : false :=
by must_fail z3
