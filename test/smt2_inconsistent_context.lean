import smt2
import .test_tactics

example (P : Prop) (p : P) (np : not P) : 3 < 1 :=
begin
    intros,
    must_fail z3
end
