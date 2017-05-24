import smt2
import .test_tactics

example (P Q : Prop) : P -> Q :=
begin
    intros,
    must_fail z3
end
