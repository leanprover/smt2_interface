import smt2
import .test_tactics

lemma P_and_not_P_false (P : Prop) (p : P) (np : not P) : false :=
begin
    intros,
    z3
end
