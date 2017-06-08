import smt2

lemma true_is_true : true :=
begin
    z3 "true.log"
end
