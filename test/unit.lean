import smt2

lemma fstar_goal_with_unit
(a b q : nat)
(prf_b : 0 < b)
(prf_q : 0 < q)
(p : unit → Prop)
(x : forall (x : unit), p x) : a = a :=
begin
    z3 "fst.log"
end
