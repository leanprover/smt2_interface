import smt2

lemma p_implies_p (P : Prop) : P → P :=
begin
    intros,
    z3 "p implies p"
end
