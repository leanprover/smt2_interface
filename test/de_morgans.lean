import smt2

lemma negation_of_conj :
    forall (P Q : Prop),
        not (P ∧ Q) ↔ not P ∨ not Q :=
by intros; z3 "d1.log"

lemma negation_of_disj :
    forall (P Q : Prop),
        ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
    intros, z3
end
