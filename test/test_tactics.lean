import init.meta.tactic

universe u
axiom should_of_failed (A : Sort u) : A

meta def must_fail (tac : tactic unit) :=
do tactic.fail_if_success tac,
   tactic.refine ``(should_of_failed _)

constant configuration (A : Type u) : Type u

inductive astep (gvars : nat → nat) :
  ∀ {X : Type u}, configuration X → configuration X → list nat → Type (u+1)
| dummy : forall X conf ls, @astep X conf conf ls
