import init.meta.tactic

universe u
axiom should_of_failed (A : Sort u) : A

meta def must_fail (tac : tactic unit) :=
do tactic.fail_if_success tac,
   tactic.refine ``(should_of_failed _)
