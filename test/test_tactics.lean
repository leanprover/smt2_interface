import init.meta.tactic

meta def must_fail (tac : tactic unit) :=
do tactic.fail_if_success tac, tactic.admit
