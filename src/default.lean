import system.io
import .solvers.z3
import .syntax
import .builder
import .tactic
import .attributes
import init.data.option.basic

declare_trace smt2

open tactic
open smt2.builder

meta structure smt2_state : Type :=
(sort_map : rb_map expr smt2.sort)

meta def smt2_state.initial : smt2_state :=
⟨ rb_map.mk _ _ ⟩

@[reducible] meta def smt2_m (α : Type) :=
state_t smt2_state tactic α

meta instance tactic_to_smt2_m (α : Type) : has_coe (tactic α) (smt2_m α) :=
⟨ fun tc, fun s, do res ← tc, return (res, s) ⟩

namespace smt2

meta def trace_smt2 (msg : string) : smt2_m unit :=
  tactic.when_tracing `smt2 (tactic.trace msg)

meta def fail {α : Type} (msg : string) : smt2_m α :=
tactic.fail $ "smt2_tactic: " ++ msg

meta def mangle_name (n : name) : string :=
"lean_" ++ n^.to_string_with_sep "-"

meta def ensure_sort (exp : expr) (mk_sort : smt2_m sort) : smt2_m sort :=
do st ← state_t.read,
   match st.sort_map.find exp with
   | some s := return s
   | none := do
     s ← mk_sort,
     state_t.write (⟨ st.sort_map.insert exp s ⟩),
     return s
   end

inductive formula_type
| const : name → smt2.sort → formula_type
| fn : name → list smt2.sort → smt2.sort → formula_type
| prop_formula
| unsupported

-- FIXME
meta def fn_type : expr → (list expr × expr)
| (expr.pi _ _ ty rest) :=
    let (args, rt) := fn_type rest
    in (ty :: args, rt)
| rt := ([], rt)

meta def type_to_sort (e : expr) : smt2_m smt2.sort :=
if (e = ```(int))
then return $ "Int"
else if (e = ```(Prop))
then return $ "Bool"
else if (e = ```(int))
then return $ "Int"
-- NB: This case for nat is kind of hack, we will treat this sort later as actually an Int and add constraints
-- I think we should change the code to map from expr -> (sort, id -> builder unit), essentially
-- each Lean becomes a z3 sort and a set of constraints true for every variable.
-- This makes it possible to elaborate refinements into primitive z3 sorts and a set of constraints
-- this should make it possible to handle classes of refinments, mapping types to integers, etc.
else if (e = ```(nat))
then return $ "Nat"
else if e.is_local_constant
then return $ (mangle_name e.local_uniq_name)
else if e.is_constant
then ensure_sort e (return $ mangle_name e.const_name)
else fail $ "unsupported type `" ++ to_string e ++ "`"

meta def formula_type_from_arrow (n : name) (e : expr) : smt2_m formula_type :=
do ty ← infer_type e,
   let (arg_tys, ret_ty) := fn_type ty
   in formula_type.fn n <$> (monad.mapm type_to_sort arg_tys) <*> (type_to_sort ret_ty)

/-- The goal of this function is to categorize the set of formulas in the hypotheses,
    and goal. We want to narrow down from the full term language of Lean to a fragment
    of formula's we suppose. The below code makes some assumptions:

   A local constant of the form `(P : Prop)`, must be reflected as declaration
   in SMT2 that is `(declare-const P Bool)`.

   An occurence of a proof of `P`, `(p : P)`, must be transformed into
   `(assert P)`. If P is a formula, not an atom, we must transform P into a corresponding
   SMT2 formula and `(assert P)`.
-/
meta def classify_formula (e : expr) : smt2_m formula_type :=
do ty ← infer_type e,
   prop_sorted ← is_prop ty,
   if e.is_local_constant
   then if (ty = ```(Prop))
        then return $ formula_type.const (e.local_uniq_name) "Bool"
        else if (ty = ```(int))
        then return $ formula_type.const (e.local_uniq_name) "Int"
        else if (ty = ```(nat))
        then return $ formula_type.const (e.local_uniq_name) "Nat"
        else if ty.is_arrow
        then formula_type_from_arrow (e.local_uniq_name) e
        else if prop_sorted
        then return formula_type.prop_formula
        else return formula_type.unsupported
   else if e.is_constant
   then if (ty = ```(Prop))
        then return $ formula_type.const (e.const_name) "Bool"
        else if (ty = ```(int))
        then return $ formula_type.const (e.const_name) "Int"
        else if (ty = ```(nat))
        then return $ formula_type.const (e.local_uniq_name) "Nat"
        else if ty.is_arrow
        then formula_type_from_arrow (e.const_name) e
        else if prop_sorted
        then return formula_type.prop_formula
        else return formula_type.unsupported
   else if (ty = ```(Prop))
   then return formula_type.prop_formula
   else return formula_type.unsupported

-- meta def is_supported_head_symbol (e : expr) : bool :=
-- if

meta def extract_coe_args (args : list expr) : smt2_m (expr × expr × expr) :=
match args with
| (source :: target :: inst :: e :: []) := return (source, target, e)
| _ := fail "internal tactic error expected `coe` to have exactly 4 arguments"
end

meta def reflect_coercion (source target e : expr) (callback : expr → smt2_m term) : smt2_m term :=
if source = ```(nat) /\ target = ```(int)
then callback e
else fail $ "unsupported coercion between " ++ "`" ++ to_string source ++ "` and `" ++ to_string target ++ "`"

meta def reflect_application (fn : expr) (args : list expr) (callback : expr → smt2_m term) : smt2_m term :=
    if fn.is_constant
    then if fn.const_name = `coe
          then do (source, target, e) ← extract_coe_args args,
                   reflect_coercion source target e callback
          else term.apply (mangle_name fn.const_name) <$> monad.mapm callback args
    else if fn.is_local_constant
    then term.apply (mangle_name fn.local_uniq_name) <$> monad.mapm callback args
    else fail $ "unsupported head symbol `" ++ to_string fn ++ "`"

meta def is_supported_head_symbol (e : expr) : bool := true

/-- This function is the meat of the tactic, it takes a propositional formula in Lean, and transforms
   it into a corresponding term in SMT2. -/
meta def reflect_arith_formula (reflect_base : expr → smt2_m term) : expr → smt2_m term
| ```(%%a + %%b) := smt2.builder.add <$> reflect_arith_formula a <*> reflect_arith_formula b
| ```(%%a - %%b) := smt2.builder.sub <$> reflect_arith_formula a <*> reflect_arith_formula b
| ```(%%a * %%b) := smt2.builder.mul <$> reflect_arith_formula a <*> reflect_arith_formula b
| ```(%%a / %%b) := smt2.builder.div <$> reflect_arith_formula a <*> reflect_arith_formula b
/- Constants -/
| ```(has_zero.zero) := smt2.builder.int_const <$> eval_expr int ```(has_zero.zero int)
| ```(has_one.one) := smt2.builder.int_const <$> eval_expr int ```(has_one.one int)
| ```(bit0 %%Bits) :=
  do ty ← infer_type Bits,
     if (ty = ```(int))
     then smt2.builder.int_const <$> eval_expr int ```(bit0 %%Bits : int)
     else if (ty = ```(nat))
     then smt2.builder.int_const <$> int.of_nat <$> eval_expr nat ```(bit0 %%Bits : nat)
     else fail $ "unknown numeric literal: " ++ (to_string ```(bit0 %%Bits : int))
| ```(bit1 %%Bits) :=
  do ty ← infer_type Bits,
     if (ty = ```(int))
     then smt2.builder.int_const <$> eval_expr int ```(bit1 %%Bits : int)
     else if (ty = ```(nat))
     then smt2.builder.int_const <$> (int.of_nat <$> eval_expr nat ```(bit1 %%Bits : nat))
     else fail $ "unknown numeric literal: " ++ (to_string ```(bit1 %%Bits : int))
| a :=
    if a.is_local_constant
    then return $ term.qual_id (mangle_name a.local_uniq_name)
    else if a.is_constant
    then return $ term.qual_id (mangle_name a.const_name)
    else if a.is_app
    then reflect_application (a.get_app_fn) (a.get_app_args) reflect_base
    else fail $ "unsupported arithmetic formula: " ++ to_string a

/-- Check if the type is an `int` or logically a subtype of an `int` like nat. -/
meta def is_int (e : expr) : tactic bool :=
do ty ← infer_type e,
   return $ (ty = ```(int)) || (ty = ```(nat))

meta def unsupported_ordering_on {α : Type} (elem : expr) : tactic α :=
do ty ← infer_type elem,
   tactic.fail $ "unable to translate orderings for values of type: " ++ to_string ty

-- I apologize for these crazy callbacks, we need a mutual keyword or section.
meta def reflect_ordering (reflect_arith : expr → smt2_m term) (R : term → term → term) (P Q : expr) : smt2_m term :=
do is ← is_int P, -- NB: P and Q should have the same type.
   if is
   then R <$> (reflect_arith P) <*> (reflect_arith Q)
   else unsupported_ordering_on P

meta def reflect_prop_formula' : expr → smt2_m term
| ```(¬ %%P) := not <$> (reflect_prop_formula' P)
| ```(%%P = %% Q) := smt2.builder.equals <$> (reflect_prop_formula' P) <*> (reflect_prop_formula' Q)
| ```(%%P ∧ %%Q) := smt2.builder.and2 <$> (reflect_prop_formula' P) <*> (reflect_prop_formula' Q)
| ```(%%P ∨ %%Q) := smt2.builder.or2 <$> (reflect_prop_formula' P) <*> (reflect_prop_formula' Q)
| ```(%%P ↔ %%Q) := smt2.builder.iff <$> (reflect_prop_formula' P) <*> (reflect_prop_formula' Q)
| ```(%%P < %%Q) := reflect_ordering (reflect_arith_formula reflect_prop_formula') smt2.builder.lt P Q
| ```(%%P <= %%Q) := reflect_ordering (reflect_arith_formula reflect_prop_formula') smt2.builder.lte P Q
| ```(%%P > %%Q) := reflect_ordering (reflect_arith_formula reflect_prop_formula') smt2.builder.gt P Q
| ```(%%P >= %%Q) := reflect_ordering (reflect_arith_formula reflect_prop_formula') smt2.builder.gte P Q
| e := if e.is_local_constant
       then return $ term.qual_id (mangle_name e.local_uniq_name)
       else if e = ```(int)
       then return "Int"
       else (do
         ty ← infer_type e,
         tactic.trace $ "expr: " ++ to_string e ++ ", inferred_type: " ++ to_string ty,
         if (ty = ```(int))
         then (do tactic.trace "arith", reflect_arith_formula reflect_prop_formula' e)
         else if e.is_arrow
         then (do tactic.trace "arrow" ,implies <$> (reflect_prop_formula' e.binding_domain) <*> (reflect_prop_formula' e.binding_body ))
         else if e.is_pi
         then do loc ← tactic.mk_local' e.binding_name e.binding_info e.binding_domain,
                 tactic.trace $ (expr.instantiate_var (e.binding_body) loc),
                 forallq (mangle_name $ loc.local_uniq_name) <$>
                      -- TODO: fix this
                      (type_to_sort $ e.binding_domain) <*>
                      (reflect_prop_formula' (expr.instantiate_var (e.binding_body) loc))
         else if e.is_app
         then do let fn := e.get_app_fn,
               let args := e.get_app_args,
            --    tactic.trace $ "app case: " ++ to_string e,
            --    tactic.trace $ "app case fn: " ++ to_string fn,
            --    tactic.trace $ "app case args: " ++ to_string args,
               -- we should probably relax for top-level constants which have already been translated
               if fn.is_local_constant
               then do args' ← monad.mapm reflect_prop_formula' args,
                       tactic.trace $ "arguments: " ++ args.to_string,
                       pure $ smt2.term.apply (mangle_name fn.local_uniq_name) args'
               else tactic.fail "can only handle fn constants right now"
          else tactic.fail $ "unsupported propositional formula : " ++ to_string e)

meta def reflect_prop_formula (e : expr) : smt2_m (builder unit) :=
do ty ← infer_type e,
   form ← reflect_prop_formula' ty,
   return $ assert form

meta def reflect_local (e : expr) : smt2_m (builder unit) :=
do ft ← classify_formula e,
   match ft with
   | formula_type.const n (sort.id "Bool") :=
     return $ declare_const (mangle_name n) "Bool"
   | formula_type.const n (sort.id "Int") :=
     return $ declare_const (mangle_name n) "Int"
   -- NB: This is the other part of the above mentioned hack
   | formula_type.const n (sort.id "Nat") :=
     let mn := mangle_name n,
         zero := has_zero.zero int
     in return $ do
       declare_const mn "Int",
       assert (smt2.builder.lte zero mn)
   | formula_type.fn n ps rs :=
     return $ declare_fun (mangle_name n) ps rs
   | formula_type.prop_formula :=
     reflect_prop_formula e
   | _ := return (return ())
   end

meta def reflect_context : smt2_m (builder unit) :=
do ls ← local_context,
   bs ← monad.mapm reflect_local ls,
   return $ list.foldl (λ (a b : builder unit), a >> b) (return ()) bs

meta def reflect_attr_decl (n : name) : smt2_m (builder unit) :=
do tactic.trace (to_string n),
   exp ← mk_const n,
   reflect_local exp

/- Reflect the environment consisting of declarations with the `smt2` attribute. -/
meta def reflect_environment : smt2_m (builder unit) :=
do decls ← attribute.get_instances `smt2,
   bs ← monad.mapm reflect_attr_decl decls.reverse,
   return $ (monad.sequence bs >> return ())

meta def reflect_goal : smt2_m (builder unit) :=
do tgt ← target,
   ft ← classify_formula tgt,
   -- tactic.trace ("target: " ++ tgt.to_string),
   match ft with
   | formula_type.const n (sort.id "Bool") :=
      return $ assert (not $ mangle_name n)
   | formula_type.prop_formula :=
      do form ← reflect_prop_formula' tgt,
         return $ assert (not form)
   | _ := fail "unsupported goal"
   end

-- meta def mk_prelude : builder unit :=
--   do declare_sort "unit" 0,
--      declare_fun

meta def reflect : smt2_m (builder unit) :=
do env_builder ← reflect_environment,
   ctxt_builder ← reflect_context,
   goal_builder ← reflect_goal,
   return $ env_builder >> ctxt_builder >> goal_builder >> check_sat

end smt2

meta def z3 (log_file : option string := none) : tactic unit :=
do (builder, _) ← smt2.reflect smt2_state.initial,
   resp ← run_io (λ ioi, @smt2 ioi builder log_file),
   match resp with
   | smt2.response.sat := fail "z3 was unable to prove the goal"
   | smt2.response.unknown := fail "z3 was unable to prove the goal"
   | smt2.response.other str := fail $ "communication error encountered unexpected response: `" ++ str ++ "`"
   | smt2.response.unsat := do
        tgt ← target,
        fresh_name ← mk_fresh_name,
        let axiom_name := name.mk_string "z3" (name.mk_string "axioms" fresh_name),
        -- TODO: generate a minimal unique axiom for each application of the tactic, add_decl (declaration.ax axiom_name [] tgt)
        sry ← to_expr $ `(sorry),
        exact sry
   end
