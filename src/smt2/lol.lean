import smt2.syntax
import smt2.builder

-- instance {α : Type} [decidable_eq α] : decidable_eq (list α)
-- | []     []      := is_true rfl
-- | (a::l) []      := is_false (λh, list.no_confusion h)
-- | []     (b::l') := is_false (λh, list.no_confusion h)
-- | (a::l) (b::l') :=
-- begin
--     refine (if ab : a = b then _ else _),
--     constructor,
--     rewrite ab,
-- end

def ordering.or_else : ordering → thunk ordering → ordering
| ordering.lt _ := ordering.lt
| ordering.eq f := f ()
| ordering.gt _ := ordering.gt

-- temp from mario's pr
instance fin.has_ordering (n : nat) : has_ordering (fin n) :=
⟨λ a b, nat.cmp a.1 b.1⟩

instance : has_ordering char :=
fin.has_ordering _

instance : has_ordering unsigned :=
fin.has_ordering _

def list.cmp {α : Type} [has_ordering α] : list α → list α → ordering
| []     []      := ordering.eq
| []     (b::l') := ordering.lt
| (a::l) []      := ordering.gt
| (a::l) (b::l') := (has_ordering.cmp a b).or_else (list.cmp l l')

instance {α : Type} [has_ordering α] : has_ordering (list α) :=
⟨list.cmp⟩
-- end temp

def string.cmp : string → string → ordering := list.cmp

instance : has_ordering string :=
⟨string.cmp⟩

namespace lol

inductive type
| bool : type
| int : type
| fn : list type → type → type

inductive term
-- TODO: eventually allow for term in head position, and generalize in trans
-- TODO: stratify this so that Prop > Ordering > Arith
| apply : string → list term → term
| true : term
| false : term
| var : string → term
| not : term → term
| equals : term → term → term
| and : term → term → term
| or : term → term → term
| iff : term → term → term
| implies : term → term → term
| add : term → term → term
| sub : term → term → term
| mul : term → term → term
| div : term → term → term
| lt : term → term → term
| lte : term → term → term
| gt : term → term → term
| gte : term → term → term
| int : int → term
| forallq : string → type → term → term

inductive decl
| fn : string → type → (option term) → decl

def decl.name : decl → string
| (decl.fn n _ _) := n

meta structure context :=
(type_decl : rb_map string type)
(decls : rb_map string decl)
(assertions : list term)

meta def context.empty : context :=
⟨ rb_map.mk _ _ , rb_map.mk _ _ , [] ⟩

meta def context.declare_type : context → string → type → context
| ⟨ type_decl, decls, assertions ⟩ n ty :=
match ty with
| type.fn _ _  := ⟨ type_decl.insert n ty,  decls, assertions ⟩
| _ := ⟨ type_decl, decls, assertions ⟩
end

meta def context.assert : context → term → context
| ⟨ type_decl, decls, assertions ⟩ t := ⟨ type_decl, decls, t :: assertions ⟩

meta def context.declare : context → decl → context
| ctxt decl :=
    { ctxt with decls := ctxt.decls.insert decl.name decl }

open smt2.builder

private meta def compile_type : type → smt2.sort
| (type.bool) := "Bool"
| (type.int) := "Int"
| (type.fn args ret) := "error"

private meta def compile_types : list (string × type) → smt2.builder unit
| [] := return ()
| ((n, ty) :: decls) :=
do match ty with
   | type.fn args ret :=
    -- TODO: fix me
      declare_sort n 0
   | type.int := return ()
   | type.bool := return ()
   end,
   compile_types decls.

private meta def split_fn_type : type → (list type × type)
| (type.bool) := ([], type.bool)
| (type.int) := ([], type.int)
| (type.fn args rt) := (args, rt)

private meta def compile_decl : decl → smt2.builder unit
| (decl.fn n ty none) :=
    let (args, rt) := split_fn_type ty
    in declare_fun n (list.map compile_type args) (compile_type rt)
| _ := return () -- TODO: fix me

private meta def compile_decls : list (string × decl) → smt2.builder unit
| [] := return ()
| ((n, d) :: rs) := do compile_decl d, compile_decls rs

private meta def compile_term : lol.term → smt2.builder smt2.term
| (term.apply t us) := smt2.term.apply t <$> monad.mapm compile_term us
| (term.true) := pure $ smt2.term.qual_id "true"
| (term.false) := pure $ smt2.term.qual_id "false"
| (term.var str) := pure $ smt2.term.qual_id str
| (term.not t) := smt2.builder.not <$> compile_term t
| (term.equals t u) := smt2.builder.equals <$> compile_term t <*> compile_term u
| (term.and t u) := smt2.builder.and2 <$> compile_term t <*> compile_term u
| (term.or t u) := smt2.builder.or2 <$> compile_term t <*> compile_term u
| (term.implies t u) := smt2.builder.implies <$> compile_term t <*> compile_term u
| (term.iff t u) := smt2.builder.iff <$> compile_term t <*> compile_term u
| (term.add a b) := smt2.builder.add <$> compile_term a <*> compile_term b
| (term.sub a b) := smt2.builder.sub <$> compile_term a <*> compile_term b
| (term.mul a b) := smt2.builder.mul <$> compile_term a <*> compile_term b
| (term.div a b) := smt2.builder.div <$> compile_term a <*> compile_term b
| (term.lt a b) := smt2.builder.lt <$> compile_term a <*> compile_term b
| (term.lte a b) := smt2.builder.lte <$> compile_term a <*> compile_term b
| (term.gt a b) := smt2.builder.gt <$> compile_term a <*> compile_term b
| (term.gte a b) := smt2.builder.gte <$> compile_term a <*> compile_term b
| (term.int i) := return $ smt2.builder.int_const i
| (term.forallq n ty body) := smt2.builder.forallq n (compile_type ty) <$> compile_term body

private meta def compile_assertions : list term → smt2.builder unit
| [] := return ()
| (t :: ts) :=
  do t' ← compile_term t,
     smt2.builder.assert t',
     compile_assertions ts

meta def compile (ctxt : context) : smt2.builder unit :=
do compile_types ctxt.type_decl.to_list,
   compile_decls ctxt.decls.to_list,
   compile_assertions ctxt.assertions

end lol
