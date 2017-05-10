inductive format_string
| const : string -> format_string
| int : format_string
| void : format_string

def format_string.to_string : format_string → string
| (format_string.const str) := str
| format_string.int := "%d"
| format_string.void := ""

instance : has_to_string format_string :=
⟨ format_string.to_string ⟩

@[reducible] def token_step (next_char : char) : (list format_string × string) -> (list format_string × string)
| (ts, "%") :=
match next_char with
| 'd' := (format_string.int :: ts, "")
| _ := (ts, "%" ++ [next_char])
end
| (ts, str) :=
match next_char with
| '%' := (format_string.const str :: ts, "%")
| _ := (ts, str ++ [next_char])
end

@[reducible] def tokenize (s : string) : list format_string :=
  let (ts, rest) := list.foldl (fun ts c, token_step c ts) ([], "") s.reverse
  in (format_string.const rest :: ts).reverse

#eval (tokenize "fooo %d bar")

-- def to_format_string (s : string) : format_string :=
--   let ts := tokenize s in
--   list.foldl (fun a b, format_string.seq a b) format_string.void ts

@[reducible] def format_str_to_type : format_string -> Type
| (format_string.const str) := empty
| format_string.int := int
| format_string.void := string

def is_not_const : format_string -> bool
| (format_string.const _) := false
| _ := true

@[reducible] def format_str_type (s : string) : Type :=
let tp := list.filter (fun x, is_not_const x) (tokenize s)
in list.foldr (fun (a b : Type), a -> b) string (list.map format_str_to_type tp)

-- attribute [reducible] list.reverse list.reverse_core list.foldl list.foldr

example : format_str_type "%d" = (int -> string) :=
begin
    reflexivity,
end

def printf (format_str : string) : format_str_type format_str := sorry

#check (let str : string := (printf "%d %d") (10 : int) (10 : int) in str)
