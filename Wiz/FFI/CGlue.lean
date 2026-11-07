import Wiz.FFI.CParse

/-!
# Checked C glue

`glue f (x : Nat) … : T := "C statements"` defines a foreign function by a C body, in
a **restricted subset of C** that is checked before it is emitted: the snippet can
compute with numbers and strings and call C functions that headers declare
(`import_c`), but it can't touch memory directly. No pointer dereference or address-of,
no casts, no indexing or member access, no `goto`, `asm` or `sizeof`. Strings
(`const char *`) can only be passed around. So a glue snippet can't break the memory
safety of the rest of the program (beyond what the C functions it calls do).

    stmt := type x [= expr] ; | x (= | += | -= | *= | /= | %=) expr ; | x++ ; | x-- ;
          | if (expr) stmt [else stmt] | while (expr) stmt | for (stmt expr ; step) stmt
          | { stmt* } | return expr ; | break ; | continue ; | call ;
    expr := literal | x | call | unary expr | expr binop expr | expr ? expr : expr | (expr)
-/

namespace Wiz.FFI

/-- The types of the subset: integers, doubles and strings. -/
inductive GTy where
  | int | dbl | str | void
  deriving BEq, Repr, Inhabited

def GTy.ofC : CType → Option GTy
  | .const t => GTy.ofC t
  | .int _ => some .int
  | .float _ => some .dbl
  | .void => some .void
  | .ptr t => match t with
    | .int "char" | .const (.int "char") => some .str
    | _ => none
  | .other _ => none

def GTy.show : GTy → String
  | .int => "an integer" | .dbl => "a double" | .str => "a string" | .void => "void"

/-- Type names allowed for locals. -/
def localTypes : List (List String × GTy) :=
  [(["int"], .int), (["long"], .int), (["unsigned"], .int), (["uint64_t"], .int), (["int64_t"], .int),
   (["size_t"], .int), (["unsigned", "long"], .int), (["long", "long"], .int), (["double"], .dbl),
   (["const", "char", "*"], .str)]

structure GState where
  toks : Array String
  pos : Nat := 0
  vars : List (String × GTy)
  funcs : List (String × List GTy × GTy)
  ret : GTy

abbrev G := StateT GState (Except String)

def gpeek : G String := do let s ← get; pure (s.toks[s.pos]?.getD "")
def gnext : G String := do let t ← gpeek; modify fun s => { s with pos := s.pos + 1 }; pure t
def expect (t : String) : G Unit := do
  let u ← gnext
  unless u == t do throw s!"expected '{t}', found '{u}'"

def forbidden : List String := ["goto", "asm", "__asm__", "sizeof", "->", "[", "&", "struct", "union", "malloc", "free"]

def isIdent (t : String) : Bool := t != "" && (t.front.isAlpha || t.front == '_')
def isNumber (t : String) : Bool := t != "" && t.front.isDigit

def binops : List (List String) :=
  [["||"], ["&&"], ["|"], ["^"], ["&"], ["==", "!="], ["<", "<=", ">", ">="], ["<<", ">>"], ["+", "-"], ["*", "/", "%"]]

/-- Two-character operators, glued from the tokenizer's single characters. -/
def joinOps (ts : Array String) : Array String := Id.run do
  let two := ["==", "!=", "<=", ">=", "&&", "||", "<<", ">>", "+=", "-=", "*=", "/=", "%=", "++", "--", "->"]
  let mut out := #[]
  let mut i := 0
  while i < ts.size do
    let t := ts[i]!
    let u := ts[i + 1]?.getD ""
    if two.contains (t ++ u) then out := out.push (t ++ u); i := i + 2
    else out := out.push t; i := i + 1
  pure out

mutual

/-- **Exercise 9.2.** Check an expression and return its type. Integers and doubles mix
(the result is a double); strings only appear as themselves (a literal, a variable, a
call returning one) and as arguments of matching type; comparisons and logic give
integers. Anything in `forbidden` (or a unary `*`) is an error. -/
partial def expr (prec : Nat := 0) : G GTy := do
  sorry

partial def unary : G GTy := do
  let t ← gpeek
  if forbidden.contains t then throw s!"'{t}' is not allowed in glue code"
  if t == "*" then throw "pointer dereference is not allowed in glue code"
  if t == "-" || t == "!" || t == "~" then
    let _ ← gnext
    let a ← unary
    if a == .str then throw s!"'{t}' needs a number"
    return (if t == "-" then a else .int)
  primary

partial def primary : G GTy := do
  let t ← gnext
  if t == "(" then
    -- a cast would start with a type name
    let nxt ← gpeek
    if localTypes.any (fun (ws, _) => ws.head? == some nxt) then throw "casts are not allowed in glue code"
    let a ← expr
    expect ")"
    return a
  if t.startsWith "\"" then return .str
  if t.startsWith "'" then return .int
  if isNumber t then return (if t.contains '.' || t.contains 'e' then .dbl else .int)
  if !isIdent t then throw s!"unexpected '{t}'"
  if (← gpeek) == "(" then
    let s ← get
    let some (_, ps, r) := s.funcs.find? (·.1 == t) | throw s!"unknown C function {t} (import its header with import_c)"
    let _ ← gnext
    let mut args := #[]
    while (← gpeek) != ")" do
      args := args.push (← expr)
      if (← gpeek) == "," then let _ ← gnext
    let _ ← gnext
    unless args.size == ps.length do throw s!"{t} takes {ps.length} arguments, not {args.size}"
    for a in args, p in ps do
      unless a == p || (a != .str && p != .str) do throw s!"{t}: expected {p.show}, got {a.show}"
    return r
  match (← get).vars.lookup t with
  | some ty =>
    let nxt ← gpeek
    if nxt == "[" || nxt == "." || nxt == "->" then throw s!"'{nxt}' (indexing or member access) is not allowed in glue code"
    pure ty
  | none => throw s!"unknown variable {t}"

end

partial def stmt : G Unit := do
  let t ← gpeek
  if forbidden.contains t then throw s!"'{t}' is not allowed in glue code"
  if t == "{" then
    let _ ← gnext
    let saved := (← get).vars
    while (← gpeek) != "}" do
      if (← gpeek) == "" then throw "missing '}'"
      stmt
    let _ ← gnext
    modify fun s => { s with vars := saved }
  else if t == "if" || t == "while" then
    let _ ← gnext; expect "("
    let c ← expr
    if c == .str then throw s!"the condition of {t} must be a number"
    expect ")"
    stmt
    if t == "if" && (← gpeek) == "else" then let _ ← gnext; stmt
  else if t == "for" then
    let _ ← gnext; expect "("
    let saved := (← get).vars
    if (← gpeek) == ";" then let _ ← gnext else stmt
    if (← gpeek) != ";" then let _ ← expr
    expect ";"
    if (← gpeek) != ")" then simple
    expect ")"
    stmt
    modify fun s => { s with vars := saved }
  else if t == "return" then
    let _ ← gnext
    let r := (← get).ret
    if r == .void then expect ";" else
      let a ← expr
      unless a == r || (a != .str && r != .str) do throw s!"return: expected {r.show}, got {a.show}"
      expect ";"
  else if t == "break" || t == "continue" then let _ ← gnext; expect ";"
  else
    -- a declaration?
    let s ← get
    let rest := (s.toks.extract s.pos (s.pos + 3)).toList
    match localTypes.find? fun (ws, _) => rest.take ws.length == ws with
    | some (ws, ty) =>
      for _ in ws do let _ ← gnext
      let x ← gnext
      unless isIdent x do throw s!"expected a variable name, found '{x}'"
      if (← gpeek) == "=" then
        let _ ← gnext
        let a ← expr
        unless a == ty || (a != .str && ty != .str) do throw s!"{x}: expected {ty.show}, got {a.show}"
      modify fun s => { s with vars := (x, ty) :: s.vars }
      expect ";"
    | none => simple; expect ";"
where
  /-- assignment, increment, or a call -/
  simple : G Unit := do
    let x ← gpeek
    let op := (← get).toks[(← get).pos + 1]?.getD ""
    if ["=", "+=", "-=", "*=", "/=", "%="].contains op then
      let _ ← gnext; let _ ← gnext
      let some ty := (← get).vars.lookup x | throw s!"unknown variable {x}"
      let a ← expr
      unless a == ty || (a != .str && ty != .str) do throw s!"{x}: expected {ty.show}, got {a.show}"
      if ty == .str && op != "=" then throw s!"'{op}' needs numbers"
    else if op == "++" || op == "--" then
      let _ ← gnext; let _ ← gnext
      if (← get).vars.lookup x != some .int then throw s!"'{op}' needs an integer variable"
    else let _ ← expr

/-- Check a glue body: the parameters and functions in scope, and the return type. -/
def checkGlue (body : String) (params : List (String × GTy)) (funcs : List (String × List GTy × GTy)) (ret : GTy) :
    Except String Unit := do
  let toks := joinOps (tokenize body)
  let ((), s) ← (do while (← gpeek) != "" do stmt : G Unit).run { toks, vars := params, funcs, ret }
  let _ := s
  pure ()

end Wiz.FFI
