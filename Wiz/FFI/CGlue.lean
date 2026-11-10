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

(9i) Structs: a glue function may take and return C structs (`c_struct`, or a struct of
an imported header) by value, declare struct locals (`struct timespec t;`, only of
structs whose fields are all numbers, so an uninitialised one holds no pointers), read
and assign their fields (`t.tv_sec`), and pass the address of a struct local or
parameter, `&t`, but only directly as the argument of a C function that takes a
pointer to that struct. Nothing else may take an address.

    stmt := type x [= expr] ; | x (= | += | -= | *= | /= | %=) expr ; | x++ ; | x-- ;
          | if (expr) stmt [else stmt] | while (expr) stmt | for (stmt expr ; step) stmt
          | { stmt* } | return expr ; | break ; | continue ; | call ;
    expr := literal | x | call | unary expr | expr binop expr | expr ? expr : expr | (expr)
-/

namespace Wiz.FFI

/-- The types of the subset: integers, doubles and strings. -/
inductive GTy where
  | int | dbl | str | void
  /-- an opaque foreign pointer: it can only be passed on -/
  | ptr
  /-- (9i) a struct by value, by its C spelling -/
  | struct (spelling : String)
  /-- (9i) a pointer to a struct: `&x` of a struct variable, or a foreign pointer -/
  | sptr (spelling : String)
  /-- (9i) `&x` of a struct variable: only an argument for a matching `sptr` parameter -/
  | addr (spelling : String)
  deriving BEq, Repr, Inhabited

def GTy.ofC : CType → Option GTy
  | .const t => GTy.ofC t
  | .int _ => some .int
  | .float _ => some .dbl
  | .void => some .void
  | .ptr t => match t with
    | .int "char" | .const (.int "char") => some .str
    | .struct sp | .const (.struct sp) => some (.sptr sp)
    | _ => some .ptr
  | .struct sp => some (.struct sp)
  | .array .. => none
  | .other _ => none

def GTy.show : GTy → String
  | .int => "an integer" | .dbl => "a double" | .str => "a string" | .void => "void" | .ptr => "a pointer"
  | .struct sp => sp | .sptr sp => s!"a pointer to {sp}" | .addr sp => s!"the address of a {sp}"

def GTy.isNum : GTy → Bool | .int | .dbl => true | _ => false

/-- Is a value of type `a` accepted where `b` is expected? Numbers mix; a foreign pointer
goes where a struct pointer is expected (and back); the address of a struct variable only
where a pointer to that struct is; everything else must match. -/
def GTy.fits (a b : GTy) : Bool :=
  match a, b with
  | .addr x, .sptr y => x == y
  | .addr _, _ => false
  | .ptr, .sptr _ | .sptr _, .ptr => true
  | _, _ => a == b || (a.isNum && b.isNum)


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
  /-- (9i) the structs in scope, by spelling: their fields -/
  structs : List (String × List (String × GTy)) := []

abbrev G := StateT GState (Except String)

def gpeek : G String := do let s ← get; pure (s.toks[s.pos]?.getD "")
def gnext : G String := do let t ← gpeek; modify fun s => { s with pos := s.pos + 1 }; pure t
def expect (t : String) : G Unit := do
  let u ← gnext
  unless u == t do throw s!"expected '{t}', found '{u}'"

def forbidden : List String := ["goto", "asm", "__asm__", "sizeof", "->", "[", "&", "union", "malloc", "free"]

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
  --<sol
  let mut lhs ← unary
  repeat
    let t ← gpeek
    if t == "?" then
      if prec > 0 then break
      let _ ← gnext
      let a ← expr
      expect ":"
      let b ← expr
      unless lhs.isNum do throw "the condition of ?: must be a number"
      unless a.fits b || b.fits a do throw s!"the branches of ?: have different types"
      lhs := if !(a.isNum && b.isNum) then a else if a == .dbl || b == .dbl then .dbl else .int
      continue
    let some lvl := binops.findIdx? (·.contains t) | break
    if lvl < prec then break
    let _ ← gnext
    let rhs ← expr (lvl + 1)
    unless lhs.isNum && rhs.isNum do throw s!"'{t}' needs numbers"
    lhs := if lvl ≤ 6 then .int else if lhs == .dbl || rhs == .dbl then .dbl else .int
  pure lhs
  --|ex
  --| sorry
  --sol>

partial def unary : G GTy := do
  let t ← gpeek
  if forbidden.contains t then throw s!"'{t}' is not allowed in glue code"
  if t == "*" then throw "pointer dereference is not allowed in glue code"
  if t == "-" || t == "!" || t == "~" then
    let _ ← gnext
    let a ← unary
    unless a.isNum do throw s!"'{t}' needs a number"
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
      -- (9i) `&x` of a struct variable, only as an argument
      if (← gpeek) == "&" then
        let _ ← gnext
        let x ← gnext
        match (← get).vars.lookup x with
        | some (.struct sp) =>
          if (← gpeek) != "," && (← gpeek) != ")" then throw "'&' only takes the address of a whole struct variable"
          args := args.push (.addr sp)
        | _ => throw "'&' is only allowed on a struct variable, as the argument of a C function"
      else
        args := args.push (← expr)
      if (← gpeek) == "," then let _ ← gnext
    let _ ← gnext
    unless args.size == ps.length do throw s!"{t} takes {ps.length} arguments, not {args.size}"
    for a in args, p in ps do
      unless a.fits p do throw s!"{t}: expected {p.show}, got {a.show}"
    return r
  match (← get).vars.lookup t with
  | some ty =>
    let ty ← members ty
    let nxt ← gpeek
    if nxt == "[" || nxt == "." || nxt == "->" then throw s!"'{nxt}' (indexing or member access) is not allowed in glue code"
    pure ty
  | none => throw s!"unknown variable {t}"

/-- (9i) Field accesses `.f` after a struct-valued variable. -/
partial def members (ty : GTy) : G GTy := do
  match ty with
  | .struct sp =>
    if (← gpeek) != "." then return ty
    let _ ← gnext
    let f ← gnext
    let some fs := (← get).structs.lookup sp | throw s!"the fields of {sp} are not known"
    let some fty := fs.lookup f | throw s!"{sp} has no field {f}"
    members fty
  | _ => pure ty

end

/-- Are all fields numbers (in nested structs too)? -/
def allNumbers (structs : List (String × List (String × GTy))) : List (String × GTy) → Nat → Bool
  | _, 0 => false
  | fs, fuel + 1 => fs.all fun (_, t) => match t with
    | .int | .dbl => true
    | .struct sp => allNumbers structs ((structs.lookup sp).getD []) fuel
    | _ => false

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
    unless c.isNum do throw s!"the condition of {t} must be a number"
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
      unless a.fits r do throw s!"return: expected {r.show}, got {a.show}"
      expect ";"
  else if t == "break" || t == "continue" then let _ ← gnext; expect ";"
  else
    -- a declaration?
    let s ← get
    let rest := (s.toks.extract s.pos (s.pos + 3)).toList
    -- (9i) a struct local: `struct t x` or `t_name x`
    let structLocal : Option (List String × GTy) :=
      match rest with
      | "struct" :: tag :: _ => if (s.structs.lookup s!"struct {tag}").isSome then some (["struct", tag], .struct s!"struct {tag}") else none
      | n :: x :: _ => if isIdent x && (s.structs.lookup n).isSome && (s.vars.lookup n).isNone then some ([n], .struct n) else none
      | _ => none
    match structLocal <|> localTypes.find? fun (ws, _) => rest.take ws.length == ws with
    | some (ws, ty) =>
      for _ in ws do let _ ← gnext
      let x ← gnext
      unless isIdent x do throw s!"expected a variable name, found '{x}'"
      if (← gpeek) == "=" then
        let _ ← gnext
        let a ← expr
        unless a.fits ty do throw s!"{x}: expected {ty.show}, got {a.show}"
      else if let .struct sp := ty then
        -- an uninitialised struct may hold no pointers
        let fs := ((← get).structs.lookup sp).getD []
        unless allNumbers (← get).structs fs 8 do throw s!"{x}: a struct local with string or pointer fields must be initialised"
      modify fun s => { s with vars := (x, ty) :: s.vars }
      expect ";"
    | none =>
      if t == "struct" then throw s!"unknown struct {rest.getD 1 ""} (declare it with c_struct or import its header)"
      simple; expect ";"
where
  /-- assignment, increment, or a call -/
  simple : G Unit := do
    let x ← gpeek
    -- (9i) an assignment to a field: `x.f.g = e`
    let mut path : Option GTy := none
    if (← get).toks[(← get).pos + 1]?.getD "" == "." then
      if let some ty@(.struct _) := (← get).vars.lookup x then
        let _ ← gnext
        path := some (← members ty)
    let st ← get
    let op := if path.isSome then st.toks[st.pos]?.getD "" else st.toks[st.pos + 1]?.getD ""
    if path.isSome && !["=", "+=", "-=", "*=", "/=", "%="].contains op then throw s!"expected an assignment, found '{op}'"
    if let some ty := path then
      let _ ← gnext
      let a ← expr
      unless a.fits ty do throw s!"{x}: expected {ty.show}, got {a.show}"
      if !ty.isNum && op != "=" then throw s!"'{op}' needs numbers"
    else if ["=", "+=", "-=", "*=", "/=", "%="].contains op then
      let _ ← gnext; let _ ← gnext
      let some ty := (← get).vars.lookup x | throw s!"unknown variable {x}"
      let a ← expr
      unless a.fits ty do throw s!"{x}: expected {ty.show}, got {a.show}"
      if !ty.isNum && op != "=" then throw s!"'{op}' needs numbers"
    else if op == "++" || op == "--" then
      let _ ← gnext; let _ ← gnext
      if (← get).vars.lookup x != some .int then throw s!"'{op}' needs an integer variable"
    else let _ ← expr

/-- Check a glue body: the parameters and functions in scope, the return type, and (9i)
the structs it may use. -/
def checkGlue (body : String) (params : List (String × GTy)) (funcs : List (String × List GTy × GTy)) (ret : GTy)
    (structs : List (String × List (String × GTy)) := []) : Except String Unit := do
  let toks := joinOps (tokenize body)
  let ((), s) ← (do while (← gpeek) != "" do stmt : G Unit).run { toks, vars := params, funcs, ret, structs }
  let _ := s
  pure ()

end Wiz.FFI
