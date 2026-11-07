import Std.Data.HashMap
/-!
# Reading C headers

`import_c "h.h"` binds the functions a C header declares. The header is first run
through the C preprocessor (`cc -E -P`, by the command line tool, since the frontend
is pure), and the result is parsed here. Only a subset of C matters: **function
prototypes** and the **typedefs** they use. Everything else (struct and enum bodies,
inline function bodies, GNU `__attribute__`s and `__asm__` labels) is skipped.

    declaration := specifier* declarator ("," declarator)* ";"
    specifier   := storage class | qualifier | base type | struct/union/enum tag [body] | typedef name
    declarator  := "*"* qualifier* (name | "(" declarator ")") ["(" parameters ")"] ["[" … "]"]*
-/

namespace Wiz.FFI

inductive CType where
  | void
  /-- an integer type (`char`, `int`, `long`, `size_t`, `_Bool` …) -/
  | int (name : String)
  | float (name : String)
  | ptr (to : CType)
  | const (t : CType)
  /-- anything this subset doesn't follow (structs by value, function pointers …) -/
  | other (what : String)
  deriving Repr, BEq, Inhabited

structure CFunc where
  name : String
  ret : CType
  params : List CType
  variadic : Bool
  deriving Repr, Inhabited

/-- Split preprocessed C into tokens: identifiers and numbers, string and character
literals, and punctuation (one character at a time, except `...`). -/
partial def tokenize (s : String) : Array String := go s.toList #[]
where
  go : List Char → Array String → Array String
    | [], acc => acc
    | c :: cs, acc =>
      if c.isWhitespace then go cs acc
      else if c.isAlpha || c == '_' then
        let w := (c :: cs).takeWhile fun d => d.isAlphanum || d == '_'
        go ((c :: cs).drop w.length) (acc.push (String.mk w))
      else if c.isDigit then
        let w := (c :: cs).takeWhile fun d => d.isAlphanum || d == '.'
        go ((c :: cs).drop w.length) (acc.push (String.mk w))
      else if c == '"' || c == '\'' then
        let rec lit : List Char → List Char × List Char
          | [] => ([], [])
          | '\\' :: d :: ds => let (l, r) := lit ds; ('\\' :: d :: l, r)
          | d :: ds => if d == c then ([d], ds) else let (l, r) := lit ds; (d :: l, r)
        let (l, rest) := lit cs
        go rest (acc.push (String.mk (c :: l)))
      else if c == '.' && cs.take 2 == ['.', '.'] then go (cs.drop 2) (acc.push "...")
      else go cs (acc.push c.toString)

def storage : List String := ["extern", "static", "inline", "__inline", "__inline__", "_Noreturn", "__extension__", "register", "auto", "_Thread_local"]
def qualifiers : List String := ["const", "volatile", "restrict", "__restrict", "__restrict__", "_Atomic", "__const"]
def intWords : List String := ["char", "short", "int", "long", "signed", "unsigned", "_Bool", "__int128"]
def floatWords : List String := ["float", "double"]

structure PState where
  toks : Array String
  pos : Nat := 0
  typedefs : Std.HashMap String CType := {}

abbrev P := StateM PState

def peek : P String := do let s ← get; pure (s.toks[s.pos]?.getD "")
def next : P String := do let t ← peek; modify fun s => { s with pos := s.pos + 1 }; pure t
def atEnd : P Bool := do let s ← get; pure (s.pos ≥ s.toks.size)

/-- Skip a balanced group, starting at an opening bracket. -/
partial def skipGroup : P Unit := do
  let o ← next
  let c := match o with | "(" => ")" | "[" => "]" | _ => "}"
  let rec loop (depth : Nat) : P Unit := do
    if ← atEnd then return
    let t ← next
    if t == o then loop (depth + 1)
    else if t == c then (if depth == 0 then pure () else loop (depth - 1))
    else loop depth
  loop 0

/-- Skip GNU extensions: `__attribute__((…))`, `__asm__(…)`, `__declspec(…)`. -/
partial def skipExtensions : P Unit := do
  let t ← peek
  if t == "__attribute__" || t == "__asm__" || t == "__asm" || t == "asm" || t == "__declspec" then
    let _ ← next
    if (← peek) == "(" then skipGroup
    skipExtensions

/-- The specifiers of a declaration: returns the base type and whether it is a typedef. -/
partial def specifiers : P (CType × Bool) := do
  let mut ints : Array String := #[]
  let mut base : Option CType := none
  let mut isTypedef := false
  let mut isConst := false
  repeat
    skipExtensions
    let t ← peek
    if t == "typedef" then let _ ← next; isTypedef := true
    else if storage.contains t then let _ ← next
    else if qualifiers.contains t then let _ ← next; if t == "const" || t == "__const" then isConst := true
    else if intWords.contains t then let _ ← next; ints := ints.push t
    else if floatWords.contains t then let _ ← next; base := some (.float t)
    else if t == "void" then let _ ← next; base := some .void
    else if t == "struct" || t == "union" || t == "enum" then
      let _ ← next
      skipExtensions
      let tag ← if (← peek) != "{" then next else pure "<anonymous>"
      if (← peek) == "{" then skipGroup
      base := some (if t == "enum" then .int "enum" else .other s!"{t} {tag}")
    else if base.isNone && ints.isEmpty then
      match (← get).typedefs.get? t with
      | some ty => let _ ← next; base := some ty
      | none => break
    else break
  let ty := match base with
    | some b => b
    | none => if ints.isEmpty then .int "int" else .int (" ".intercalate ints.toList)
  pure (if isConst then .const ty else ty, isTypedef)

/-- **Exercise 9.1.** A declarator, applied to the base type: pointers, the name (or a
parenthesised declarator, which makes it a function pointer or other complex type:
`other`), then a parameter list (a function) or array suffixes (a pointer).
Returns the name (if any), the type, and the parameters if it declares a function. -/
partial def declarator (base : CType) : P (Option String × CType × Option (List CType × Bool)) := do
  --<sol
  let mut ty := base
  repeat
    skipExtensions
    let t ← peek
    if t == "*" then let _ ← next; ty := .ptr ty
    else if qualifiers.contains t then let _ ← next
    else break
  skipExtensions
  let mut name : Option String := none
  let mut complex := false
  let t ← peek
  if t == "(" then
    -- `(*f)(…)` and the like: a function pointer (or worse); keep its name
    let _ ← next
    let (n, _, _) ← declarator .void
    while (← peek) != ")" && !(← atEnd) do
      if (← peek) == "(" || (← peek) == "[" then skipGroup else let _ ← next
    let _ ← next
    name := n
    complex := true
  else if t != "" && (t.front.isAlpha || t.startsWith "_") then
    name := some (← next)
  skipExtensions
  let mut params : Option (List CType × Bool) := none
  if (← peek) == "(" then
    let _ ← next
    let mut ps : Array CType := #[]
    let mut variadic := false
    repeat
      let t ← peek
      if t == ")" || t == "" then let _ ← next; break
      if t == "," then let _ ← next; continue
      if t == "..." then let _ ← next; variadic := true; continue
      let (pb, _) ← specifiers
      let (_, pty, pfun) ← declarator pb
      ps := ps.push (if pfun.isSome then .other "function pointer" else pty)
    -- `(void)` means no parameters
    params := some ((if ps == #[.void] then #[] else ps).toList, variadic)
  while (← peek) == "[" do
    skipGroup
    ty := .ptr ty
  skipExtensions
  if complex then return (name, .other "function pointer", none)
  pure (name, ty, params)
  --|ex
  --| sorry
  --sol>

/-- Parse a preprocessed header: its function prototypes. -/
partial def parseHeader (src : String) : Array CFunc := Id.run do
  let st : PState := { toks := tokenize src }
  let rec decls (fuel : Nat) (acc : Array CFunc) : P (Array CFunc) := do
    if fuel == 0 || (← atEnd) then return acc
    let start := (← get).pos
    let (base, isTypedef) ← specifiers
    let mut acc := acc
    repeat
      let (name, ty, fn) ← declarator base
      if (← peek) == "{" then
        -- a function definition (an inline function in a header): skip its body
        skipGroup
        if let (some n, some (ps, v)) := (name, fn) then
          unless isTypedef do acc := acc.push { name := n, ret := ty, params := ps, variadic := v }
        break
      if (← peek) == "=" then
        -- an initialiser: skip to the end of the declaration
        while (← peek) != "," && (← peek) != ";" && !(← atEnd) do
          if (← peek) == "(" || (← peek) == "{" || (← peek) == "[" then skipGroup else let _ ← next
      match name, fn with
      | some n, some (ps, v) =>
        if isTypedef then modify fun s => { s with typedefs := s.typedefs.insert n (.other "function type") }
        else acc := acc.push { name := n, ret := ty, params := ps, variadic := v }
      | some n, none => if isTypedef then modify fun s => { s with typedefs := s.typedefs.insert n ty }
      | _, _ => pure ()
      if (← peek) == "," then let _ ← next else break
    -- the end of the declaration (or skip a token we don't understand)
    if (← peek) == ";" then let _ ← next
    if (← get).pos == start then let _ ← next
    decls (fuel - 1) acc
  -- a function may be declared several times: keep the first
  let fs := (decls 1000000 #[]).run' st
  pure (fs.foldl (fun acc f => if acc.any (·.name == f.name) then acc else acc.push f) #[])

end Wiz.FFI
