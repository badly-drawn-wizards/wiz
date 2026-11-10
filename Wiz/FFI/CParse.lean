import Std.Data.HashMap
/-!
# Reading C headers

`import_c "h.h"` binds the functions a C header declares. The header is first run
through the C preprocessor (`cc -E -P`, by the command line tool, since the frontend
is pure), and the result is parsed here. Only a subset of C matters: **function
prototypes**, the **typedefs** they use, and (9i) the **struct definitions** whose
fields are plain (no bit fields or anonymous members). Everything else (union and enum
bodies, inline function bodies, GNU `__attribute__`s and `__asm__` labels) is skipped.

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
  /-- (9i) a struct, by its C spelling: `struct tag`, or a typedef name for an anonymous one -/
  | struct (spelling : String)
  /-- (9i) an array (of a known length, if it's a number); as a parameter, a pointer -/
  | array (t : CType) (len : Option Nat)
  /-- anything this subset doesn't follow (structs by value, function pointers …) -/
  | other (what : String)
  deriving Repr, BEq, Inhabited

structure CFunc where
  name : String
  ret : CType
  params : List CType
  variadic : Bool
  /-- the parameters' names, where the prototype gives them (`""` otherwise) -/
  paramNames : List String := []
  deriving Repr, Inhabited

/-- (9i) A header's structs: the fields, or `none` when the definition has something this
subset doesn't marshal (bit fields, anonymous members), and the typedef names of each. -/
structure CStruct where
  spelling : String
  fields : Option (List (String × CType))
  aliases : List String := []
  deriving Repr, Inhabited

/-- An array parameter is a pointer. -/
def CType.decay : CType → CType
  | .array t _ => .ptr t
  | .const (.array t _) => .ptr t
  | t => t

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
  /-- struct definitions, by spelling (9i); in order of definition -/
  structs : Array CStruct := #[]
  anon : Nat := 0
  /-- typedef names of named structs (`typedef struct foo foo_t`), with the struct -/
  aliases : Array (String × String) := #[]
  /-- the parameter names of the last parameter list read -/
  lastNames : List String := []

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

mutual

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
      let tag ← if (← peek) != "{" then next else do
        let k := (← get).anon
        modify fun s => { s with anon := k + 1 }
        pure s!"<anonymous {k}>"
      if t == "struct" && (← peek) == "{" then
        let fields ← structBody
        let spelling := if tag.startsWith "<" then tag else s!"struct {tag}"
        modify fun s => { s with structs := s.structs.push { spelling, fields } }
      else if (← peek) == "{" then skipGroup
      base := some (if t == "enum" then .int "enum"
        else if t == "struct" then .struct (if tag.startsWith "<" then tag else s!"struct {tag}")
        else .other s!"{t} {tag}")
    else if base.isNone && ints.isEmpty then
      match (← get).typedefs.get? t with
      | some ty => let _ ← next; base := some ty
      | none => break
    else break
  let ty := match base with
    | some b => b
    | none => if ints.isEmpty then .int "int" else .int (" ".intercalate ints.toList)
  pure (if isConst then .const ty else ty, isTypedef)

/-- (9i) The body of a struct definition, at its `{`: the fields, or `none` if it has bit
fields or anonymous members. -/
partial def structBody : P (Option (List (String × CType))) := do
  let _ ← next
  let mut fields : Array (String × CType) := #[]
  let mut ok := true
  repeat
    if (← atEnd) then break
    if (← peek) == "}" then let _ ← next; break
    if (← peek) == ";" then let _ ← next; continue
    let start := (← get).pos
    let (base, _) ← specifiers
    repeat
      if (← peek) == ";" then
        -- an anonymous struct or union member
        ok := false; break
      let (name, ty, fn) ← declarator base
      if (← peek) == ":" then
        -- a bit field
        ok := false
        while (← peek) != "," && (← peek) != ";" && (← peek) != "}" && !(← atEnd) do let _ ← next
      match name, fn with
      | some n, none => fields := fields.push (n, ty)
      | _, _ => ok := false
      if (← peek) == "," then let _ ← next else break
    if (← peek) == ";" then let _ ← next
    else if (← peek) != "}" then
      ok := false
      while (← peek) != ";" && (← peek) != "}" && !(← atEnd) do
        if (← peek) == "(" || (← peek) == "{" || (← peek) == "[" then skipGroup else let _ ← next
    if (← get).pos == start then let _ ← next
  skipExtensions
  pure (if ok && !fields.isEmpty then some fields.toList else none)

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
    let mut names : Array String := #[]
    let mut variadic := false
    repeat
      let t ← peek
      if t == ")" || t == "" then let _ ← next; break
      if t == "," then let _ ← next; continue
      if t == "..." then let _ ← next; variadic := true; continue
      let (pb, _) ← specifiers
      let (pn, pty, pfun) ← declarator pb
      ps := ps.push (if pfun.isSome then .other "function pointer" else pty.decay)
      names := names.push (pn.getD "")
    -- `(void)` means no parameters
    params := some ((if ps == #[.void] then #[] else ps).toList, variadic)
    modify fun s => { s with lastNames := if ps == #[.void] then [] else names.toList }
  -- array suffixes, innermost last: `int a[2][3]` is an array of 2 arrays of 3
  let mut lens : Array (Option Nat) := #[]
  while (← peek) == "[" do
    let s ← get
    let len := match s.toks[s.pos + 1]?, s.toks[s.pos + 2]? with
      | some n, some "]" => n.toNat?
      | _, _ => none
    skipGroup
    lens := lens.push len
  ty := lens.foldr (fun n t => .array t n) ty
  skipExtensions
  if complex then return (name, .other "function pointer", none)
  pure (name, ty, params)
  --|ex
  --| sorry
  --sol>

end

/-- A typedef name for a type: an anonymous struct takes the name as its spelling (9i),
and a named one gets it as an alias. -/
def bindTypedef (n : String) (ty : CType) : P Unit := do
  match ty with
  | .struct sp =>
    if sp.startsWith "<" then
      modify fun s => { s with typedefs := s.typedefs.insert n (.struct n),
                               structs := s.structs.map fun st => if st.spelling == sp then { st with spelling := n } else st }
    else
      modify fun s => { s with typedefs := s.typedefs.insert n ty, aliases := s.aliases.push (n, sp) }
  | _ => modify fun s => { s with typedefs := s.typedefs.insert n ty }

/-- Parse a preprocessed header: its function prototypes and (9i) its structs. -/
partial def parseHeaderFull (src : String) : Array CFunc × Array CStruct := Id.run do
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
          unless isTypedef do acc := acc.push { name := n, ret := ty, params := ps, variadic := v, paramNames := (← get).lastNames }
        break
      if (← peek) == "=" then
        -- an initialiser: skip to the end of the declaration
        while (← peek) != "," && (← peek) != ";" && !(← atEnd) do
          if (← peek) == "(" || (← peek) == "{" || (← peek) == "[" then skipGroup else let _ ← next
      match name, fn with
      | some n, some (ps, v) =>
        if isTypedef then modify fun s => { s with typedefs := s.typedefs.insert n (.other "function type") }
        else acc := acc.push { name := n, ret := ty, params := ps, variadic := v, paramNames := (← get).lastNames }
      | some n, none => if isTypedef then bindTypedef n ty
      | _, _ => pure ()
      if (← peek) == "," then let _ ← next else break
    -- the end of the declaration (or skip a token we don't understand)
    if (← peek) == ";" then let _ ← next
    if (← get).pos == start then let _ ← next
    decls (fuel - 1) acc
  -- a function may be declared several times: keep the first
  let (fs, st) := (decls 1000000 #[]).run st
  -- a struct defined twice (in several headers): keep the first
  let structs := st.structs.foldl (fun acc t => if acc.any (·.spelling == t.spelling) then acc else acc.push t) #[]
  -- the typedef names (a typedef may come before the definition; an opaque struct has
  -- no definition, only its names)
  let structs := st.aliases.foldl (fun acc (n, sp) =>
    if acc.any (·.spelling == sp) then acc.map fun t => if t.spelling == sp && !t.aliases.contains n then { t with aliases := t.aliases ++ [n] } else t
    else acc.push { spelling := sp, fields := none, aliases := [n] }) structs
  pure (fs.foldl (fun acc f => if acc.any (·.name == f.name) then acc else acc.push f) #[], structs)

/-- Parse a preprocessed header: its function prototypes. -/
def parseHeader (src : String) : Array CFunc := (parseHeaderFull src).1

end Wiz.FFI
