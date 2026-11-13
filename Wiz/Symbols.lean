import Wiz.Query

/-!
# Document symbols, workspace symbols and folding ranges

* **Document symbols** (the outline): the declarations of the file, one per command (the
  first name it declares), with the others it declares (constructors, fields, the
  generated functions) as children. Ranges are the commands'.
* **Workspace symbols**: the declarations of every open document and of the libraries
  they import whose name contains the query (case-insensitive).
* **Folding ranges**: commands spanning several lines, `by` blocks, `match`es and block
  comments.
-/

namespace Wiz.Symbols

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- LSP `SymbolKind`s. -/
def kindFunction : Nat := 12
def kindStruct : Nat := 23
def kindConstructor : Nat := 9
def kindField : Nat := 8
def kindConstant : Nat := 14

/-- Names the elaborator makes for its own use. -/
def hidden (n : Name) : Bool :=
  (n.splitOn "✝").length > 1 || n.startsWith "_private." ||
  [".desc", ".casesOn", ".rec", ".ind", ".below", ".brecOn", ".noConfusion", ".sizeOf", ".elim", ".Tag"].any (n.endsWith ·)

partial def endsInSort : Term R → Bool
  | .pi _ _ _ _ cod _ => endsInSort cod
  | .sort _ => true
  | _ => false

structure Symbol where
  name : Name
  kind : Nat
  detail : String
  /-- the command's range (and the name's, here the same) -/
  range : SourceInfo
  children : Array Symbol := #[]
  deriving Inhabited

def kindOf (g : Globals R) (n : Name) (child : Bool) : Nat :=
  match g.find? n with
  | some d =>
    if endsInSort d.type then kindStruct
    else if child then (if d.value.isNone then kindConstructor else kindField)
    else kindFunction
  | none => kindFunction

/-- The outline of the main file. -/
def documentSymbols (s : CommandState R) : Array Symbol := Id.run do
  let mut out : Array Symbol := #[]
  for n in s.globals.order do
    if hidden n then continue
    let some (r, "") := s.declSites.get? n | continue
    let detail := match s.globals.find? n with
      | some d => d.type.pretty []
      | none => ""
    match out.back? with
    | some p =>
      if p.range == r then
        out := out.pop.push { p with children := p.children.push { name := n, kind := kindOf s.globals n true, detail, range := r } }
        continue
    | none => pure ()
    out := out.push { name := n, kind := kindOf s.globals n false, detail, range := r }
  out

/-- Folding ranges: (first line, last line, kind) with `kind` `""` or `comment`. -/
def foldingRanges (s : CommandState R) (text : String) : Array (Nat × Nat × String) := Id.run do
  let chars := text.toList.toArray
  -- the line of each offset
  let mut lineOf : Array Nat := Array.mkEmpty (chars.size + 1)
  let mut l := 0
  for c in chars do
    lineOf := lineOf.push l
    if c == '\n' then l := l + 1
  lineOf := lineOf.push l
  let line (o : Nat) : Nat := lineOf[min o chars.size]!
  let mut out : Array (Nat × Nat × String) := #[]
  let add (out : Array (Nat × Nat × String)) (a b : Nat) (k : String) :=
    -- (a range ending at a newline ends on the line before)
    let la := line a
    let lb := line (if b > a && b ≤ chars.size && chars[b - 1]! == '\n' then b - 1 else b)
    if lb > la && !out.contains (la, lb, k) then out.push (la, lb, k) else out
  for n in s.globals.order do
    if let some (r, "") := s.declSites.get? n then out := add out r.start r.stop ""
  for i in s.infos do
    match i with
    | .tactic r true .. | .matchCases r .. => if !r.synthetic then out := add out r.start r.stop ""
    | _ => pure ()
  -- block comments
  let mut i := 0
  while i + 1 < chars.size do
    if chars[i]! == '-' && chars[i + 1]! == '-' then
      while i < chars.size && chars[i]! != '\n' do i := i + 1
    else if chars[i]! == '/' && chars[i + 1]! == '-' then
      let a := i
      let mut depth := 0
      while i + 1 < chars.size do
        if chars[i]! == '/' && chars[i + 1]! == '-' then depth := depth + 1; i := i + 2
        else if chars[i]! == '-' && chars[i + 1]! == '/' then
          depth := depth - 1; i := i + 2
          if depth == 0 then break
        else i := i + 1
      out := add out a i "comment"
    else i := i + 1
  out.qsort fun (a, b, _) (c, d, _) => a < c || (a == c && b > d)

end Wiz.Symbols
