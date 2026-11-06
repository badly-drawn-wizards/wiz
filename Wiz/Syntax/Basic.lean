import Wiz.Core.Term

/-!
# Syntax trees

The parser produces **untyped** syntax trees. Everything downstream (macro expansion,
elaboration, the LSP) works on this one data type, which is what makes the language
extensible: a user-declared `syntax` rule produces the same `Syntax` as a built-in
one, just with a different `kind`.

* `atom`  -- a keyword or symbol token, such as `fun` or `→`
* `ident` -- an identifier
* `node`  -- a parsed construct with a `kind` (such as `term.app`) and children

By convention a node of kind `null` is a plain list. `many`, `optional` and `sepBy`
produce these.

Literals are nodes too: `num` and `str` nodes with a single atom child. For `str`
the atom holds the *decoded* string.
-/

namespace Wiz

/-- A half-open range `[start, stop)` of character offsets in the input. -/
structure SourceInfo where
  start : Nat := 0
  stop  : Nat := 0
  deriving Repr, BEq, Inhabited

inductive Syntax where
  | missing
  | atom (info : SourceInfo) (val : String)
  | ident (info : SourceInfo) (val : Name)
  | node (info : SourceInfo) (kind : Name) (args : Array Syntax)
  deriving Repr, Inhabited

namespace Syntax

def nullKind : Name := "null"
def numKind : Name := "num"
def strKind : Name := "str"

def info : Syntax → SourceInfo
  | missing => {}
  | atom i _ | ident i _ | node i _ _ => i

def kind : Syntax → Name
  | missing => "missing"
  | atom .. => "atom"
  | ident .. => "ident"
  | node _ k _ => k

def args : Syntax → Array Syntax
  | node _ _ as => as
  | _ => #[]

def getArg (s : Syntax) (i : Nat) : Syntax := s.args[i]?.getD missing

def isOfKind (s : Syntax) (k : Name) : Bool := s.kind == k

def getId? : Syntax → Option Name
  | ident _ n => some n
  | _ => none

def isNone (s : Syntax) : Bool := s.isOfKind nullKind && s.args.isEmpty

/-- The value of a `num` node. -/
def getNat? : Syntax → Option Nat
  | node _ "num" #[atom _ v] => v.toNat?
  | _ => none

/-- The value of a `str` node. -/
def getStr? : Syntax → Option String
  | node _ "str" #[atom _ v] => some v
  | _ => none

def mkNull (args : Array Syntax) (info : SourceInfo := {}) : Syntax := node info nullKind args

/-- Compact s-expression rendering, used in tests and `wiz parse`.
Atoms are omitted unless `atoms := true`, `null` nodes print as `[...]`, and literals
print as their value. -/
partial def toSExpr (s : Syntax) (atoms : Bool := false) : String :=
  match s with
  | missing => "<missing>"
  | atom _ v => s!"\"{v}\""
  | ident _ n => n
  | node _ "num" #[atom _ v] => v
  | node _ "str" #[atom _ v] => s!"\"{v}\""
  | node _ k args =>
    let shown := args.filter fun a => atoms || !(a matches atom ..)
    let inner := " ".intercalate (shown.map (toSExpr · atoms)).toList
    if k == nullKind then s!"[{inner}]"
    else if inner.isEmpty then s!"({k})" else s!"({k} {inner})"

instance : ToString Syntax := ⟨(·.toSExpr)⟩

end Syntax

/-- Line and column (both 0-based) of a character offset. -/
def lineCol (input : String) (offset : Nat) : Nat × Nat := Id.run do
  let mut line := 0
  let mut col := 0
  let mut i := 0
  for c in input.toList do
    if i == offset then break
    if c == '\n' then
      line := line + 1
      col := 0
    else
      col := col + 1
    i := i + 1
  (line, col)

end Wiz
