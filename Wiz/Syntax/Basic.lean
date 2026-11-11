import Wiz.Core.Level

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

/-- A half-open range `[start, stop)` of character offsets in the input.

`synthetic` marks syntax a macro made rather than the user wrote (11q): the nodes of a
macro rule's template (whose range is in the file that declared the rule, not the one
being elaborated) and the output of a procedural macro (whose range is the call's).
Errors still point at it, but the info tree records nothing at it (hovers and goals
would land in the wrong place), and the local context keeps the nearest range the user
wrote (`LocalCtx.withInfo`). -/
structure SourceInfo where
  start : Nat := 0
  stop  : Nat := 0
  synthetic : Bool := false
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
def setArg (s : Syntax) (i : Nat) (a : Syntax) : Syntax := match s with
  | node info k as => node info k (as.set! i a)
  | s => s

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

/-- (11q) Mark every range in `s` synthetic (a macro rule's template, before it is
instantiated: what the antiquotations bind keeps its own ranges). -/
partial def markSynthetic : Syntax → Syntax
  | missing => missing
  | atom i v => atom { i with synthetic := true } v
  | ident i n => ident { i with synthetic := true } n
  | node i k as => node { i with synthetic := true } k (as.map markSynthetic)

/-- The source text of syntax, roughly: its tokens separated by spaces, with
parentheses around arguments that need them (for "expands to" in hovers). Macro scopes
print as `x✝`, as Lean shows inaccessible names. -/
partial def reprint (s : Syntax) : String := go s
where
  name (n : Name) : String := match n.splitOn "✝" with
    | [n] => n
    | n :: _ => n ++ "✝"
    | [] => n
  -- an argument without parentheses: one token, or something in brackets of its own
  atomic (s : Syntax) : Bool :=
    ["term.paren", "num", "str", "term.ident", "term.tuple", "term.anon"].contains s.kind || (go s).all (· != ' ')
  arg (s : Syntax) : String := if atomic s then go s else s!"({go s})"
  go (s : Syntax) : String := match s with
    | missing => ""
    | atom _ v => v
    | ident _ n => name n
    | node _ "num" #[atom _ v] => v
    | node _ "str" #[atom _ v] => (repr v).pretty
    | node _ "term.app" as =>
      " ".intercalate (arg (as.getD 0 missing) :: ((as.getD 1 missing).args.toList.map arg))
    | node _ _ as => " ".intercalate ((as.toList.map go).filter (!·.isEmpty))

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
