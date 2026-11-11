import Wiz.Parser.Descr

/-!
# The pretty printer's table (notation-aware printing)

What `Term.pretty` needs to print an application as notation (`[1, 2]` for
`List.cons 1 (List.cons 2 List.nil)`, `a + b` for `Add.add a b`): the **unexpanders**
of each constant, and how each syntax kind is **formatted** (its grammar). It lives in
`Globals.pp`, as a Lean environment extension would; the kernel never reads it. The
command elaborator keeps it up to date (`CommandState.refreshPP`). The algorithm is in
`Core/Pretty.lean`; the design in `docs/stages/11-tooling.md`, 11r.
-/

namespace Wiz

/-- How an application of a constant prints as notation. -/
inductive Unexpander where
  /-- match `pattern`, an application `c $x₁ … $xₙ` (or the bare `c` when `n = 0`), and
  print `template` with the bindings filled in. From `notation`, `infix…`, `macro_rules`
  (inverted) and `app_unexpander` -/
  | rule (pattern template : Syntax)
  /-- the Wiz function `fn : Unexpander` (`attribute [app_unexpander c] fn`), run by the
  interpreter on the application (`PPTable.run`) -/
  | fn (name : Name)
  deriving Inhabited

structure UnexpanderEntry where
  /-- the constant at the head -/
  head : Name
  /-- the explicit arguments a `rule` takes (`fn`s get them all, then fewer) -/
  arity : Nat
  how : Unexpander
  deriving Inhabited

/-- How the nodes of a syntax kind print: the parser that makes them. `raw` are the
atoms as declared, whitespace included (`" + "`, `"!"`), in the order they occur in `p`,
when known (user syntax); they decide the spacing. -/
structure PPFormat where
  cat : Name
  leading : Bool
  prec : Nat
  lhsPrec : Nat := 0
  p : ParserDescr
  raw : Array String := #[]
  deriving Inhabited

structure PPTable where
  /-- per constant, latest first -/
  unexpanders : Std.HashMap Name (List UnexpanderEntry) := {}
  /-- per node kind -/
  formats : Std.HashMap Name PPFormat := {}
  /-- `pp.notation` (`--pp-all`, `set_option pp.notation false` turn it off): without it
  terms print as they are -/
  useNotation : Bool := true
  /-- run a procedural unexpander on the application: `none` when it doesn't apply (it
  failed) or can't run here (no interpreter: kernel messages) -/
  run : Name → Syntax → Option Syntax := fun _ _ => none
  deriving Inhabited

def PPTable.active (t : PPTable) : Bool := t.useNotation && !t.unexpanders.isEmpty

end Wiz
