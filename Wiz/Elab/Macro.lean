import Wiz.Elab.Basic

/-!
# Macros by example

A macro rule rewrites syntax to syntax:

```
macro_rules
  | `(term| unless $c then $t else $e) => `(term| if $c then $e else $t)
notation:65 a:65 " + " b:66 => add a b
infixl:70 " * " => mul
```

* **Matching** compares syntax trees structurally; `$x` binds a subtree.
* **Instantiation** replaces `$x` (and, for `notation`, the argument names) with what
  they matched.
* **Hygiene**: every other identifier the template introduces gets a fresh *macro
  scope*, `x ↦ x✝3`. A local variable only matches an identifier with the same scope,
  so a template's binders can't capture a user's variables. Globals are looked up with
  the scope stripped, so templates can still refer to `add`. (Lean does the same.)

Expansion happens in the elaborator: before elaborating a node, the latest matching
rule (if any) rewrites it.
-/

namespace Wiz.Elab

def antiquotName? : Syntax → Option Name
  | .node _ "antiquot" args => args[1]? >>= Syntax.getId?
  | _ => none

/-- **Exercise 6.1a.** Match `stx` against a pattern, extending the bindings. -/
partial def matchPattern (pat stx : Syntax) (acc : List (Name × Syntax)) : Option (List (Name × Syntax)) :=
  --<sol
  match antiquotName? pat with
  | some x => some ((x, stx) :: acc)
  | none =>
    match pat, stx with
    | .node _ k as, .node _ k' bs =>
      if k == k' && as.size == bs.size then
        (as.zip bs).foldlM (fun acc (a, b) => matchPattern a b acc) acc
      else none
    | .atom _ v, .atom _ v' => if v == v' then some acc else none
    | .ident _ n, .ident _ n' => if n == n' then some acc else none
    | .missing, .missing => some acc
    | _, _ => none
  --|ex
  --| sorry
  --sol>

/-- The base name of a (possibly macro-scoped) identifier. -/
def stripScope (n : Name) : Name := (n.splitOn "✝").headD n

/-- Identifiers under these node kinds are not references, so they get no scope. -/
def unscopedParents : List Name := ["term.dotIdent", "term.field", "level.param", "term.syntheticHole"]

/-- **Exercise 6.1b.** Instantiate a template: replace antiquotations (and the `vars` of a
`notation`) by their bindings, and add `scope` to every other plain identifier that
isn't under one of the `unscopedParents` (dotted names are global references: leave
them too). -/
partial def instantiate (binds : List (Name × Syntax)) (vars : List Name) (scope : Nat)
    (parent : Name) (t : Syntax) : Syntax :=
  --<sol
  match antiquotName? t with
  | some x => ((binds.find? (·.1 == x)).map (·.2)).getD t
  | none => match t with
    -- a `notation` argument used as a term: replace the whole `term.ident` node
    | .node _ "term.ident" #[.ident _ n] =>
      if vars.contains n then ((binds.find? (·.1 == n)).map (·.2)).getD t
      else .node t.info "term.ident" #[instantiate binds vars scope "term.ident" (.ident t.info n)]
    | .ident i n =>
      if vars.contains n then ((binds.find? (·.1 == n)).map (·.2)).getD t
      else if unscopedParents.contains parent || n.contains '.' then t
      else .ident i s!"{n}✝{scope}"
    | .node i k as => .node i k (as.map (instantiate binds vars scope k))
    | s => s
  --|ex
  --| sorry
  --sol>

/-- Expand `stx` with the latest matching rule, if any; also returns the rule. The
template's ranges are marked synthetic (11q): they are in the file that declared the
rule, while what the antiquotations bind keeps the ranges the user wrote. -/
def expandMacroRule? (rules : List MacroRule) (stx : Syntax) (scope : Nat) : Option (Syntax × MacroRule) := do
  for r in rules do
    if r.kind == stx.kind then
      if let some binds := matchPattern r.pattern stx [] then
        return (instantiate binds r.vars scope "" r.template.markSynthetic, r)
  none

/-- Expand `stx` with the latest matching rule, if any. -/
def expandMacro? (rules : List MacroRule) (stx : Syntax) (scope : Nat) : Option Syntax :=
  (expandMacroRule? rules stx scope).map (·.1)

end Wiz.Elab
