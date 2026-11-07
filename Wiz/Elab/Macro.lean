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

/-- A rule: the node kind it applies to, the pattern, the template, and the names that
`notation` arguments use in the template (`[]` for `macro_rules`, which uses `$x`). -/
structure MacroRule where
  kind : Name
  pattern : Syntax
  template : Syntax
  vars : List Name := []
  deriving Inhabited

def antiquotName? : Syntax → Option Name
  | .node _ "antiquot" args => args[1]? >>= Syntax.getId?
  | _ => none

/-- **Exercise 6.1a.** Match `stx` against a pattern, extending the bindings. -/
partial def matchPattern (pat stx : Syntax) (acc : List (Name × Syntax)) : Option (List (Name × Syntax)) :=
  sorry

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
  sorry

/-- Expand `stx` with the latest matching rule, if any. -/
def expandMacro? (rules : List MacroRule) (stx : Syntax) (scope : Nat) : Option Syntax := do
  for r in rules do
    if r.kind == stx.kind then
      if let some binds := matchPattern r.pattern stx [] then
        return instantiate binds r.vars scope "" r.template
  none

end Wiz.Elab
