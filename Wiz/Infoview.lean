import Wiz.Core.Pretty
import Wiz.Elab.Basic

/-!
# Tagged terms, for the infoview

`Term.prettyTagged` (`Core/Pretty.lean`) prints a term exactly as `Term.pretty` does, but as **tagged text**:
every printed subterm is wrapped in a tag naming it, so an infoview can highlight the
subterm under the mouse and ask about it (`wiz/subtermInfo`). A tag holds an index into
the array of subterms the printer returns; the language server turns those into refs of
the document's session table.

Each subterm remembers its context: the names and (where known) types of the variables in
scope, innermost first, so its type can be inferred later. A `fun` binder's type isn't in
the term, so under a `fun` it is unknown.
-/

namespace Wiz

variable {R : Type} [QuantitySyntax R] [BEq R]

/-! ## Goals -/

/-- The context of a goal's target: names and types, innermost first. -/
def GoalView.scope (g : GoalView R) : List Name × List (Option (Term R)) :=
  (g.hyps.toList.reverse.map (·.1), g.hyps.toList.reverse.map (some ·.2.1))

/-- A hypothesis and a goal, tagged. -/
structure TaggedGoal where
  hyps : Array (Name × TT × Option TT)
  target : TT
  userName : Option Name

def GoalView.tagged (g : GoalView R) (env : Option (Globals R) := none) : StateM (Array (Subterm R)) TaggedGoal := do
  let mut hyps := #[]
  let mut names : List Name := []
  let mut tys : List (Option (Term R)) := []
  for (x, ty, v) in g.hyps do
    let t ← ty.prettyTagged names tys env
    let v ← v.mapM (·.prettyTagged names tys env)
    hyps := hyps.push (x, t, v)
    names := x :: names
    tys := some ty :: tys
  pure { hyps, target := ← g.target.prettyTagged names tys env, userName := g.userName }

end Wiz
