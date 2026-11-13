import Wiz.Core.Eval
import Wiz.Core.StructLayout
import Wiz.Syntax.Basic

/-!
# The layout of a structure (stage 13h)

A `structure S Δ where f₁ : F₁ … fₙ : Fₙ` is a definition `S := λ Δ. Σ …` (see
`elabStructure`). Everything that takes a structure apart **by its encoding**
(structure patterns, `let ⟨a, b⟩ := s`, `{ s with f := v }`) reads the encoding through
`StructLayout`, computed here from the declaration itself, so a change of encoding is a
change to `structLayout?` (and to nothing else in the elaboration of patterns and
updates).

Today the Σ is `(f₁ : F₁) × … × (fₙ : Fₙ) × tail`, with `tail` a singleton that is not
a field (`Unit`, or the marker and phantom tail `(0 fields✝ : …) → Unit`, 22i). The
layout is a list of **components** of the right-nested Σ, the last one being the final
second projection; each is a field or a marker. `structLayout?` classifies them from the
declaration (a Σ binder with a phantom name is a marker, any other Σ binder a field, and
the final component is a field exactly if `S.mk` has a field left for it), so the
planned encoding with the marker as a 0-quantity component before the last field
(`f₁ × … × (0 fields✝ : M) × Fₙ`) is read correctly too.
-/

namespace Wiz.Elab

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

/-- The layout of the structure `S` (`structLayoutWith?`, `Core/StructLayout.lean`). -/
def structLayout? (g : Globals R) (S : Name) : Option StructLayout :=
  structLayoutWith? (· == .qlit 0) g S

/-- The structure a type is an application of: its name, universe levels and arguments.
Looks through definitions that unfold to one (`def T := S A`). Force metavariables
first. A structure that is opaque here (13b) is found too (it has no layout). -/
partial def structHead? (g : Globals R) : Val R → Option (Name × List Level × List (Val R))
  | .unfold S us sp v =>
    if g.contains (S ++ ".mk") && !g.contains (S ++ ".desc") && (structLayout? g S).isSome then
      some (S, us, sp.toList.filterMap fun e => match e with
        | .app a => some a
        | _ => none)
    else structHead? g v.get
  | .neutral (.global S us) sp =>
    if g.contains (S ++ ".mk") && !g.contains (S ++ ".desc") && (g.opaqueTo? S).isSome then
      some (S, us, sp.toList.filterMap fun e => match e with
        | .app a => some a
        | _ => none)
    else none
  | _ => none

end Elab

namespace StructLayout

/-- The pattern for `S.mk p₀ … pₙ₋₁` as a tuple pattern over the components, with `_`
for the markers. -/
def tuplePattern (L : StructLayout) (info : SourceInfo) (ps : List Syntax) : Syntax :=
  let hole : Syntax := .node {} "term.hole" #[.atom {} "_"]
  let items := L.comps.map fun c => match c with
    | .field i => ps[i]?.getD hole
    | .marker _ => hole
  match items with
  | [] => hole
  | [p] => p
  | p :: rest =>
    let sep := (rest.flatMap fun q => [Syntax.atom {} ",", q]).drop 1
    .node info "term.tuple" #[.atom {} "(", p, .atom {} ",", .node {} "null" sep.toArray, .atom {} ")"]

end StructLayout

end Wiz
