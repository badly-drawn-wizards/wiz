import Wiz.Core.Eval
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

/-- A component of a structure's Σ. -/
inductive StructComp where
  /-- the `i`-th field of `S.mk` -/
  | field (i : Nat)
  /-- not a field (the marker or phantom tail). `erased`: its Σ binds it at quantity 0,
  so a linear split may leave it unused; the final component never is. -/
  | marker (erased : Bool)
  deriving BEq, Inhabited

/-- How the Σ of the structure `name` is laid out. -/
structure StructLayout where
  name : Name
  /-- the number of parameters (`S.mk` takes them implicitly) -/
  nParams : Nat
  /-- the fields, in the order `S.mk` takes them -/
  fields : List Name
  /-- the components of the right-nested Σ, in order; the last is the final `snd` -/
  comps : List StructComp
  deriving Inhabited

/-- The layout of the structure `S`, if `S` is one: a definition `λ Δ. Σ…` with a
constructor `S.mk : {Δ} → fields → S Δ` (and not a data type, whose `mk` is a
constructor of its description). `none` for a structure that is opaque here (13b). -/
def structLayout? (g : Globals R) (S : Name) : Option StructLayout := do
  if g.contains (S ++ ".desc") then none
  let d ← g.find? S
  let mk ← g.find? (S ++ ".mk")
  let body ← d.value
  let rec nPis : Term R → Nat
    | .pi _ _ _ _ b _ => nPis b + 1
    | _ => 0
  let nΔ := nPis d.type
  let rec strip : Nat → Term R → Option (Term R)
    | 0, t => some t
    | n + 1, .lam _ b => strip n b
    | _, _ => none
  let body ← strip nΔ body
  -- `S.mk`'s binders after the parameters are the fields
  let rec piNames : Term R → List Name
    | .pi x _ _ _ b _ => x :: piNames b
    | _ => []
  let fields := (piNames mk.type).drop nΔ
  let rec walk (i : Nat) : Term R → Option (List StructComp)
    | .sigma x q _ rest _ =>
      if isPhantomName x then (walk i rest).map (.marker (q == .qlit 0) :: ·)
      else if fields[i]? == some x then (walk (i + 1) rest).map (.field i :: ·)
      else none
    | _ =>
      if i == fields.length then some [.marker false]
      else if i + 1 == fields.length then some [.field i]
      else none
  let comps ← walk 0 body
  pure { name := S, nParams := nΔ, fields, comps }

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

namespace StructLayout

/-- The component that holds field `i`. -/
def fieldComp? (L : StructLayout) (i : Nat) : Option Nat := L.comps.idxOf? (.field i)

/-- Component `k` of `t`, by projections. -/
def compTerm (L : StructLayout) (k : Nat) (t : Term R) : Term R :=
  let base := (List.range k).foldl (fun t _ => Term.snd t) t
  if k + 1 == L.comps.length then base else .fst base

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

end Wiz.Elab
