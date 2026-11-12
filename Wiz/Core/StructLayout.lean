import Wiz.Core.Term

/-!
# The layout of a structure (stage 13h)

How the Σ of a structure is laid out, read from its declaration: see `Elab/Struct.lean`,
which uses it for structure patterns and updates. It lives in the core so that the
printer can show `S.mk` applications back as structure updates (13p).
-/

namespace Wiz

variable {R : Type}

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
constructor of its description). `none` for a structure that is opaque here (13b).
`isZero`: is a Σ binder's quantity `0` (for `StructComp.marker`'s flag). -/
def structLayoutWith? (isZero : Term R → Bool) (g : Globals R) (S : Name) : Option StructLayout := do
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
      if isPhantomName x then (walk i rest).map (.marker (isZero q) :: ·)
      else if fields[i]? == some x then (walk (i + 1) rest).map (.field i :: ·)
      else none
    | _ =>
      if i == fields.length then some [.marker false]
      else if i + 1 == fields.length then some [.field i]
      else none
  let comps ← walk 0 body
  pure { name := S, nParams := nΔ, fields, comps }

namespace StructLayout


/-- The component that holds field `i`. -/
def fieldComp? (L : StructLayout) (i : Nat) : Option Nat := L.comps.idxOf? (.field i)

/-- Component `k` of `t`, by projections. -/
def compTerm (L : StructLayout) (k : Nat) (t : Term R) : Term R :=
  let base := (List.range k).foldl (fun t _ => Term.snd t) t
  if k + 1 == L.comps.length then base else .fst base

end StructLayout

end Wiz
