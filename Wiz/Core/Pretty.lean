import Wiz.Core.Term

/-!
# Pretty printing core terms

`names` is the list of binder names in scope, innermost first (so `names[ix]` names
`var ix`). Shadowed binder names get primes so the output is unambiguous.
-/

namespace Wiz

variable {R : Type} [ToString R]

private def freshen (names : List Name) (x : Name) : Name :=
  if x == "_" then x else go (names.length + 1) x
where
  -- `names.length + 1` primes always suffice, so the fuel never runs out
  go : Nat → Name → Name
    | 0, y => y
    | n + 1, y => if names.contains y then go n (y ++ "'") else y

/-- Precedence levels: 0 = binders (λ, Π, let), 1 = application, 2 = atoms. -/
partial def Term.prettyPrec (names : List Name) (prec : Nat) : Term R → String
  | .var ix => names[ix]?.getD s!"#{ix}"
  | .const n => n
  | .sort l => if l == 0 then "Type" else s!"Type {l}"
  | .pi x q dom cod =>
    let x' := freshen names x
    let s := s!"({x'} :{q} {dom.prettyPrec names 0}) → {cod.prettyPrec (x' :: names) 0}"
    paren (prec > 0) s
  | .lam x body =>
    let x' := freshen names x
    paren (prec > 0) s!"λ {x'}. {body.prettyPrec (x' :: names) 0}"
  | .app f a =>
    paren (prec > 1) s!"{f.prettyPrec names 1} {a.prettyPrec names 2}"
  | .letE x q ty val body =>
    let x' := freshen names x
    paren (prec > 0)
      s!"let {x'} :{q} {ty.prettyPrec names 0} := {val.prettyPrec names 0}; {body.prettyPrec (x' :: names) 0}"
  | .ann tm ty => s!"({tm.prettyPrec names 0} : {ty.prettyPrec names 0})"
where
  paren (b : Bool) (s : String) : String := if b then s!"({s})" else s

def Term.pretty (names : List Name := []) (t : Term R) : String :=
  t.prettyPrec names 0

instance : ToString (Term R) := ⟨Term.pretty []⟩

end Wiz
