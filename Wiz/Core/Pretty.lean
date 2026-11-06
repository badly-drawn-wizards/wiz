import Wiz.Core.Term
import Wiz.Rig

/-!
# Pretty printing core terms

Prints **surface syntax**, so `#check` output can be pasted back into a file.

`names` is the list of binder names in scope, innermost first (so `names[ix]` names
`var ix`). Shadowed binder names get primes so the output is unambiguous. Quantities
equal to the binder's default are omitted (see `QuantitySyntax`), and a Π whose
variable isn't used is printed as an arrow.

Precedences match the parser (`Wiz.Parser.Builtin`): arrows are 25, application is
`leadPrec` (1022) with arguments at `argPrec` (1023), and atoms are `maxPrec`.
-/

namespace Wiz

variable {R : Type} [QuantitySyntax R] [BEq R]

private def freshen (names : List Name) (x : Name) : Name :=
  if x == "_" then x else go (names.length + 1) x
where
  -- `names.length + 1` primes always suffice, so the fuel never runs out
  go : Nat → Name → Name
    | 0, y => y
    | n + 1, y => if names.contains y then go n (y ++ "'") else y

/-- Does `var ix` occur free in `t`? -/
def Term.hasVar {R : Type} (ix : Nat) : Term R → Bool
  | .var i => i == ix
  | .pi _ _ _ a b => a.hasVar ix || b.hasVar (ix + 1)
  | .lam _ b => b.hasVar (ix + 1)
  | .app f a | .ann f a => f.hasVar ix || a.hasVar ix
  | .letE _ _ ty v b => ty.hasVar ix || v.hasVar ix || b.hasVar (ix + 1)
  | .sigma _ _ a b => a.hasVar ix || b.hasVar (ix + 1)
  | .pair a b | .absurd a b => a.hasVar ix || b.hasVar ix
  | .fst t | .snd t => t.hasVar ix
  | .split _ s _ m _ _ b => s.hasVar ix || m.hasVar (ix + 1) || b.hasVar (ix + 2)
  | _ => false

/-- `Prop`, `Type`, `Type 2`, `Type u`, `Sort u`, `Type (max u v)`, ... -/
def showSort (l : Level) : String :=
  match l.toNat? with
  | some 0 => "Prop"
  | some 1 => "Type"
  | some (n + 1) => s!"Type {n}"
  | _ => match l with
    | .succ l' => s!"Type {Level.format.formatArg l'}"
    | _ => s!"Sort {Level.format.formatArg l}"

def atomicSort (l : Level) : Bool := l.toNat? == some 0 || l.toNat? == some 1

private def paren (b : Bool) (s : String) : String := if b then s!"({s})" else s

private def qtyPrefix (bi : BinderInfo) (q : R) : String :=
  let dflt := if bi == .implicit then QuantitySyntax.implicitDefault else QuantitySyntax.explicitDefault
  if q == dflt then "" else QuantitySyntax.display q ++ " "

partial def Term.prettyPrec (names : List Name) (prec : Nat) : Term R → String
  | .var ix => names[ix]?.getD s!"#{ix}"
  | .const n _ => n
  | .mvar m => s!"?m{m}"
  | .sort l => paren (prec > 1022 && !atomicSort l) (showSort l)
  | .pi x bi q dom cod =>
    if bi == .default && q == QuantitySyntax.explicitDefault && !cod.hasVar 0 then
      paren (prec > 25) s!"{dom.prettyPrec names 26} → {cod.prettyPrec ("_" :: names) 25}"
    else
      let x' := freshen names x
      let (o, c) := if bi == .implicit then ("{", "}") else ("(", ")")
      paren (prec > 25)
        s!"{o}{qtyPrefix bi q}{x'} : {dom.prettyPrec names 0}{c} → {cod.prettyPrec (x' :: names) 25}"
  | t@(.lam ..) =>
    let (xs, names', body) := lams names t #[]
    paren (prec > 0) s!"fun {" ".intercalate xs.toList} => {body.prettyPrec names' 0}"
  | t@(.app ..) =>
    let (f, args) := spine t #[]
    let args := args.map (·.prettyPrec names maxArg)
    paren (prec > 1022) s!"{f.prettyPrec names 1024} {" ".intercalate args.toList}"
  | .letE x q ty val body =>
    let x' := freshen names x
    paren (prec > 0)
      s!"let {qtyPrefix .default q}{x'} : {ty.prettyPrec names 0} := {val.prettyPrec names 0}; {body.prettyPrec (x' :: names) 0}"
  | .ann tm ty => s!"({tm.prettyPrec names 0} : {ty.prettyPrec names 0})"
  | .sigma x q a b =>
    if q == QuantitySyntax.explicitDefault && !b.hasVar 0 then
      paren (prec > 35) s!"{a.prettyPrec names 36} × {b.prettyPrec ("_" :: names) 35}"
    else
      let x' := freshen names x
      paren (prec > 35)
        s!"({qtyPrefix .default q}{x'} : {a.prettyPrec names 0}) × {b.prettyPrec (x' :: names) 35}"
  | t@(.pair ..) =>
    let parts := tuple t #[]
    s!"({", ".intercalate (parts.map (·.prettyPrec names 0)).toList})"
  | .fst t => s!"{t.prettyPrec names 1024}.1"
  | .snd t => s!"{t.prettyPrec names 1024}.2"
  | .split q s _ _ x y b =>
    let x' := freshen names x
    let y' := freshen (x' :: names) y
    paren (prec > 0)
      s!"let {qtyPrefix .default q}({x'}, {y'}) := {s.prettyPrec names 0}; {b.prettyPrec (y' :: x' :: names) 0}"
  | .unit l => match l.toNat? with
    | some 0 => "True"
    | some 1 => "Unit"
    | _ => s!"Unit.\{{l}}"
  | .tt => "()"
  | .empty l => match l.toNat? with
    | some 0 => "False"
    | some 1 => "Empty"
    | _ => s!"Empty.\{{l}}"
  | .absurd _ t => paren (prec > 1022) s!"absurd {t.prettyPrec names maxArg}"
where
  tuple : Term R → Array (Term R) → Array (Term R)
    | .pair a b, acc => tuple b (acc.push a)
    | t, acc => acc.push t
  maxArg : Nat := 1023
  lams (names : List Name) : Term R → Array Name → Array Name × List Name × Term R
    | .lam x b, acc => let x' := freshen names x; lams (x' :: names) b (acc.push x')
    | t, acc => (acc, names, t)
  spine : Term R → Array (Term R) → Term R × Array (Term R)
    | .app f a, acc => spine f (#[a] ++ acc)
    | t, acc => (t, acc)

def Term.pretty (names : List Name := []) (t : Term R) : String :=
  t.prettyPrec names 0

instance : ToString (Term R) := ⟨Term.pretty []⟩

end Wiz
