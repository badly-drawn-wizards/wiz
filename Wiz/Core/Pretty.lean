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
partial def Term.hasVar {R : Type} (ix : Nat) : Term R → Bool
  | .var i => i == ix
  | t => (t.forChildren (m := StateM Bool) (fun _ => pure ())
      (fun k c => modify (· || c.hasVar (ix + k))) |>.run false).2

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

/-- Is the quantity term the literal default for this kind of binder? -/
private def isDefaultQ (bi : BinderInfo) : Term R → Bool
  | .qlit r => r == if bi == .implicit then QuantitySyntax.implicitDefault else QuantitySyntax.explicitDefault
  | _ => false

private def qtyPrefixLit (bi : BinderInfo) (q : R) : String :=
  let dflt := if bi == .implicit then QuantitySyntax.implicitDefault else QuantitySyntax.explicitDefault
  if q == dflt then "" else QuantitySyntax.display q ++ " "

partial def Term.prettyPrec (names : List Name) (prec : Nat) : Term R → String
  | .var ix => names[ix]?.getD s!"#{ix}"
  | .const n _ => n
  | .mvar m => s!"?m{m}"
  | .qty => "Qty"
  | .qlit r => QuantitySyntax.display r
  | .sort l => paren (prec > 1022 && !atomicSort l) (showSort l)
  | .pi x bi q dom cod =>
    if bi == .default && isDefaultQ .default q && !cod.hasVar 0 then
      paren (prec > 25) s!"{dom.prettyPrec names 26} → {cod.prettyPrec ("_" :: names) 25}"
    else
      let x' := freshen names (if x == "_" then "x" else x)
      let (o, c) := if bi == .implicit then ("{", "}") else ("(", ")")
      paren (prec > 25)
        s!"{o}{qtyPrefix names bi q}{x'} : {dom.prettyPrec names 0}{c} → {cod.prettyPrec (x' :: names) 25}"
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
      s!"let {qtyPrefix names .default q}{x'} : {ty.prettyPrec names 0} := {val.prettyPrec names 0}; {body.prettyPrec (x' :: names) 0}"
  | .ann tm ty => s!"({tm.prettyPrec names 0} : {ty.prettyPrec names 0})"
  | .sigma x q a b =>
    if isDefaultQ .default q && !b.hasVar 0 then
      paren (prec > 35) s!"{a.prettyPrec names 36} × {b.prettyPrec ("_" :: names) 35}"
    else
      let x' := freshen names x
      paren (prec > 35)
        s!"({qtyPrefix names .default q}{x'} : {a.prettyPrec names 0}) × {b.prettyPrec (x' :: names) 35}"
  | t@(.pair ..) =>
    let parts := tuple t #[]
    s!"({", ".intercalate (parts.map (·.prettyPrec names 0)).toList})"
  | .fst t => s!"{t.prettyPrec names 1024}.1"
  | .snd t => s!"{t.prettyPrec names 1024}.2"
  | .split q s _ _ x y b =>
    let x' := freshen names x
    let y' := freshen (x' :: names) y
    paren (prec > 0)
      s!"let {qtyPrefix names .default q}({x'}, {y'}) := {s.prettyPrec names 0}; {b.prettyPrec (y' :: x' :: names) 0}"
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
  | .eq _ a b | .eqTy a b =>
    paren (prec > 50) s!"{a.prettyPrec names 51} = {b.prettyPrec names 51}"
  | .refl _ a | .reflTy a => paren (prec > 1022) s!"refl {a.prettyPrec names maxArg}"
  | .cast _ _ e t =>
    paren (prec > 1022) s!"cast {e.prettyPrec names maxArg} {t.prettyPrec names maxArg}"
  | .enum ls => s!"Enum [{", ".intercalate ls}]"
  | .tag ls i => s!"'{ls[i]?.getD s!"#{i}"}"
  | .ecase _ _ t bs =>
    paren (prec > 1022) s!"ecase {t.prettyPrec names maxArg} [{", ".intercalate (bs.map (·.prettyPrec names 0))}]"
  | .desc _ I => paren (prec > 1022) s!"Desc {I.prettyPrec names maxArg}"
  | .dret i => app "Desc.ret" [i]
  | .darg q S D => app "Desc.arg" [q, S, D]
  | .drec q j D => app "Desc.rec" [q, j, D]
  | .delim _ P a b c D => app "Desc.elim" [P, a, b, c, D]
  | .mu _ _ D i => app "μ" [D, i]
  | .con x => app "con" [x]
  | .ind _ _ _ _ P m i x => app "ind" [P, m, i, x]
  | .nu _ _ D i => app "ν" [D, i]
  | .out x => app "out" [x]
  | .coit _ _ _ S st i s => app "coit" [S, st, i, s]
  | .transp _ _ P p _ e =>
    paren (prec > 1022)
      s!"transp {P.prettyPrec names maxArg} {p.prettyPrec names maxArg} {e.prettyPrec names maxArg}"
where
  app (f : String) (args : List (Term R)) : String :=
    paren (prec > 1022) (" ".intercalate (f :: args.map (·.prettyPrec names maxArg)))
  tuple : Term R → Array (Term R) → Array (Term R)
    | .pair a b, acc => tuple b (acc.push a)
    | t, acc => acc.push t
  maxArg : Nat := 1023
  /-- `1 `, `0 `, `%q `, or nothing for the default -/
  qtyPrefix (names : List Name) (bi : BinderInfo) : Term R → String
    | .qlit r => qtyPrefixLit bi r
    | q => s!"%{q.prettyPrec names 1024} "
  lams (names : List Name) : Term R → Array Name → Array Name × List Name × Term R
    | .lam x b, acc =>
      let x' := freshen names (if x == "_" && b.hasVar 0 then "x" else x)
      lams (x' :: names) b (acc.push x')
    | t, acc => (acc, names, t)
  spine : Term R → Array (Term R) → Term R × Array (Term R)
    | .app f a, acc => spine f (#[a] ++ acc)
    | t, acc => (t, acc)

def Term.pretty (names : List Name := []) (t : Term R) : String :=
  t.prettyPrec names 0

instance : ToString (Term R) := ⟨Term.pretty []⟩

end Wiz
