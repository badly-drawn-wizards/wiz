import Wiz.Rig

/-!
# Quantity polynomials

With quantity polymorphism (stage 4d), a binder's quantity may be a *variable*,
`(%q x : A) → B`, and usages become expressions such as `q + 1` or `q * r`. Usage
vectors therefore hold **polynomials** over the rig, whose variables are the de Bruijn
levels of `Qty`-typed binders.

A polynomial is a sum of monomials `c · x₁ · … · xₙ`. The normal form keeps monomials
sorted by their (sorted) variable lists, merges equal monomials, and drops zero
coefficients. The rig is commutative (`Rig.mul_comm`), which makes this a normal form.

`used ≤ declared` must hold for **every** value of the variables, so for symbolic
polynomials it is decided by trying every assignment over `QRig.elements?`. This
works for finite rigs such as `{0, 1, ω}`. For infinite ones, only polynomials that
are syntactically equal are accepted.
-/

namespace Wiz

/-- Monomial variables (sorted levels, with repetition) and a coefficient. -/
abbrev QPoly (R : Type) := List (List Nat × R)

namespace QPoly

variable {R : Type} [QRig R] [DecidableEq R]

private def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

private def monoLt (a b : List Nat) : Bool :=
  a.length < b.length || (a.length == b.length && compare a b == .lt)

private def addMono (m : List Nat × R) : QPoly R → QPoly R
  | [] => if m.2 == 0 then [] else [m]
  | n :: ns =>
    if m.1 == n.1 then
      let c := m.2 + n.2
      if c == 0 then ns else (n.1, c) :: ns
    else if monoLt m.1 n.1 then (if m.2 == 0 then n :: ns else m :: n :: ns)
    else n :: addMono m ns

def const (r : R) : QPoly R := addMono ([], r) []
def var (l : Nat) : QPoly R := [([l], 1)]

def add (p q : QPoly R) : QPoly R := p.foldl (fun acc m => addMono m acc) q

def mul (p q : QPoly R) : QPoly R :=
  p.foldl (init := []) fun acc (xs, a) =>
    q.foldl (init := acc) fun acc (ys, b) => addMono (xs.foldl (fun zs x => insertSorted x zs) ys, a * b) acc

instance : Add (QPoly R) := ⟨add⟩
instance : Mul (QPoly R) := ⟨mul⟩

def vars (p : QPoly R) : List Nat := (p.flatMap (·.1)).eraseDups

/-- The constant value, if there are no variables. -/
def isConst? (p : QPoly R) : Option R :=
  if p.all (·.1.isEmpty) then some (p.foldl (fun acc m => acc + m.2) 0) else none

def eval (assign : Nat → R) (p : QPoly R) : R :=
  p.foldl (fun acc (xs, c) => acc + xs.foldl (fun m x => m * assign x) c) 0

/-- Every assignment of `vs` to elements of `elems`. -/
def assignments (elems : List R) : List Nat → List (List (Nat × R))
  | [] => [[]]
  | v :: vs => (assignments elems vs).flatMap fun a => elems.map fun e => (v, e) :: a

/-- **Exercise 4.15.** `p ≤ q` for polynomials with variables: if the rig is finite
(`QRig.elements?`), check `QRig.le` under every assignment of the variables of `p`
and `q` (`assignments`, `eval`); otherwise accept only `p == q`. -/
def leSymbolic (p q : QPoly R) : Bool :=
  --<sol
  match QRig.elements? (R := R) with
  | some elems =>
    (assignments elems (vars p ++ vars q).eraseDups).all fun a =>
      let f := fun x => ((a.find? (·.1 == x)).map (·.2)).getD 0
      QRig.le (eval f p) (eval f q)
  | none => p == q
  --|ex
  --| sorry
  --sol>

/-- `used ≤ declared`. Constant polynomials just use `QRig.le`. -/
def le (p q : QPoly R) : Bool :=
  match p.isConst?, q.isConst? with
  | some a, some b => QRig.le a b
  | _, _ => leSymbolic p q

/-- Equality as functions: syntactic, or (finite rigs) under every assignment. -/
def equiv (p q : QPoly R) : Bool :=
  p == q || match QRig.elements? (R := R) with
    | some elems =>
      (assignments elems (vars p ++ vars q).eraseDups).all fun a =>
        let f := fun x => ((a.find? (·.1 == x)).map (·.2)).getD 0
        eval f p == eval f q
    | none => false

/-- The least upper bound of two usages in the `le` order, used for the branches of a
case (alternatives): `0 ⊔ 1 = ω` in `{0, 1, ω}`. Exists for equivalent polynomials,
and for constants of a finite rig with a least common upper bound; otherwise `none`. -/
def join? (p q : QPoly R) : Option (QPoly R) :=
  if equiv p q then some p else
  match p.isConst?, q.isConst?, QRig.elements? (R := R) with
  | some a, some b, some elems =>
    let ups := elems.filter fun e => QRig.le a e && QRig.le b e
    (ups.find? fun e => ups.all (QRig.le e ·)).map const
  | _, _, _ => none

def toString [ToString R] (p : QPoly R) : String :=
  if p.isEmpty then "0" else
  " + ".intercalate <| p.map fun (xs, c) =>
    let vs := xs.map (s!"q{·}")
    if xs.isEmpty then s!"{c}" else if c == 1 then " * ".intercalate vs
    else " * ".intercalate (s!"{c}" :: vs)

instance [ToString R] : ToString (QPoly R) := ⟨toString⟩

end QPoly

end Wiz
