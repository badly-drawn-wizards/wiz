/-!
# Universe levels of the spec

Levels are Lean 4's (`0`, `l+1`, `max`, `imax`, parameters). A declaration is checked
with its parameters symbolic (prenex polymorphism), so every side condition on levels
quantifies over all assignments of the parameters:

* `Lvl.Equiv a b`: equal under every assignment;
* `Lvl.NeverZero l`: nonzero under every assignment;
* `Lvl.IsZero l`: zero under every assignment.

These are the *specification*. `Lvl.equiv`, `Lvl.neverZero`, `Lvl.isZero` are a total
decision procedure for them, written independently of `Wiz/Core/Level.lean`: split on
which parameters are `0` (that decides every `imax`), then compare max-plus normal forms.
Unlike the kernel's `Level.equiv` (fuel 8) it is complete, and exponential in the number
of parameters, which is small.
-/

namespace WizMeta

inductive Lvl where
  | zero
  | succ (l : Lvl)
  | max (a b : Lvl)
  | imax (a b : Lvl)
  /-- the `i`-th level parameter of the enclosing declaration -/
  | param (i : Nat)
  deriving Repr, Inhabited, BEq, DecidableEq

namespace Lvl

def ofNat : Nat → Lvl
  | 0 => zero
  | n + 1 => succ (ofNat n)

instance {n : Nat} : OfNat Lvl n := ⟨ofNat n⟩

/-- The meaning of a level under an assignment of the parameters. -/
def eval (ρ : Nat → Nat) : Lvl → Nat
  | zero => 0
  | succ l => eval ρ l + 1
  | max a b => Nat.max (eval ρ a) (eval ρ b)
  | imax a b => if eval ρ b = 0 then 0 else Nat.max (eval ρ a) (eval ρ b)
  | param i => ρ i

/-- `a` and `b` are the same level, whatever the parameters stand for. -/
def Equiv (a b : Lvl) : Prop := ∀ ρ, eval ρ a = eval ρ b
/-- `l` is not `0` (so `Sort l` is not `Prop`), whatever the parameters stand for. -/
def NeverZero (l : Lvl) : Prop := ∀ ρ, eval ρ l ≠ 0
/-- `l` is `0` (so `Sort l` is `Prop`), whatever the parameters stand for. -/
def IsZero (l : Lvl) : Prop := ∀ ρ, eval ρ l = 0

/-- Substitute levels for the parameters (a parameter out of range becomes `0`; the
checker rejects such a term before it gets here). -/
def inst (us : List Lvl) : Lvl → Lvl
  | zero => zero
  | succ l => succ (inst us l)
  | max a b => max (inst us a) (inst us b)
  | imax a b => imax (inst us a) (inst us b)
  | param i => us.getD i zero

/-- One more than the largest parameter index (`0` for a closed level). -/
def bound : Lvl → Nat
  | zero => 0
  | succ l => bound l
  | max a b | imax a b => Nat.max (bound a) (bound b)
  | param i => i + 1

/-! ## The decision procedure -/

/-- A max-plus form `max(c, max_i (p_i' + k_i))`, where `p_i' = p_i - 1` for a parameter
`p_i` known to be nonzero. `ks` is sorted by parameter, one entry each. -/
structure MP where
  c : Nat
  ks : List (Nat × Nat)
  deriving BEq, Repr

namespace MP

def insert (p k : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(p, k)]
  | (q, j) :: r =>
    if p < q then (p, k) :: (q, j) :: r
    else if p == q then (q, Nat.max j k) :: r
    else (q, j) :: insert p k r

def merge (a b : MP) : MP :=
  ⟨Nat.max a.c b.c, a.ks.foldl (fun acc (p, k) => insert p k acc) b.ks⟩

def succ (a : MP) : MP := ⟨a.c + 1, a.ks.map fun (p, k) => (p, k + 1)⟩

/-- The form is `0` under every assignment: a nonzero parameter is at least `1`, and it
is written `p' + k` with `k ≥ 1`. -/
def isZero (a : MP) : Bool := a.c == 0 && a.ks.isEmpty

/-- The constant is redundant when some `p' + k` is always at least `c`. -/
def canon (a : MP) : MP := if a.ks.any (fun (_, k) => a.c ≤ k) then ⟨0, a.ks⟩ else a

end MP

/-- The max-plus form of a level, given which parameters are `0` (`z p = true`). -/
def toMP (z : Nat → Bool) : Lvl → MP
  | zero => ⟨0, []⟩
  | succ l => (toMP z l).succ
  | max a b => (toMP z a).merge (toMP z b)
  | imax a b => let b' := toMP z b; if b'.isZero then ⟨0, []⟩ else (toMP z a).merge b'
  | param i => if z i then ⟨0, []⟩ else ⟨0, [(i, 1)]⟩

/-- All assignments of "is zero" to the parameters below `n`. -/
def splits : Nat → List (Nat → Bool)
  | 0 => [fun _ => false]
  | n + 1 => (splits n).flatMap fun z => [z, fun i => if i == n then true else z i]

def equiv (a b : Lvl) : Bool :=
  (splits (Nat.max a.bound b.bound)).all fun z => (toMP z a).canon == (toMP z b).canon

def neverZero (l : Lvl) : Bool := (splits l.bound).all fun z => !(toMP z l).isZero
def isZero (l : Lvl) : Bool := (splits l.bound).all fun z => (toMP z l).isZero
def le (a b : Lvl) : Bool := equiv (max a b) b

/-- A closed level's value. -/
def toNat? (l : Lvl) : Option Nat := if l.bound == 0 then some (eval (fun _ => 0) l) else none

def prettyRaw : Lvl → String
  | zero => "0"
  | succ l => s!"({prettyRaw l}+1)"
  | max a b => s!"(max {prettyRaw a} {prettyRaw b})"
  | imax a b => s!"(imax {prettyRaw a} {prettyRaw b})"
  | param i => s!"u{i}"

def pretty (l : Lvl) : String := match l.toNat? with
  | some n => toString n
  | none => prettyRaw l

end Lvl
end WizMeta
