import Wiz.Elab.Basic

/-!
# Pattern unification

`unify l t u` makes two values equal by solving metavariables, or fails.

The core case is a **flex** value, a neutral headed by an unsolved meta:

    ?m x₁ … xₙ  =?=  rhs

Miller's *pattern* fragment requires the spine `x₁ … xₙ` to be **distinct bound
variables**. Then the unique solution is `?m := fun x₁ … xₙ => rhs`, provided that

* `rhs` only mentions variables among `x₁ … xₙ` (a **scope check**), and
* `rhs` doesn't mention `?m` itself (an **occurs check**).

Both checks happen while **renaming** `rhs` from the current context (`cod`, `l`
variables) into the context of the solution (`dom`, `n` variables) with a *partial
renaming* that maps each `xᵢ` to its new position.

Reference: elaboration-zoo `03-holes`, which this follows closely.
-/

namespace Wiz

variable {R : Type}

/-- **Exercise 3.1.** Unfold solved metavariables at the head of a value, repeatedly.
A neutral `?m sp` whose meta has a solution `v` becomes `v` applied to `sp`. Anything
else is returned unchanged. -/
partial def force (v : Val R) : ElabM R (Val R) := do
  sorry

/-- A partial renaming from context `cod` (size `cod`) to context `dom` (size `dom`):
`ren` maps the levels of variables in the spine to their new levels. -/
structure PRen where
  dom : Lvl
  cod : Lvl
  ren : Std.HashMap Lvl Lvl

/-- Go under a binder on both sides. -/
def PRen.lift (p : PRen) : PRen :=
  { dom := p.dom + 1, cod := p.cod + 1, ren := p.ren.insert p.cod p.dom }

/-- **Exercise 3.2.** Invert a spine into a partial renaming. `gamma` is the size of the
current context. Every spine entry must force to a bound variable with an empty spine
(`.neutral (.local x) #[]`), and no variable may occur twice. Otherwise throw (at
`{}`), saying the problem is outside the pattern fragment. The i-th spine variable
maps to level i. -/
def invert (gamma : Lvl) (sp : Array (Val R)) : ElabM R PRen := do
  sorry

/-- **Exercise 3.3.** Rename a value into a term in the solution's context, checking
scope and occurs.

* A local `x` must be in `p.ren`; it becomes `.var (p.dom - ren[x] - 1)`. Otherwise
  throw a scope error.
* A meta `?m'` with `m' == m` fails the occurs check. Otherwise it is kept.
* Spines are renamed elementwise. Binders go under `p.lift` with a fresh variable
  `Val.var p.cod`. Force first! -/
partial def rename (m : Nat) (p : PRen) (v : Val R) : ElabM R (Term R) := do
  sorry

/-- **Exercise 3.4.** Solve `?m sp =?= rhs` in a context of size `gamma`: invert the
spine, rename `rhs`, wrap the result in `sp.size` lambdas, and evaluate it in the
empty environment to get the solution. Record it with `solveMeta`. -/
def solve (gamma : Lvl) (m : Nat) (sp : Array (Val R)) (rhs : Val R) : ElabM R Unit := do
  sorry

/-- Does level metavariable `m` occur in `l`? -/
def Level.occurs (m : Nat) : Level → Bool
  | .mvar m' => m == m'
  | .succ l => Level.occurs m l
  | .max a b | .imax a b => Level.occurs m a || Level.occurs m b
  | _ => false

/-- **Exercise 4.1.** Unify two universe levels. Instantiate solved metas first
(`instLevel`). Then:

* if the levels are already equivalent (`Level.equiv`), succeed;
* a lone metavariable `?u` against any level not containing it: assign it;
* `a+1 =?= b+1`: unify `a` and `b`;
* otherwise fail with a "universe level mismatch" error.

This is deliberately incomplete. `max ?u ?v =?= 1` has several solutions, and Lean
postpones such constraints instead of failing (see the optional exercises). -/
partial def unifyLevel (a b : Level) : ElabM R Unit := do
  sorry

variable [DecidableEq R]

mutual

/-- **Exercise 3.5.** Unify two values in a context of `l` variables, throwing on
failure. Force both sides first, then:

* `sort`/`sort`: `unifyLevel`.
* `pi`/`pi`: equal binder info and quantities, unify domains and codomains.
* `lam`/`lam`, and η: `lam`/anything and anything/`lam`, as in `conv`.
* Two rigid neutrals with the same head: unify the spines. For globals, "the same
  head" means the same name, with the levels unified pairwise.
* Two flex neutrals with the same meta: unify the spines (a simple approximation).
* A flex neutral against anything: `solve`.
* Anything else fails. -/
partial def unify (l : Lvl) (t u : Val R) : ElabM R Unit := do
  sorry

partial def unifySpine (l : Lvl) (sp sp' : Array (Val R)) : ElabM R Unit := do
  unless sp.size == sp'.size do throwAt {} "spine length mismatch"
  for a in sp, b in sp' do unify l a b

end

end Wiz
