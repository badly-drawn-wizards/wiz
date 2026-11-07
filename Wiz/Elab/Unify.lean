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

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

/-- **Exercise 3.1.** Unfold solved metavariables at the head of a value, repeatedly.
A neutral `?m sp` whose meta has a solution `v` becomes `v` with the eliminations of
`sp` applied (`vElims`). Anything else is returned unchanged. -/
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
current context. Every spine entry must be an application (`Elim.app v`) whose
argument forces to a bound variable with an empty spine (`.neutral (.local x) #[]`),
and no variable may occur twice. Otherwise throw (at `{}`), saying the problem is
outside the pattern fragment. The i-th spine variable maps to level i. -/
def invert (gamma : Lvl) (sp : Array (Elim R)) : ElabM R PRen := do
  sorry

/-- **Exercise 3.3.** Rename a value into a term in the solution's context, checking
scope and occurs.

* A local `x` must be in `p.ren`; it becomes `.var (p.dom - ren[x] - 1)`. Otherwise
  throw a scope error.
* A meta `?m'` with `m' == m` fails the occurs check. Otherwise it is kept.
* Spines are renamed elimination by elimination. Binders go under `p.lift` with a
  fresh variable `Val.var p.cod` (twice for a `split` body). Force first!

(The structural types of stage 4b are already handled in the solution's style. Add
them when you get there.) -/
partial def rename (m : Nat) (p : PRen) (v : Val R) : ElabM R (Term R) := do
  if let .natLit n ← force v then return .natLit n
  sorry

/-- **Exercise 3.4.** Solve `?m sp =?= rhs` in a context of size `gamma`: invert the
spine, rename `rhs`, wrap the result in `sp.size` lambdas, and evaluate it in the
empty environment to get the solution. Record it with `solveMeta`. -/
def solve (gamma : Lvl) (m : Nat) (sp : Array (Elim R)) (rhs : Val R) : ElabM R Unit := do
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
* Anything else fails.

**Exercise 4.8** (stage 4b): `sigma`, `pair` (with η: `(a, b) =?= t` unifies `a` with
`t.1` and `b` with `t.2`), `unit`, `tt`, `empty`; and the other eliminations in
`unifySpine`. -/
partial def unify (l : Lvl) (t u : Val R) : ElabM R Unit := do
  -- numerals: compare two directly, or else look one step inside (`vNatView`)
  let g ← getGlobals
  let (t, u) ← match ← force t, ← force u with
    | .natLit n, .natLit m => if n == m then return () else throwAt {} s!"{n} ≠ {m}"
    | t, u => pure (vNatView g t, vNatView g u)
  sorry

/-- Rigid heads: the same variable, the same global (levels unified), or the same
stuck observational construct (components unified). Any two proofs are equal. -/
partial def unifyHead (l : Lvl) (h h' : Head R) : ElabM R Unit := do
  let isProof : Head R → Bool
    | .refl .. | .reflTy _ | .transp .. => true
    | _ => false
  match h, h' with
  | .global n us, .global n' us' =>
    unless n == n' && us.length == us'.length do throwAt {} "rigid mismatch"
    for a in us, b in us' do unifyLevel a b
  | .eq A a b, .eq A' a' b' => unify l A A'; unify l a a'; unify l b b'
  | .eqTy A B, .eqTy A' B' => unify l A A'; unify l B B'
  | .cast A B _ t, .cast A' B' _ t' => unify l A A'; unify l B B'; unify l t t'
  | _, _ =>
    unless (isProof h && isProof h') || h.equiv h' do throwAt {} "rigid mismatch"

partial def unifySpine (l : Lvl) (sp sp' : Array (Elim R)) : ElabM R Unit := do
  unless sp.size == sp'.size do throwAt {} "spine length mismatch"
  let g ← getGlobals
  for e in sp, e' in sp' do
    match e, e' with
    | .app a, .app b => unify l a b
    | .fst, .fst | .snd, .snd => pure ()
    | .split q _ m _ _ b, .split q' _ m' _ _ b' =>
      unify l q q'
      unify (l + 1) (← instM m (Val.var l)) (← instM m' (Val.var l))
      unify (l + 2) (Closure.inst2 g b (Val.var l) (Val.var (l + 1)))
        (Closure.inst2 g b' (Val.var l) (Val.var (l + 1)))
    | .absurd m, .absurd m' => unify l m m'
    | .ecase _ m env bs, .ecase _ m' env' bs' =>
      unify (l + 1) (← instM m (Val.var l)) (← instM m' (Val.var l))
      unless bs.length == bs'.length do throwAt {} "spine mismatch"
      for b in bs, b' in bs' do unify l (eval g env b) (eval g env' b')
    | .delim v P a b c h, .delim v' P' a' b' c' h' =>
      unifyLevel v v'
      for (x, y) in [(P, P'), (a, a'), (b, b'), (c, c'), (h, h')] do unify l x y
    | .ind u I D v P mt i, .ind u' I' D' v' P' mt' i' =>
      unifyLevel u u'; unifyLevel v v'
      for (x, y) in [(I, I'), (D, D'), (P, P'), (mt, mt'), (i, i')] do unify l x y
    | .out, .out => pure ()
    | .scase u I D v P f s i, .scase u' I' D' v' P' f' s' i' =>
      unifyLevel u u'; unifyLevel v v'
      for (x, y) in [(I, I'), (D, D'), (P, P'), (f, f'), (s, s'), (i, i')] do unify l x y
    | .sfix u I D v P f s i, .sfix u' I' D' v' P' f' s' i' =>
      unifyLevel u u'; unifyLevel v v'
      for (x, y) in [(I, I'), (D, D'), (P, P'), (f, f'), (s, s'), (i, i')] do unify l x y
    | _, _ => throwAt {} "spine mismatch"

end

end Wiz
