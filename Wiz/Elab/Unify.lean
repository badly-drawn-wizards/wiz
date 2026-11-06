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
A neutral `?m sp` whose meta has a solution `v` becomes `v` with the eliminations of
`sp` applied (`vElims`). Anything else is returned unchanged. -/
partial def force (v : Val R) : ElabM R (Val R) := do
  --<sol
  match v with
  | .neutral (.mvar m) sp =>
    match (← lookupMeta m).solution with
    | some sol => force (vElims (← getGlobals) sol sp)
    | none => pure v
  | _ => pure v
  --|ex
  --| sorry
  --sol>

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
  --<sol
  let mut ren : Std.HashMap Lvl Lvl := {}
  let mut dom := 0
  for e in sp do
    let .app v := e | throwAt {} "unification problem is outside the pattern fragment"
    match ← force v with
    | .neutral (.local x) #[] =>
      if ren.contains x then throwAt {} "non-linear spine: a variable is repeated"
      ren := ren.insert x dom
      dom := dom + 1
    | _ => throwAt {} "unification problem is outside the pattern fragment"
  pure { dom, cod := gamma, ren }
  --|ex
  --| sorry
  --sol>

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
  --<sol
  let goSp (h : Term R) (sp : Array (Elim R)) : ElabM R (Term R) :=
    sp.foldlM (init := h) fun acc e => match e with
      | .app a => return .app acc (← rename m p a)
      | .fst => pure (.fst acc)
      | .snd => pure (.snd acc)
      | .split q z mo x y b => do
        let mo' ← rename m p.lift (← instM mo (Val.var p.cod))
        let g ← getGlobals
        let b' ← rename m p.lift.lift (Closure.inst2 g b (Val.var p.cod) (Val.var (p.cod + 1)))
        pure (.split q acc z mo' x y b')
      | .absurd mo => return .absurd (← rename m p mo) acc
  match ← force v with
  | .neutral (.local x) sp =>
    match p.ren[x]? with
    | some x' => goSp (.var (p.dom - x' - 1)) sp
    | none => throwAt {} "a variable escapes the scope of the hole being solved"
  | .neutral (.global n us) sp => goSp (.const n us) sp
  | .neutral (.mvar m') sp =>
    if m == m' then throwAt {} s!"occurs check: ?m{m} would have to contain itself"
    else goSp (.mvar m') sp
  | .sort l => pure (.sort l)
  | .pi x bi q a b =>
    return .pi x bi q (← rename m p a) (← rename m p.lift (← instM b (Val.var p.cod)))
  | .lam x b => return .lam x (← rename m p.lift (← instM b (Val.var p.cod)))
  | .sigma x q a b =>
    return .sigma x q (← rename m p a) (← rename m p.lift (← instM b (Val.var p.cod)))
  | .pair a b => return .pair (← rename m p a) (← rename m p b)
  | .unit l => pure (.unit l)
  | .tt => pure .tt
  | .empty l => pure (.empty l)
  --|ex
  --| sorry
  --sol>

/-- **Exercise 3.4.** Solve `?m sp =?= rhs` in a context of size `gamma`: invert the
spine, rename `rhs`, wrap the result in `sp.size` lambdas, and evaluate it in the
empty environment to get the solution. Record it with `solveMeta`. -/
def solve (gamma : Lvl) (m : Nat) (sp : Array (Elim R)) (rhs : Val R) : ElabM R Unit := do
  --<sol
  let p ← invert gamma sp
  let body ← rename m p rhs
  let sol := (List.range sp.size).foldl (fun t i => Term.lam s!"x{sp.size - i - 1}" t) body
  solveMeta m (eval (← getGlobals) [] sol)
  --|ex
  --| sorry
  --sol>

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
  --<sol
  let a ← instLevel a
  let b ← instLevel b
  if a.equiv b then return
  match a, b with
  | .mvar m, l | l, .mvar m =>
    if Level.occurs m l then throwAt {} s!"universe level mismatch: {a} vs {b}"
    modify fun s => { s with levelMetas := s.levelMetas.set! m (some l) }
  | .succ a', .succ b' => unifyLevel a' b'
  | _, _ => throwAt {} s!"universe level mismatch: {a} vs {b}"
  --|ex
  --| sorry
  --sol>

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
* Anything else fails.

**Exercise 4.8** (stage 4b): `sigma`, `pair` (with η: `(a, b) =?= t` unifies `a` with
`t.1` and `b` with `t.2`), `unit`, `tt`, `empty`; and the other eliminations in
`unifySpine`. -/
partial def unify (l : Lvl) (t u : Val R) : ElabM R Unit := do
  --<sol
  match ← force t, ← force u with
  | .sort a, .sort b => unifyLevel a b
  | .pi _ bi q a b, .pi _ bi' q' a' b' =>
    unless bi == bi' do throwAt {} "implicit vs explicit binder mismatch"
    unless q == q' do throwAt {} "quantity mismatch"
    unify l a a'
    unify (l + 1) (← instM b (Val.var l)) (← instM b' (Val.var l))
  | .sigma _ q a b, .sigma _ q' a' b' =>
    unless q == q' do throwAt {} "quantity mismatch"
    unify l a a'
    unify (l + 1) (← instM b (Val.var l)) (← instM b' (Val.var l))
  | .pair a b, .pair a' b' => unify l a a'; unify l b b'
  | .pair a b, t'@(.neutral ..) => unify l a (vFst t'); unify l b (vSnd t')
  | t'@(.neutral ..), .pair a b => unify l (vFst t') a; unify l (vSnd t') b
  | .unit u, .unit u' | .empty u, .empty u' => unifyLevel u u'
  | .tt, .tt => pure ()
  | .lam _ b, .lam _ b' => unify (l + 1) (← instM b (Val.var l)) (← instM b' (Val.var l))
  | .lam _ b, t' => unify (l + 1) (← instM b (Val.var l)) (← vAppM t' (Val.var l))
  | t', .lam _ b => unify (l + 1) (← vAppM t' (Val.var l)) (← instM b (Val.var l))
  | .neutral (.mvar m) sp, .neutral (.mvar m') sp' =>
    if m == m' then unifySpine l sp sp' else solve l m sp (.neutral (.mvar m') sp')
  | .neutral (.mvar m) sp, t' => solve l m sp t'
  | t', .neutral (.mvar m) sp => solve l m sp t'
  | .neutral (.global n us) sp, .neutral (.global n' us') sp' =>
    unless n == n' && us.length == us'.length do throwAt {} "rigid mismatch"
    for a in us, b in us' do unifyLevel a b
    unifySpine l sp sp'
  | .neutral h sp, .neutral h' sp' =>
    if h.equiv h' then unifySpine l sp sp' else throwAt {} "rigid mismatch"
  | _, _ => throwAt {} "rigid mismatch"
  --|ex
  --| sorry
  --sol>

partial def unifySpine (l : Lvl) (sp sp' : Array (Elim R)) : ElabM R Unit := do
  unless sp.size == sp'.size do throwAt {} "spine length mismatch"
  let g ← getGlobals
  for e in sp, e' in sp' do
    match e, e' with
    | .app a, .app b => unify l a b
    | .fst, .fst | .snd, .snd => pure ()
    | .split q _ m _ _ b, .split q' _ m' _ _ b' =>
      unless q == q' do throwAt {} "quantity mismatch"
      unify (l + 1) (← instM m (Val.var l)) (← instM m' (Val.var l))
      unify (l + 2) (Closure.inst2 g b (Val.var l) (Val.var (l + 1)))
        (Closure.inst2 g b' (Val.var l) (Val.var (l + 1)))
    | .absurd m, .absurd m' => unify l m m'
    | _, _ => throwAt {} "spine mismatch"

end

end Wiz
