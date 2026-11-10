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
partial def forceMeta (v : Val R) : ElabM R (Val R) := do
  sorry

/-- Unfold solved metavariables and glued definitions at the head: the value's shape,
ready to match on. (`forceMeta` keeps glued heads, for unification.) -/
partial def force (v : Val R) : ElabM R (Val R) := do
  match ← forceMeta v with
  | .unfold _ _ _ v => force v.get
  | .lazyInd _ _ _ _ _ _ _ _ _ v => force v.get
  | v => pure v

/-- An equation stuck on a metavariable (its type or a side) computes once the
metavariable is solved: recompute it (`none` if nothing changed). -/
def recomputeEq? (v : Val R) : ElabM R (Option (Val R)) := do
  let .neutral (.eq A a b) sp := v | return none
  let solved (v : Val R) : ElabM R Bool := do
    match v with
    | .neutral (.mvar m) _ => return (← lookupMeta m).solution.isSome
    | _ => return false
  if (← solved A) || (← solved a) || (← solved b) then
    let g ← getGlobals
    return some (vElims g (vEq g (← forceMeta A) (← forceMeta a) (← forceMeta b)) sp)
  else return none

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
and a variable that occurs twice is left out of the renaming (the solution may not use
it). Otherwise throw (at `{}`), saying the problem is outside the pattern fragment.
The i-th spine variable maps to level i. -/
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
  -- (given) a glued value keeps its name in the solution
  if let .unfold n us sp _ ← forceMeta v then return ← rename m p (.neutral (.global n us) sp)
  -- (given) and glued induction on a numeral keeps its folded form
  if let .lazyInd lv I D w P mt i x sp _ ← forceMeta v then
    let t := Term.ind lv (← rename m p I) (← rename m p D) w (← rename m p P) (← rename m p mt) (← rename m p i) (← rename m p x)
    return ← sp.foldlM (fun t e => match e with
      | .app a => return .app t (← rename m p a)
      | .fst => pure (.fst t)
      | .snd => pure (.snd t)
      | .down => pure (.down t)
      | _ => pure t) t
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
  if ← unifyGlued l (← forceMeta t) (← forceMeta u) then return ()
  -- numerals: compare two directly, or else look one step inside (`vNatView`)
  let g ← getGlobals
  let (t, u) ← match ← force t, ← force u with
    | .natLit n, .natLit m => if n == m then return () else throwAt {} s!"{n} ≠ {m}"
    -- only against a constructor: a metavariable is solved with the numeral itself (as
    -- a constructor view it isn't a literal, and native arithmetic on it falls back to
    -- the unary definitions)
    | t@(.natLit _), u@(.con _) => pure (vNatView g t, u)
    | t@(.con _), u@(.natLit _) => pure (t, vNatView g u)
    | t, u => pure (t, u)
  -- an equation against something that isn't one: it may compute further
  let isEq (v : Val R) : Bool := v matches .neutral (.eq ..) _
  if isEq t != isEq u then
    if let some t' ← recomputeEq? t then return ← unify l t' u
    if let some u' ← recomputeEq? u then return ← unify l t u'
  sorry

/-- Glued values (given). Returns `true` if it solved the problem:

* the same global head on both sides: unify the spines (on failure, undo and let the
  caller unfold);
* an unsolved meta against a glued value: solve it with the value as it is, so the
  solution keeps the definition's name; outside the pattern fragment, try the
  **first-order approximation** `?m a₁ … aₖ =?= f b₁ … bₙ` ↦ `aᵢ =?= bₙ₋ₖ₊ᵢ` and
  `?m =?= f b₁ … bₙ₋ₖ` (for the trailing non-variable `aᵢ`; this is how `?M ?A` meets
  `TacticM Nat`). -/
partial def unifyGlued (l : Lvl) (t u : Val R) : ElabM R Bool := do
  let attempt (x : ElabM R Unit) : ElabM R Bool := do
    let s ← get
    try x; pure true catch _ => set s; pure false
  match t, u with
  | .lazyInd .., .lazyInd .. =>
    let g ← getGlobals
    pure (quote g l t == quote g l u)
  | .unfold n us sp v, .unfold n' us' sp' v' =>
    if n == n' && us.length == us'.length && sp.size == sp'.size then
      if ← attempt (do for a in us, b in us' do unifyLevel a b
                       unifySpine l sp sp') then return true
    -- lazy delta: unfold the later definition by one step, and compare again
    let g ← getGlobals
    let height (x : Name) : Nat := (g.order.idxOf? x).getD 0
    -- (recursors compute: unfold them first; otherwise the later definition, then the other)
    let isRec (x : Name) : Bool := x.endsWith ".rec" || x.endsWith ".casesOn" || x.endsWith ".scasesOn"
    let first := isRec n || (!isRec n' && height n ≥ height n')
    if first then
      if ← attempt (unify l v.get u) then return true
      attempt (unify l t v'.get)
    else
      if ← attempt (unify l t v'.get) then return true
      attempt (unify l v.get u)
  | .neutral (.mvar m) sp, v@(.unfold ..) | v@(.unfold ..), .neutral (.mvar m) sp =>
    if ← attempt (solve l m sp v) then return true
    unifyFirstOrder l m sp v
  -- a hole against a rigid neutral, outside the pattern fragment:
  -- * the same projection on both sides (`?e.op =?= e.op`): unify what is projected;
  -- * applications (`?M ?A =?= m A`): the first-order approximation.
  -- (Heuristics like Lean's, tried only when pattern unification fails.)
  | .neutral (.mvar m) sp, v@(.neutral h' sp') | v@(.neutral h' sp'), .neutral (.mvar m) sp =>
    if h' matches .mvar _ then return false
    if ← isPattern sp then return false
    match sp.back?, sp'.back? with
    | some .fst, some .fst | some .snd, some .snd =>
      attempt (unify l (.neutral (.mvar m) sp.pop) (.neutral h' sp'.pop))
    | _, _ =>
      if sp.all (· matches .app _) && sp'.all (· matches .app _) && !sp'.isEmpty then
        unifyFirstOrder l m sp v
      else pure false
  | _, _ => pure false
where
  isPattern (sp : Array (Elim R)) : ElabM R Bool := do
    for e in sp do
      match e with
      | .app a => unless (← forceMeta a) matches .neutral (.local _) #[] do return false
      | _ => return false
    pure true

/-- The first-order approximation (see `unifyGlued`). -/
partial def unifyFirstOrder (l : Lvl) (m : Nat) (sp : Array (Elim R)) (v : Val R) : ElabM R Bool := do
  -- the rigid side: a glued definition, or a variable (or other head) applied to arguments
  let (rebuild, sp') : (Array (Elim R) → ElabM R (Val R)) × Array (Elim R) ← match v with
    | .unfold n us sp' _ => pure ((fun pre => do
        let g ← getGlobals
        pure (pre.foldl (fun acc e => match e with
          | .app b => vApp g acc b
          | _ => acc) (eval g [] (.const n us)))), sp')
    | .neutral h sp' => pure ((fun pre => pure (.neutral h pre)), sp')
    | _ => return false
  let appArg : Elim R → Option (Val R)
    | .app a => some a
    | _ => none
  let some args := sp.mapM appArg | pure false
  let some args' := sp'.mapM appArg | pure false
  -- the arguments after the longest prefix of bound variables
  let mut k := 0
  for a in args do
    if (← forceMeta a) matches .neutral (.local _) #[] then k := k + 1 else break
  let j := args.size - k
  if j == 0 || j > args'.size then return false
  let s ← get
  try
    for a in args.extract k args.size, b in args'.extract (args'.size - j) args'.size do
      unify l a b
    let head ← rebuild (sp'.extract 0 (sp'.size - j))
    solve l m (sp.extract 0 k) head
    pure true
  catch _ =>
    set s
    pure false

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
  | .eq A a b, .eq A' a' b' =>
    unify l A A'
    let s ← get
    try unify l a a'; unify l b b'
    catch err =>
      -- an equation that was stuck on a metavariable (its type, say) may compute now:
      -- `succ ?a = succ ?b` at a solved `Nat` is `?a = ?b`. Compare the computed forms,
      -- if either changed.
      set s
      let g ← getGlobals
      let v := vEq g (← force A) a b
      let v' := vEq g (← force A') a' b'
      let same (w : Val R) (A a b : Val R) : Bool :=
        quote g l w == quote g l (.neutral (.eq A a b) #[])
      if same v A a b && same v' A' a' b' then throw err
      unify l v v'
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
    | .out, .out | .down, .down => pure ()
    | .scase u I D v P f s i, .scase u' I' D' v' P' f' s' i' =>
      unifyLevel u u'; unifyLevel v v'
      for (x, y) in [(I, I'), (D, D'), (P, P'), (f, f'), (s, s'), (i, i')] do unify l x y
    | .sfix u I D v P f s i, .sfix u' I' D' v' P' f' s' i' =>
      unifyLevel u u'; unifyLevel v v'
      for (x, y) in [(I, I'), (D, D'), (P, P'), (f, f'), (s, s'), (i, i')] do unify l x y
    | _, _ => throwAt {} "spine mismatch"

end

end Wiz
