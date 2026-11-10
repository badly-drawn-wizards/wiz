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
  --<sol
  match v with
  | .neutral (.mvar m) sp =>
    match (← lookupMeta m).solution with
    | some sol => forceMeta (vElims (← getGlobals) sol sp)
    | none => pure v
  | _ => pure v
  --|ex
  --| sorry
  --sol>

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
`ren` maps the levels of variables in the spine to their new levels; `downs` maps the
variables that occur in the spine lowered, as `down x` (see `invert`). -/
structure PRen where
  dom : Lvl
  cod : Lvl
  ren : Std.HashMap Lvl Lvl
  downs : Std.HashMap Lvl Lvl := {}

/-- Go under a binder on both sides. -/
def PRen.lift (p : PRen) : PRen :=
  { p with dom := p.dom + 1, cod := p.cod + 1, ren := p.ren.insert p.cod p.dom }

/-- **Exercise 3.2.** Invert a spine into a partial renaming. `gamma` is the size of the
current context. Every spine entry must be an application (`Elim.app v`) whose
argument forces to a bound variable with an empty spine (`.neutral (.local x) #[]`),
and a variable that occurs twice is left out of the renaming (the solution may not use
it). Otherwise throw (at `{}`), saying the problem is outside the pattern fragment.
The i-th spine variable maps to level i.

(Given) A lowered variable `down x` (`x : ULift A`) counts as a variable too: the
solution's i-th parameter `y` stands for `down x`, and `x` itself for `up y` (η for
`ULift`). Constructor fields with a lifted domain (`k : A → Proto` with `A : Type` in a
`Type 1` inductive) are stored as `fun h => k (down h)`, so unifying two such fields
meets `?k … (down h)`. -/
def invert (gamma : Lvl) (sp : Array (Elim R)) : ElabM R PRen := do
  --<sol
  let mut ren : Std.HashMap Lvl Lvl := {}
  let mut downs : Std.HashMap Lvl Lvl := {}
  let mut repeated : Array Lvl := #[]
  let mut dom := 0
  for e in sp do
    let .app v := e | throwAt {} "unification problem is outside the pattern fragment"
    match ← force v with
    | .neutral (.local x) #[] =>
      -- a repeated variable can't be used by the solution (which occurrence?)
      if ren.contains x || downs.contains x then repeated := repeated.push x
      ren := ren.insert x dom
      dom := dom + 1
    | .neutral (.local x) #[.down] =>
      if ren.contains x || downs.contains x then repeated := repeated.push x
      downs := downs.insert x dom
      dom := dom + 1
    | _ => throwAt {} "unification problem is outside the pattern fragment"
  pure { dom, cod := gamma, ren := repeated.foldl (·.erase ·) ren,
         downs := repeated.foldl (·.erase ·) downs }
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
        pure (.split (← rename m p q) acc z mo' x y b')
      | .absurd mo => return .absurd (← rename m p mo) acc
      | .ecase z mo env bs => do
        let mo' ← rename m p.lift (← instM mo (Val.var p.cod))
        let g ← getGlobals
        let bs' ← bs.mapM fun b => rename m p (eval g env b)
        pure (.ecase z mo' acc bs')
      | .delim v P a b c h =>
        return .delim v (← rename m p P) (← rename m p a) (← rename m p b) (← rename m p c) (← rename m p h) acc
      | .ind l I D v P mt i =>
        return .ind l (← rename m p I) (← rename m p D) v (← rename m p P) (← rename m p mt) (← rename m p i) acc
      | .out => pure (.out acc)
      | .down => pure (.down acc)
      | .scase l I D v P mt s i =>
        return .scase l (← rename m p I) (← rename m p D) v (← rename m p P) (← rename m p mt) (← rename m p s) (← rename m p i) acc
      | .sfix l I D v P f s i =>
        return .sfix l (← rename m p I) (← rename m p D) v (← rename m p P) (← rename m p f) (← rename m p s) (← rename m p i) acc
  match ← force v with
  | .neutral (.local x) sp =>
    match p.ren[x]? with
    | some x' => goSp (.var (p.dom - x' - 1)) sp
    | none => match p.downs[x]? with
      -- (given) `down x` is the parameter `y`; a bare `x` is `up y`
      | some x' =>
        let y : Term R := .var (p.dom - x' - 1)
        if sp[0]? matches some Elim.down then goSp y (sp.extract 1 sp.size) else goSp (.up y) sp
      | none => throwAt {} "a variable escapes the scope of the hole being solved"
  | .neutral (.global n us) sp => goSp (.const n us) sp
  | .neutral (.eq A a b) sp => do goSp (.eq (← rename m p A) (← rename m p a) (← rename m p b)) sp
  | .neutral (.eqTy A B) sp => do goSp (.eqTy (← rename m p A) (← rename m p B)) sp
  | .neutral (.cast A B e t) sp => do
    goSp (.cast (← rename m p A) (← rename m p B) (← rename m p e) (← rename m p t)) sp
  | .neutral (.refl A a) sp => do goSp (.refl (← rename m p A) (← rename m p a)) sp
  | .neutral (.reflTy X) sp => do goSp (.reflTy (← rename m p X)) sp
  | .neutral (.transp A a P q b e) sp => do
    goSp (.transp (← rename m p A) (← rename m p a) (← rename m p P) (← rename m p q)
      (← rename m p b) (← rename m p e)) sp
  | .neutral (.mvar m') sp =>
    if m == m' then throwAt {} s!"occurs check: ?m{m} would have to contain itself"
    else goSp (.mvar m') sp
  | .sort l => pure (.sort l)
  | .pi x bi q a b s =>
    return .pi x bi (← rename m p q) (← rename m p a) (← rename m p.lift (← instM b (Val.var p.cod))) s
  | .lam x b => return .lam x (← rename m p.lift (← instM b (Val.var p.cod)))
  | .sigma x q a b s =>
    return .sigma x (← rename m p q) (← rename m p a) (← rename m p.lift (← instM b (Val.var p.cod))) s
  | .pair a b => return .pair (← rename m p a) (← rename m p b)
  | .unit l => pure (.unit l)
  | .tt => pure .tt
  | .empty l => pure (.empty l)
  | .qty => pure .qty
  | .qlit r => pure (.qlit r)
  | .size => pure .size
  | .sizeLt s => return .sizeLt (← rename m p s)
  | .szInf => pure .szInf
  | .szSuc s => return .szSuc (← rename m p s)
  | .cocon x => return .cocon (← rename m p x)
  | .scofix l I D A f s i a =>
    return .scofix l (← rename m p I) (← rename m p D) (← rename m p A) (← rename m p f) (← rename m p s) (← rename m p i) (← rename m p a)
  | .enum ls => pure (.enum ls)
  | .tag ls i => pure (.tag ls i)
  | .desc l I => return .desc l (← rename m p I)
  | .dret i => return .dret (← rename m p i)
  | .darg q S D => return .darg (← rename m p q) (← rename m p S) (← rename m p D)
  | .drec q j D => return .drec (← rename m p q) (← rename m p j) (← rename m p D)
  | .dhrec q H j D => return .dhrec (← rename m p q) (← rename m p H) (← rename m p j) (← rename m p D)
  | .mu l I D i s h => return .mu l (← rename m p I) (← rename m p D) (← rename m p i) (← rename m p s) (← renameHint h)
  | .nu l I D i s h => return .nu l (← rename m p I) (← rename m p D) (← rename m p i) (← rename m p s) (← renameHint h)
  | .con x => return .con (← rename m p x)
  | .ulift l A => return .ulift l (← rename m p A)
  | .up a => return .up (← rename m p a)
  | .natLit n => return .natLit n
  | .unfold n us sp _ => goSp (.const n us) sp
  | .lazyInd _ _ _ _ _ _ _ _ _ v => rename m p v.get
  | .coit l I D S st i s =>
    return .coit l (← rename m p I) (← rename m p D) (← rename m p S) (← rename m p st) (← rename m p i) (← rename m p s)
where
  renameHint : Option (Name × List Level × List (Val R)) → ElabM R (Option (Name × List Level × List (Term R)))
    | some (n, us, as) => return some (n, us, ← as.mapM (rename m p))
    | none => pure none
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
  --<sol
  match ← force t, ← force u with
  | .sort a, .sort b => unifyLevel a b
  | .pi _ bi q a b _, .pi _ bi' q' a' b' _ =>
    unless bi == bi' do throwAt {} "implicit vs explicit binder mismatch"
    unify l q q'
    unify l a a'
    unify (l + 1) (← instM b (Val.var l)) (← instM b' (Val.var l))
  | .sigma _ q a b _, .sigma _ q' a' b' _ =>
    unify l q q'
    unify l a a'
    unify (l + 1) (← instM b (Val.var l)) (← instM b' (Val.var l))
  | .pair a b, .pair a' b' => unify l a a'; unify l b b'
  | .pair a b, t'@(.neutral ..) => unify l a (vFst t'); unify l b (vSnd t')
  | t'@(.neutral ..), .pair a b => unify l (vFst t') a; unify l (vSnd t') b
  | .unit u, .unit u' | .empty u, .empty u' => unifyLevel u u'
  | .tt, .tt | .qty, .qty | .size, .size | .szInf, .szInf => pure ()
  | .szSuc a, .szSuc b | .cocon a, .cocon b | .sizeLt a, .sizeLt b => unify l a b
  | .scofix u I D A f s i a, .scofix u' I' D' A' f' s' i' a' =>
    unifyLevel u u'
    for (x, y) in [(I, I'), (D, D'), (A, A'), (f, f'), (s, s'), (i, i'), (a, a')] do unify l x y
  | .qlit a, .qlit b => unless a == b do throwAt {} "quantity mismatch"
  | .enum ls, .enum ls' => unless ls.length == ls'.length do throwAt {} "enumeration size mismatch"
  | .tag _ i, .tag _ j => unless i == j do throwAt {} "tag mismatch"
  | .desc u I, .desc u' I' => unifyLevel u u'; unify l I I'
  | .dret i, .dret j => unify l i j
  | .darg q S D, .darg q' S' D' | .drec q S D, .drec q' S' D' => unify l q q'; unify l S S'; unify l D D'
  | .dhrec q H j D, .dhrec q' H' j' D' => unify l q q'; unify l H H'; unify l j j'; unify l D D'
  | .mu u I D i s _, .mu u' I' D' i' s' _ | .nu u I D i s _, .nu u' I' D' i' s' _ =>
    unifyLevel u u'; unify l I I'; unify l D D'; unify l i i'; unify l s s'
  | .con x, .con y => unify l x y
  | .ulift u A, .ulift u' A' => unifyLevel u u'; unify l A A'
  | .up a, .up b => unify l a b
  | .up a, t'@(.neutral ..) => unify l a (vDown t')
  | t'@(.neutral ..), .up a => unify l (vDown t') a
  | .coit u I D S st i s, .coit u' I' D' S' st' i' s' =>
    unifyLevel u u'
    for (a, b) in [(I, I'), (D, D'), (S, S'), (st, st'), (i, i'), (s, s')] do unify l a b
  | .lam _ b, .lam _ b' => unify (l + 1) (← instM b (Val.var l)) (← instM b' (Val.var l))
  | .lam _ b, t' => unify (l + 1) (← instM b (Val.var l)) (← vAppM t' (Val.var l))
  | t', .lam _ b => unify (l + 1) (← vAppM t' (Val.var l)) (← instM b (Val.var l))
  | .neutral (.mvar m) sp, .neutral (.mvar m') sp' =>
    if m == m' then unifySpine l sp sp' else solve l m sp (.neutral (.mvar m') sp')
  | .neutral (.mvar m) sp, t' => solve l m sp t'
  | t', .neutral (.mvar m) sp => solve l m sp t'
  | .neutral h sp, .neutral h' sp' => unifyHead l h h'; unifySpine l sp sp'
  | _, _ => throwAt {} "rigid mismatch"
  --|ex
  --| sorry
  --sol>

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
      | .app a => match ← forceMeta a with
        | .neutral (.local _) #[] | .neutral (.local _) #[.down] => pure ()
        | _ => return false
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
  -- a rigid argument on the hole's side against an unsolved hole on the other is a guess,
  -- and an untyped one: `?P 3 =?= Ex ?A ?Q` would solve `?Q := 3` (and `?P := Ex ?A`),
  -- ill-typed, and applying `?Q` later panics. Leave such problems to the caller.
  let flex (v : Val R) : ElabM R Bool := return (← forceMeta v) matches .neutral (.mvar _) _
  for a in args.extract k args.size, b in args'.extract (args'.size - j) args'.size do
    if (← flex b) && !(← flex a) then return false
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
