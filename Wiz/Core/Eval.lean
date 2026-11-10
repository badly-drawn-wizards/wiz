import Wiz.Core.Value
import Wiz.Core.Templates

/-!
# Evaluation, quotation, normalisation

Normalisation by evaluation (NbE) in two halves:

* `eval : Env → Term → Val` interprets syntax into the semantic domain. β-reduction
  happens for free, because applying a `Val.lam` just evaluates its closure body.
* `quote : Lvl → Val → Term` reads a value back into β-normal syntax, going under
  binders by applying closures to fresh variables `Val.var l`.

`nf = quote ∘ eval`.

Every eliminator has a semantic version (`vApp`, `vFst`, `vSnd`, `vSplit`,
`vAbsurd`). Each computes when its argument is a constructor (a β-rule) and otherwise
pushes itself onto the neutral's spine.

Globals are **glued** (stage 7a): `const n` evaluates to `Val.unfold`, which keeps the
name and computes the unfolding only when `whnf` needs it. Definitions marked `inline`
(constructors), or all of them when `Globals.eager` is set (as `nf` does), are
δ-unfolded at once. Axioms (no
definition) become neutrals.

These are `partial` because the untyped evaluator need not terminate (`Ω = (λx. x x)(λx. x x)`).
On well-typed terms they do.
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

/-- Are two quantity values equal? `none` if either is not a polynomial (unknown). -/
def sameQty (a b : Val R) : Option Bool := do
  return QPoly.equiv (← a.toPoly?) (← b.toPoly?)

/-- Unfold glued values (`Val.unfold`) until the head is not a definition: do this before
matching on a value's shape. -/
partial def whnf : Val R → Val R
  | .unfold _ _ _ v => whnf v.get
  | .lazyInd _ _ _ _ _ _ _ _ _ v => whnf v.get
  | v => v

/-- **Exercise 4.4b.** First projection. -/
partial def vFst : Val R → Val R
  | .unfold _ _ _ v => vFst v.get  -- (given) unfold glued values
  | .lazyInd l I D w P m i x sp v => .lazyInd l I D w P m i x (sp.push .fst) (Thunk.mk fun _ => vFst v.get)  -- (given)
  | v => sorry

/-- **Exercise 4.4c.** Second projection. -/
partial def vSnd : Val R → Val R
  | .unfold _ _ _ v => vSnd v.get  -- (given)
  | .lazyInd l I D w P m i x sp v => .lazyInd l I D w P m i x (sp.push .snd) (Thunk.mk fun _ => vSnd v.get)  -- (given)
  | v => sorry

/-- The arity of a registered operation on numbers. -/
def natOpArity : Name → Nat
  | "nat.zero" => 0
  | "nat.succ" | "nat.pred" | "nat.log2" => 1
  | _ => 2

/-- The registered operations on numbers that return a number, computed natively. The
kernel, the interpreters and the native runtime (`runtime/wiz.c`) agree with these, and
with the Prelude's definitions (`Nat.div`, …): `n / 0 = 0`, `n % 0 = n`, `log2 0 = 0`. -/
def natNative? : Name → Array Nat → Option Nat
  | "nat.succ", #[a] => some (a + 1)
  | "nat.pred", #[a] => some (a - 1)
  | "nat.add", #[a, b] => some (a + b)
  | "nat.sub", #[a, b] => some (a - b)
  | "nat.mul", #[a, b] => some (a * b)
  | "nat.div", #[a, b] => some (a / b)
  | "nat.mod", #[a, b] => some (a % b)
  | "nat.pow", #[a, b] => some (a ^ b)
  | "nat.land", #[a, b] => some (a &&& b)
  | "nat.lor", #[a, b] => some (a ||| b)
  | "nat.xor", #[a, b] => some (a ^^^ b)
  | "nat.shiftLeft", #[a, b] => some (a <<< b)
  | "nat.shiftRight", #[a, b] => some (a >>> b)
  | "nat.log2", #[a] => some a.log2
  | _, _ => none

/-- The value of a global registered as an operation on numbers (`builtin nat.add := …`):
`nat.zero` is the literal `0`, and an operation is a closure whose body is a
`Term.natOp` on its arguments, so it computes natively when they are literals. -/
def vBuiltin? (g : Globals R) (n : Name) : Option (Val R) := do
  let k ← g.builtinKey? n
  if !k.startsWith "nat." then none
  else if k == "nat.zero" then some (.natLit 0)
  else if natOpArity k == 1 then some (.lam "a" (.mk [] (.natOp k #[.var 0])))
  else some (.lam "a" (.mk [] (.lam "b" (.natOp k #[.var 1, .var 0]))))

/-- `absurd` is always stuck: the empty type has no constructors. -/
def vAbsurd (m : Val R) : Val R → Val R
  | .neutral h sp => .neutral h (sp.push (.absurd m))
  | _ => panic! "vAbsurd: ill-typed"

/-- `(a → b) × (b → a)`: equality of propositions (propositional extensionality) -/
def vIff (a b : Val R) : Val R :=
  .sigma "_" (.qlit 0) (.pi "_" .default (.qlit 0) a (.mk [b] (.var 1)) (some 0))
    (.mk [a, b] (.pi "_" .default (.qlit 0) (.var 2) (.var 2) (some 0))) (some 0)

/-- Is this type (in weak head normal form) a proposition? `none` when its sort can't be
seen: a neutral, or a `Π`/`Σ` without a sort or with one that depends on a universe
parameter. Type equality needs to know: two propositions are equal when equivalent,
whatever their shapes (`True = (True → True)`), and comparing them by shape instead
proved `False` (a proposition can be the domain of a function type in `Type`). -/
def propSort? : Val R → Option Bool
  | .pi _ _ _ _ _ (some s) | .sigma _ _ _ _ (some s) | .unit s | .empty s =>
    if s.equiv 0 then some true else if s.isNeverZero then some false else none
  | .sort _ | .qty | .enum _ | .desc .. | .mu .. | .nu .. | .size | .sizeLt _ => some false
  | .neutral (.eq ..) #[] | .neutral (.eqTy ..) #[] => some true
  | _ => none

/-! ### A level above every variable of a value

Regularity (`vCast`'s last case) compares two types by quoting them. Quoting at level
`l` turns the variable at level `x` into the index `l - x - 1`, so `l` must be above
every variable the values mention, or two different variables could quote to the same
index. `Val.lvlBound` computes such an `l`. A closure counts only the entries of its
environment that its body might mention (that is all `quote` can reach). The bound may
be too large (a `lazyInd`'s whole spine counts), never too small. -/

/-- The free variables of `t` under `depth` binders, as indices into the enclosing
environment (with repeats). -/
partial def Term.freeVarsAt (depth : Nat) (t : Term R) : StateM (Array Nat) Unit :=
  match t with
  | .var i => if i ≥ depth then modify (·.push (i - depth)) else pure ()
  | t => t.forChildren (fun _ => pure ()) (fun d c => Term.freeVarsAt (depth + d) c)

mutual
/-- `1 +` the largest level of a local variable in `v` (`0` if none). -/
partial def Val.lvlBound : Val R → Nat
  | .neutral h sp => max h.lvlBound (Elim.spineBound sp)
  | .unfold _ _ sp _ => Elim.spineBound sp
  | .lazyInd _ I D _ P m i x sp _ => max (Val.maxBound [I, D, P, m, i, x]) (Elim.spineBound sp)
  | .pi _ _ q a b _ | .sigma _ q a b _ => max (max q.lvlBound a.lvlBound) (b.lvlBound 1)
  | .lam _ b => b.lvlBound 1
  | .pair a b => max a.lvlBound b.lvlBound
  | .desc _ a | .dret a | .szSuc a | .sizeLt a | .con a | .cocon a => a.lvlBound
  | .darg q S D => Val.maxBound [q, S, D]
  | .drec q j D => Val.maxBound [q, j, D]
  | .dhrec q H j D => Val.maxBound [q, H, j, D]
  | .mu _ I D i s h | .nu _ I D i s h => max (Val.maxBound [I, D, i, s]) (Val.maxBound ((h.map (·.2.2)).getD []))
  | .scofix _ I D A f s i a => Val.maxBound [I, D, A, f, s, i, a]
  | .coit _ I D S st i s => Val.maxBound [I, D, S, st, i, s]
  | .sort _ | .unit _ | .tt | .empty _ | .qty | .qlit _ | .enum _ | .tag .. | .size | .szInf
  | .natLit _ => 0
partial def Val.maxBound (vs : List (Val R)) : Nat := vs.foldl (fun m v => max m v.lvlBound) 0
partial def Head.lvlBound : Head R → Nat
  | .local x => x + 1
  | .global .. | .mvar _ => 0
  | .eq A a b => Val.maxBound [A, a, b]
  | .eqTy A B => Val.maxBound [A, B]
  | .cast A B e t => Val.maxBound [A, B, e, t]
  | .refl A a => Val.maxBound [A, a]
  | .reflTy X => X.lvlBound
  | .transp A a P p b e => Val.maxBound [A, a, P, p, b, e]
partial def Elim.spineBound (sp : Array (Elim R)) : Nat := sp.foldl (fun m e => max m e.lvlBound) 0
partial def Elim.lvlBound : Elim R → Nat
  | .app a => a.lvlBound
  | .fst | .snd | .out => 0
  | .split q _ m _ _ b => max q.lvlBound (max (m.lvlBound 1) (b.lvlBound 2))
  | .absurd m => m.lvlBound
  | .ecase _ m env bs => max (m.lvlBound 1) (envBound env (bs.foldl (fun acc b => ((Term.freeVarsAt 0 b).run acc).2) #[]))
  | .delim _ P a b c h => Val.maxBound [P, a, b, c, h]
  | .ind _ I D _ P m i => Val.maxBound [I, D, P, m, i]
  | .sfix _ I D _ P f s i => Val.maxBound [I, D, P, f, s, i]
  | .scase _ I D _ P m s i => Val.maxBound [I, D, P, m, s, i]
/-- The bound of the entries of `env` at the indices `fv`. -/
partial def envBound (env : Env R) (fv : Array Nat) : Nat :=
  (fv.qsort (· < ·)).foldl (init := (0, none)) (fun (m, prev) i =>
    if prev == some i then (m, prev)
    else (max m ((env[i]?.map Val.lvlBound).getD 0), some i)) |>.1
/-- A closure whose body is under `binders` binders. -/
partial def Closure.lvlBound (binders : Nat) : Closure R → Nat
  | .mk env body => envBound env ((Term.freeVarsAt binders body).run #[]).2
end

/-- (D1 experiment, `Regularity.refl`) Is this proof visibly a reflexivity: `refl`,
`reflTy`, `()`, or a `transp` of one along one? Such proofs only prove equations whose
sides are definitionally equal. -/
partial def reflProof (e : Val R) : Bool :=
  match whnf e with
  | .neutral (.refl ..) #[] | .neutral (.reflTy _) #[] | .tt => true
  | .neutral (.transp _ _ _ p _ e) #[] => reflProof p && reflProof e
  | _ => false

/-- (D1 experiment) May `cast A A e t` reduce to `t` under `g.regularity`? -/
def regularityAllowed (g : Globals R) (A e : Val R) : Bool :=
  match g.regularity with
  | .full => true
  | .nonProp => propSort? A != some true
  | .refl => reflProof e
  | .off => false

/-- The predecessor of a size, for `con`/`cocon`/`out`: `↑s ↦ s`, `∞ ↦ ∞`; `none`
for a size variable, which can't be built from or observed. -/
partial def sizePred? : Val R → Option (Val R)
  | .unfold _ _ _ v => sizePred? v.get
  | .lazyInd _ _ _ _ _ _ _ _ _ v => sizePred? v.get
  | .szInf => some .szInf
  | .szSuc s => some s
  | _ => none

mutual

/-- **Exercise 1.1.** Evaluate a term in an environment.

* `var ix`: look it up in `env` (index 0 is the head).
* `const n us`: if there is a definition, a **glued** value `unfold n us #[] t`, where
  the thunk `t` evaluates the definition in the *empty* environment, after
  instantiating its level parameters with `us` (`Term.instLevels`). Declarations
  marked `inline` (constructors), or all of them if `g.eager`, are evaluated right
  away instead. Without a definition it is a stuck `neutral (.global n us) #[]`.
* `pi`/`lam`: don't evaluate the body; capture it with `env` in a `Closure`.
* `app`: evaluate both sides and use `vApp`.
* `letE`: evaluate the value and push it onto the environment for the body.
* `ann`: annotations have no computational content.
* `mvar`: (given) metavariables are stuck neutrals.

**Exercise 4.10** (stage 4c): `eq` uses `vEq`, `eqTy` uses `vEqType`, `cast` uses
`vCast`, and the proofs `refl`, `reflTy` and `transp` are stuck heads (proofs never
compute).

**Exercise 4.3** (stage 4b): the structural types. Constructors evaluate their parts,
`sigma` captures its second component in a closure, and eliminators use `vFst`,
`vSnd`, `vSplit` and `vAbsurd`. -/
partial def eval (g : Globals R) (env : Env R) : Term R → Val R
  | .var ix => sorry
  -- (given) numerals; `vBuiltin?` registered operations
  | .natLit n => .natLit n
  | .natOp op args => vNatOp g op (args.map (eval g env))
  | .const n us => if let some v := vBuiltin? g n then v else sorry
  | .sort l => sorry
  | .pi x bi q dom cod s => sorry
  | .lam x body => sorry
  | .app f a => sorry
  | .letE _ _ _ val body => sorry
  | .ann tm _ => sorry
  | .mvar m => .neutral (.mvar m) #[]
  -- Exercise 4.3
  | .sigma x q a b s => sorry
  | .pair a b => sorry
  | .fst t => sorry
  | .snd t => sorry
  | .split q s z m x y b => sorry
  | .unit l => sorry
  | .tt => sorry
  | .empty l => sorry
  | .absurd m t => sorry
  -- Exercise 4.10
  | .eq A a b => sorry
  | .eqTy A B => sorry
  | .cast A B e t => sorry
  | .refl A a => sorry
  | .reflTy X => sorry
  | .transp A a P p b e => sorry
  | .qty => .qty
  | .qlit r => .qlit r
  -- Exercise 4.18: constructors evaluate their parts; eliminators use
  -- vEcase, vDelim, vInd and vOut.
  | .enum ls => sorry
  | .tag ls i => sorry
  | .ecase z m s bs => sorry
  | .desc l I => sorry
  | .dret i => sorry
  | .darg q S D => sorry
  | .drec q j D => sorry
  | .dhrec q H j D => sorry
  | .delim v P a b c h D => sorry
  | .mu l I D i s h => sorry
  | .con x => sorry
  | .ind l I D v P m i x => sorry
  | .nu l I D i s h => sorry
  | .out x => sorry
  | .coit l I D S st i s => sorry
  | .size => .size
  | .szInf => .szInf
  | .szSuc s => match eval g env s with
    | .szInf => .szInf
    | v => .szSuc v
  | .sizeLt s => .sizeLt (eval g env s)
  -- Exercise 4.22: the sized primitives (vSfix, and cocon/scofix are values)
  | .sfix l I D v P f s i x => sorry
  | .cocon x => sorry
  | .scase l I D v P m s i x => sorry
  | .scofix l I D A f s i a => sorry

/-- Evaluate a display hint's arguments. -/
partial def evalHint (g : Globals R) (env : Env R) :
    Option (Name × List Level × List (Term R)) → Option (Name × List Level × List (Val R))
  | some (n, us, as) => some (n, us, as.map (eval g env))
  | none => none

/-- **Exercise 1.2a.** Semantic application.
A `lam` β-reduces; a neutral grows its spine (with `Elim.app`). Anything else is a
type error that the checker should have ruled out (use `panic!`). -/
partial def vApp (g : Globals R) : Val R → Val R → Val R
  -- (given) a glued application grows its spine, and its unfolding lazily
  | .unfold n us sp v, a => .unfold n us (sp.push (.app a)) (Thunk.mk fun _ => vApp g v.get a)
  | .lazyInd l I D w P m i x sp v, a => .lazyInd l I D w P m i x (sp.push (.app a)) (Thunk.mk fun _ => vApp g v.get a)
  | f, a => sorry

/-- **Exercise 1.2b.** Instantiate a closure with a value for its bound variable. -/
partial def Closure.inst (g : Globals R) : Closure R → Val R → Val R
  | .mk env body, a => sorry

/-- Instantiate a closure over two binders (`a` first, then `b`). -/
partial def Closure.inst2 (g : Globals R) : Closure R → Val R → Val R → Val R
  | .mk env body, a, b => eval g (b :: a :: env) body

/-- **Exercise 4.4a.** `let (x, y) := s; body`: β-reduces on a `pair`, gets stuck on a
neutral. -/
partial def vSplit (g : Globals R) (q : Val R) (s : Val R) (z : Name) (m : Closure R) (x y : Name)
    (body : Closure R) : Val R :=
  let s := whnf s
  sorry

/- ### Data (stage 4d)

`vEcase`, `vDelim`, `vInd` and `vOut` compute on canonical arguments and are stuck on
neutrals. `vInd` and `vOut` use the description templates of `Wiz.Core.Templates`. -/

/-- `λ j. μ^s D j` and `λ j. ν^s D j` at a given size. -/
partial def muFamilyAt (l : Level) (I D s : Val R) : Val R :=
  .lam "j" (.mk [s, D, I] (.mu l (.var 3) (.var 2) (.var 0) (.var 1) none))

partial def nuFamilyAt (l : Level) (I D s : Val R) : Val R :=
  .lam "j" (.mk [s, D, I] (.nu l (.var 3) (.var 2) (.var 0) (.var 1) none))

/-- `λ j. μ D j`, the family being defined, as a value. -/
partial def muFamily (l : Level) (I D : Val R) : Val R :=
  .lam "j" (.mk [D, I] (.mu l (.var 2) (.var 1) (.var 0) .szInf none))

partial def nuFamily (l : Level) (I D : Val R) : Val R :=
  .lam "j" (.mk [D, I] (.nu l (.var 2) (.var 1) (.var 0) .szInf none))

/-- `⟦D⟧ X i` -/
partial def vInterp (g : Globals R) (l : Level) (I D X i : Val R) : Val R :=
  [I, D, X, i].foldl (vApp g) (eval g [] (Templates.interpTm l))

/-- `All D X P i xs` -/
partial def vAll (g : Globals R) (l v : Level) (I D X P i xs : Val R) : Val R :=
  [I, D, X, P, i, xs].foldl (vApp g) (eval g [] (Templates.allTm l v))

/-- **Exercise 4.19a.** `ecase` on a tag picks the branch (evaluated in `env`). -/
partial def vEcase (g : Globals R) (z : Name) (m : Closure R) (s : Val R) (env : Env R)
    (bs : List (Term R)) : Val R :=
  let s := whnf s
  sorry

/-- **Exercise 4.19b.** The description eliminator:

    delim (ret i)     ↦ mret i
    delim (arg q S D) ↦ marg q S D (fun s => delim (D s))
    delim (rec q j D) ↦ mrec q j D (delim D)
    delim (hrec q H j D) ↦ mhrec q H j D (delim D)

The `fun s => …` is a closure over a small template, as in `vEq`. -/
partial def vDelim (g : Globals R) (v : Level) (P mret marg mrec mhrec D : Val R) : Val R :=
  let D := whnf D
  sorry

/-- A numeral as a constructor, one step deep: `0 ↦ zero`, `n+1 ↦ succ (natLit n)`, using
the constructors' definitions (not their `vBuiltin?` values). Other values are
unchanged. -/
partial def vNatView (g : Globals R) : Val R → Val R
  | .natLit n =>
    let ctor (k : Name) : Val R := match (g.builtins.lookup k).bind g.find? with
      | some { value := some v, .. } => eval g [] v
      | _ => panic! s!"numerals need `builtin {k}`"
    if n == 0 then ctor "nat.zero" else vApp g (ctor "nat.succ") (.natLit (n - 1))
  | v => v

/-- A registered operation applied to all its arguments: native arithmetic on literals,
otherwise the operation's definition. -/
partial def vNatOp (g : Globals R) (op : Name) (args : Array (Val R)) : Val R :=
  -- the arguments as numerals, stopping at the first that isn't one: forcing the rest
  -- could run a numeral's recursion all the way down (`d * 2^64` is `d + d * (2^64 - 1)`,
  -- whose second argument is the next step, and so on)
  let lits : Option (Array Nat) := args.foldlM (init := #[]) fun acc a => match whnf a with
    | .natLit n => some (acc.push n)
    | _ => none
  let d : Val R := match (g.builtins.lookup op).bind g.find? with
    | some { value := some v, .. } => eval g [] v
    | _ => panic! s!"no definition for builtin {op}"
  match lits with
  | some ns => match natNative? op ns, op, ns with
    | some n, _, _ => .natLit n
    -- comparisons return a `Bool`: the definition's own result on small numerals
    | none, "nat.beq", #[a, b] =>
      whnf (vApp g (vApp g d (.natLit 0)) (.natLit (if a == b then 0 else 1)))
    | none, "nat.blt", #[a, b] =>
      whnf (vApp g (vApp g d (.natLit 0)) (.natLit (if a < b then 1 else 0)))
    | none, _, _ => args.foldl (vApp g) d
  | none => args.foldl (vApp g) d

/-- **Exercise 4.19c.** Induction computes on constructors:

    ind P m i (con xs) ↦ m i xs (hyps D (μ D) P (fun j y => ind P m j y) i xs)

(`Templates.hypsTm`; the `fun j y => …` is a template closure). -/
partial def vIndStep (g : Globals R) (l : Level) (I D : Val R) (v : Level) (P m i x : Val R) : Val R :=
  let x := vNatView g (whnf x)
  sorry

/-- `ind` on a numeral `n + 1` is computed only when needed (`Val.lazyInd`): its
hypothesis is `ind` on `n`, so computing eagerly would go all the way down to `0`. -/
partial def vInd (g : Globals R) (l : Level) (I D : Val R) (v : Level) (P m i x : Val R) : Val R :=
  match whnf x with
  | .natLit (_ + 1) => .lazyInd l I D v P m i x #[] (Thunk.mk fun _ => vIndStep g l I D v P m i x)
  | _ => vIndStep g l I D v P m i x

/-- **Exercise 4.22a.** Sized recursion unfolds on a constructor, with the recursive
calls at size `∞` (sizes are irrelevant at runtime):

    sfix P f s i (con xs) ↦ f ∞ (fun j i y => sfix P f j i y) i (con xs) -/
partial def vSfix (g : Globals R) (l : Level) (I D : Val R) (v : Level) (P f s i x : Val R) : Val R :=
  let x := vNatView g (whnf x)
  sorry

/-- **Exercise 4.22b.** Sized case analysis: `scase P m s i (con xs) ↦ m ∞ i xs` (the
size of the fields is irrelevant at runtime). -/
partial def vScase (g : Globals R) (l : Level) (I D : Val R) (v : Level) (P m s i x : Val R) : Val R :=
  let x := vNatView g (whnf x)
  sorry

/-- **Exercise 4.19d.** Observing an unfolding runs one step and re-wraps the
recursive positions:

    out (coit S step i s) ↦ map D S (ν D) (fun j s => coit S step j s) i (step i s) -/
partial def vOut (g : Globals R) (x : Val R) : Val R :=
  let x := whnf x
  sorry

/- ### Observational equality (stage 4c)

`a = b` at type `A` is not an inductive type. It **computes** by `A`:

    (f = g : (x : A) → B)    ↦  (x :0 A) → f x = g x                    funext
    (p = q : (x : A) × B)    ↦  (e :0 p.1 = q.1) × cast (B p.1) (B q.1) _ p.2 = q.2
    (u = v : Unit), Empty    ↦  True
    (P = Q : Prop)           ↦  (P → Q) × (Q → P)                       propext
    (X = Y : Type u)         ↦  vEqType X Y
    otherwise (A neutral)    ↦  stuck: neutral (Head.eq A a b)

Some results need new binders (`(x :0 A) → …`). Values can't contain Lean functions,
so these are **closures over small term templates**: the closure's environment holds
the values involved, and the template refers to them by de Bruijn index. Index 0 is
the new binder, and index `i + 1` is the environment's `i`-th entry.

All generated binders have quantity 0, since they are inside propositions.

Reference: Pujet & Tabareau, *Observational Equality: Now for Good* (POPL 2022). -/

/-- **Exercise 4.11a.** Observational equality at type `A`. See the table above.
`p = q` at a Σ type needs a proof that `B p.1 = B q.1`; build it with
`transp A₁ p.1 (fun y _ => B p.1 = B y) (reflTy (B p.1)) q.1 e`. For `Prop`, use
`Level.equiv l 0`; for `Type u` (`Level.isNeverZero`) it's `vEqType`. Otherwise
it's stuck. -/
partial def vEq (g : Globals R) (A a b : Val R) : Val R :=
  -- numerals: decide directly, or else look one step inside (`vNatView`)
  if let (.natLit n, .natLit m) := (whnf a, whnf b) then (if n == m then .unit 0 else .empty 0) else
  let A := whnf A
  let a := vNatView g (whnf a)
  let b := vNatView g (whnf b)
  sorry

/-- Equality of two payloads `x y : ⟦D⟧ X i`, by the description: constructor by
constructor, so that `succ m = succ n` is `m = n` (and not, through the Σ rule, an
equation with a cast along the tags' equation, which without regularity would be stuck):

    ret j          ↦ True                       (the index proofs are irrelevant)
    arg q (Enum) E ↦ by the tags: equal ↦ True × (the rest at `E tag`); different ↦ the
                     Σ rule (a pair whose first component is False); not both tags ↦
                     none (the whole equation is stuck)
    arg q S E      ↦ `x = y` at the Σ type `⟦arg q S E⟧ X i` (the Σ rule)
    rec q j E      ↦ (x.1 = y.1 : X j) × (the rest at E)
    hrec q H j E   ↦ (x.1 = y.1 : (h : H) → X (j h)) × (the rest at E)

The choice between rules depends only on `D` and on whether tags are canonical (computed or
stuck), so it is stable under substitution. -/
partial def vEqPayload (g : Globals R) (l : Level) (I X i D x y : Val R) : Option (Val R) :=
  let pairTy (A B : Val R) : Val R := .sigma "_" (.qlit 0) A (.mk [B] (.var 1)) (some 0)
  match whnf D with
  | .dret _ => some (.unit 0)
  | .darg q S E => match whnf S with
    | .enum _ => match whnf (vFst x), whnf (vFst y) with
      | .tag ls a, .tag _ b =>
        if a == b then (pairTy (.unit 0) ·) <$> vEqPayload g l I X i (vApp g E (.tag ls a)) (vSnd x) (vSnd y)
        -- different tags: the Σ rule, whose first component is `False`
        else some (vEq g (vInterp g l I (.darg q S E) X i) x y)
      | _, _ => none
    | _ => some (vEq g (vInterp g l I (.darg q S E) X i) x y)
  | .drec _ j E => do
    let r ← vEqPayload g l I X i E (vSnd x) (vSnd y)
    pure (pairTy (vEq g (vApp g X j) (vFst x) (vFst y)) r)
  | .dhrec q H j E => do
    let r ← vEqPayload g l I X i E (vSnd x) (vSnd y)
    -- h0 j1 X2
    let F : Val R := .pi "h" .default q H (.mk [j, X] (.app (.var 2) (.app (.var 1) (.var 0)))) none
    pure (pairTy (vEq g F (vFst x) (vFst y)) r)
  | _ => none

/-- **Exercise 4.11b.** Equality of types:

    ((x :q A) → B) = ((x :q A') → B')  ↦  (e :0 A' = A) × ((x :0 A') → B (cast A' A e x) = B' x)
    ((x :q A) × B) = ((x :q A') × B')  ↦  (e :0 A = A') × ((x :0 A) → B x = B' (cast A A' e x))
    Sort u = Sort v, Unit = Unit, …     ↦  True if the levels are equivalent; False if
                                           both are closed and differ; stuck otherwise
    different type formers, or
    different quantities                ↦  False
    a neutral on either side            ↦  stuck: neutral (Head.eqTy X Y)

Why can't `Sort u = Sort v` be `False` when `u` and `v` are different parameters?
(Instantiate them with the same level.) -/
partial def vEqType (g : Globals R) (X Y : Val R) : Val R :=
  let X := whnf X
  let Y := whnf Y
  sorry

/-- **Exercise 4.11c.** `cast A B e t`, computing by the two types:

    cast ((x : A₁) → B₁) ((x : A₂) → B₂) e f
      ↦ fun x => cast (B₁ (cast A₂ A₁ e.1 x)) (B₂ x) (e.2 x) (f (cast A₂ A₁ e.1 x))
    cast ((x : A₁) × B₁) ((x : A₂) × B₂) e p
      ↦ (cast A₁ A₂ e.1 p.1, cast (B₁ p.1) (B₂ (cast A₁ A₂ e.1 p.1)) (e.2 p.1) p.2)
    cast (Sort u) (Sort u) e t ↦ t;  Unit ↦ (); Empty ↦ t
    otherwise ↦ stuck: neutral (Head.cast A B e t)

The Π case needs a template (it builds a lambda); the Σ case can be computed
directly. Quantities must match, or it's stuck. -/
partial def vCast (g : Globals R) (A B e t : Val R) : Val R :=
  let A := whnf A
  let B := whnf B
  sorry


/-- Syntactic equality of two values, quoted at a level above any variable in use. The
side condition of the rules below (as it was of regularity): cheap, and stable under
substitution, since a substitution instance of equal terms is equal. -/
partial def sameVal (g : Globals R) (a b : Val R) : Bool :=
  let l := max a.lvlBound b.lvlBound
  quote g l a == quote g l b

/-- An **inert** type: first-order data, whose values contain no functions, no proofs
but index equations at inert types, and no values of a neutral type: `Enum`, `Unit`,
`Σ`s of inert types, and `μ` types whose index type and fields are inert (`rec` fields;
`arg` fields at inert types; not `hrec`). At an inert type, a cast between equal types
is the identity (regularity, restricted): there it never creates a redex, since an inert
value has no λ to apply, and on a constructor it agrees with `vCastData` up to proof
irrelevance. (The Abel–Coquand box has a `Prop` field, so it is not inert.) `depth`
bounds the nesting of `μ`s in fields. -/
partial def inertTy (g : Globals R) (depth : Nat) (A : Val R) : Bool :=
  depth < 8 &&
  match whnf A with
  | .enum _ => true
  | .unit l => l.isNeverZero
  | .sigma _ _ A₁ B (some s) => s.isNeverZero && inertTy g (depth + 1) A₁ &&
      inertTy g (depth + 1) (Closure.inst g B (Val.var (100000 + depth)))
  | .mu _ I D _ _ _ => inertTy g (depth + 1) I && inertDesc g (depth + 1) D
  | _ => false

/-- Every field of the description is inert (`inertTy`). -/
partial def inertDesc (g : Globals R) (depth : Nat) (D : Val R) : Bool :=
  depth < 8 &&
  match whnf D with
  | .dret _ => true
  | .drec _ _ E => inertDesc g depth E
  | .darg _ S E => match whnf S with
    | .enum ls => (List.range ls.length).all fun k => inertDesc g depth (vApp g E (.tag ls k))
    | S => inertTy g (depth + 1) S && inertDesc g depth (vApp g E (Val.var (100000 + 50 + depth)))
  | _ => false

/-- Two `μ` (or two `ν`) types of the same family, `μ^s_l I D i` and `μ^s_l I D i'`:
the level, index type, description and size agree (`sameVal`), only the indices may
differ. Returns `(l, I, D, s, i, i')`. -/
partial def sameFamily? (g : Globals R) (A B : Val R) :
    Option (Level × Val R × Val R × Val R × Val R × Val R) :=
  match A, B with
  | .mu l I D i s _, .mu l' I' D' i' s' _ | .nu l I D i s _, .nu l' I' D' i' s' _ =>
    if l.equiv l' && sameVal g s s' && sameVal g I I' && sameVal g D D' then
      some (l, I, D, s, i, i')
    else none
  | _, _ => none

/-- The payload types of a family `X` (`muFamilyAt …`/`nuFamilyAt …`) at two indices,
and the equation between them derived from `e : i = i'`:

    transp I i (fun j _ => ⟦D⟧ X i = ⟦D⟧ X j) (reflTy (⟦D⟧ X i)) i' e
      : ⟦D⟧ X i = ⟦D⟧ X i' -/
partial def payloadEq (g : Globals R) (l : Level) (I D X i i' e : Val R) : Val R × Val R × Val R :=
  let Xi := vInterp g l I D X i
  let Xi' := vInterp g l I D X i'
  -- under `j _`: _0 j1 Xi2 X3 D4 I5
  let P : Val R := .lam "j" (.mk [Xi, X, D, I] (.lam "_"
    (.eqTy (.var 2) ((Templates.interpTm l).app (.var 5) |>.app (.var 4) |>.app (.var 3) |>.app (.var 1)))))
  (Xi, Xi', .neutral (.transp I i P (.neutral (.reflTy Xi) #[]) i' e) #[])

/-- `cast` at the data types, by the value (no regularity):

    cast (Desc l I) (Desc l I') e D        by `D` (`e : I = I'`):
      ret i ↦ ret (cast I I' e i);   arg q S E ↦ arg q S (fun s => cast _ _ e (E s))
      rec q j E ↦ rec q (cast I I' e j) (cast _ _ e E)
      hrec q H j E ↦ hrec q H (fun h => cast I I' e (j h)) (cast _ _ e E)
    cast (μ^s D i) (μ^s D i') e (con x)  ↦ con (cast (⟦D⟧ μ^s' i) (⟦D⟧ μ^s' i') e' x)
    cast (ν^s D i) (ν^s D i') e (cocon x) ↦ cocon (cast (⟦D⟧ ν^s' i) (⟦D⟧ ν^s' i') e' x)

where `s = ↑s'` (or `∞`), `e : i = i'` (`vEqType` at a family), and `e'` is `payloadEq`'s
equation. The payload's cast casts every field, so a proof field becomes the
equivalence applied to it (`vCast` between propositions), and a field at a neutral type
stays a stuck cast. A numeral is a value of `builtin nat`, a type with an index in
`Unit` and no proof or neutral fields: its cast is itself (what the rule computes, up
to proof irrelevance). Otherwise stuck. -/
partial def vCastData (g : Globals R) (A B e t stuck : Val R) : Val R :=
  let v (i : Nat) : Term R := .var i
  match A, B with
  | .desc l I, .desc l' I' =>
    if !l.equiv l' then stuck else
    match whnf t with
    | .dret i => .dret (vCast g I I' e i)
    -- s0 E1 e2 I'3 I4
    | .darg q S E => .darg q S (.lam "s" (.mk [E, e, I', I] (.cast (.desc l (v 4)) (.desc l (v 3)) (v 2) (.app (v 1) (v 0)))))
    | .drec q j E => .drec q (vCast g I I' e j) (vCast g A B e E)
    -- h0 j1 e2 I'3 I4
    | .dhrec q H j E => .dhrec q H (.lam "h" (.mk [j, e, I', I] (.cast (v 4) (v 3) (v 2) (.app (v 1) (v 0)))))
        (vCast g A B e E)
    | _ => stuck
  | .mu .., .mu .. => match sameFamily? g A B with
    | some (l, I, D, s, i, i') =>
      let t := whnf t
      if (match t with | .natLit _ => true | _ => false) && sameVal g i i' then t else
      match vNatView g t, sizePred? s with
      | .con x, some s' =>
        let (Xi, Xi', e') := payloadEq g l I D (muFamilyAt l I D s') i i' e
        .con (vCast g Xi Xi' e' x)
      | _, _ => stuck
    | none => stuck
  | .nu .., .nu .. => match sameFamily? g A B, whnf t with
    | some (l, I, D, s, i, i'), .cocon x => match sizePred? s with
      | some s' =>
        let (Xi, Xi', e') := payloadEq g l I D (nuFamilyAt l I D s') i i' e
        .cocon (vCast g Xi Xi' e' x)
      | none => stuck
    | _, _ => stuck
  | _, _ => stuck

/-- **Exercise 1.3.** Read a value back into syntax in a context of `l` local variables.
To quote under a binder, instantiate the closure with `Val.var l` and quote the
result at `l + 1`. Remember to convert levels back into indices. A neutral's head can
be a local, a global or a metavariable, and its spine is folded over the head: so far
only `Elim.app`, with the other eliminations in Exercise 4.5.

**Exercise 4.12** (stage 4c): quote the heads `eq`, `eqTy`, `cast`, `refl`, `reflTy`
and `transp` (just quote their components).

**Exercise 4.5** (stage 4b): quote the structural types and the `fst`, `snd`, `split`
and `absurd` eliminations. A `split`'s motive is under one binder and its body under
two. -/
partial def quote (g : Globals R) (l : Lvl) : Val R → Term R
  -- (given) a glued value keeps its name
  | .unfold n us sp _ => quote g l (.neutral (.global n us) sp)
  | .lazyInd lv I D v P m i x sp _ =>
    sp.foldl (fun t e => match e with
      | .app a => .app t (quote g l a)
      | .fst => .fst t
      | .snd => .snd t
      | _ => t)
      (.ind lv (quote g l I) (quote g l D) v (quote g l P) (quote g l m) (quote g l i) (quote g l x))
  | .natLit n => .natLit n  -- (given)
  | v => sorry

end

/-- Apply a whole spine of eliminations to a value (used to unfold solved metas). -/
def vElims (g : Globals R) (v : Val R) (sp : Array (Elim R)) : Val R :=
  sp.foldl (init := v) fun v e => match e with
    | .app a => vApp g v a
    | .fst => vFst v
    | .snd => vSnd v
    | .split q z m x y b => vSplit g q v z m x y b
    | .absurd m => vAbsurd m v
    | .ecase z m env bs => vEcase g z m v env bs
    | .delim lv P a b c h => vDelim g lv P a b c h v
    | .ind l I D lv P m i => vInd g l I D lv P m i v
    | .out => vOut g v
    | .sfix l I D lv P f s i => vSfix g l I D lv P f s i v
    | .scase l I D lv P m s i => vScase g l I D lv P m s i v

/-- Normal form of a closed term (every definition unfolded). -/
def nf (g : Globals R) (t : Term R) : Term R :=
  let g := { g with eager := true }
  quote g 0 (eval g [] t)

end Wiz
