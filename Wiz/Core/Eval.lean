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

Globals are δ-unfolded eagerly: `const n` evaluates to the value of `n`'s definition.
Axioms (no definition) become neutrals. (Eager unfolding makes error messages huge and
is slow; "glued evaluation" is the standard fix, see the optional exercises.)

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
  | "nat.succ" | "nat.pred" => 1
  | _ => 2

/-- The value of a global registered as an operation on numbers (`builtin nat.add := …`):
`nat.zero` is the literal `0`, and an operation is a closure whose body is a
`Term.natOp` on its arguments, so it computes natively when they are literals. -/
def vBuiltin? (g : Globals R) (n : Name) : Option (Val R) := do
  let k ← g.builtinKey? n
  if !k.startsWith "nat." || k == "nat.beq" then none
  else if k == "nat.zero" then some (.natLit 0)
  else if natOpArity k == 1 then some (.lam "a" (.mk [] (.natOp k #[.var 0])))
  else some (.lam "a" (.mk [] (.lam "b" (.natOp k #[.var 1, .var 0]))))

/-- `absurd` is always stuck: the empty type has no constructors. -/
def vAbsurd (m : Val R) : Val R → Val R
  | .neutral h sp => .neutral h (sp.push (.absurd m))
  | _ => panic! "vAbsurd: ill-typed"

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
  | .pi x bi q dom cod => sorry
  | .lam x body => sorry
  | .app f a => sorry
  | .letE _ _ _ val body => sorry
  | .ann tm _ => sorry
  | .mvar m => .neutral (.mvar m) #[]
  -- Exercise 4.3
  | .sigma x q a b => sorry
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
  let lits := args.filterMap fun a => match whnf a with
    | .natLit n => some n
    | _ => none
  let native : Option Nat := if lits.size != args.size then none else
    match op, lits with
    | "nat.succ", #[a] => some (a + 1)
    | "nat.pred", #[a] => some (a - 1)
    | "nat.add", #[a, b] => some (a + b)
    | "nat.sub", #[a, b] => some (a - b)
    | "nat.mul", #[a, b] => some (a * b)
    | _, _ => none
  match native with
  | some n => .natLit n
  | none => match (g.builtins.lookup op).bind g.find? with
    | some { value := some v, .. } => args.foldl (vApp g) (eval g [] v)
    | _ => panic! s!"no definition for builtin {op}"

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
