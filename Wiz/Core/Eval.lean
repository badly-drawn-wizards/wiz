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

/-- **Exercise 4.4b.** First projection. -/
def vFst : Val R → Val R
  --<sol
  | .pair a _ => a
  | .neutral h sp => .neutral h (sp.push .fst)
  | _ => panic! "vFst: ill-typed"
  --|ex
  --| | v => sorry
  --sol>

/-- **Exercise 4.4c.** Second projection. -/
def vSnd : Val R → Val R
  --<sol
  | .pair _ b => b
  | .neutral h sp => .neutral h (sp.push .snd)
  | _ => panic! "vSnd: ill-typed"
  --|ex
  --| | v => sorry
  --sol>

/-- `absurd` is always stuck: the empty type has no constructors. -/
def vAbsurd (m : Val R) : Val R → Val R
  | .neutral h sp => .neutral h (sp.push (.absurd m))
  | _ => panic! "vAbsurd: ill-typed"

mutual

/-- **Exercise 1.1.** Evaluate a term in an environment.

* `var ix`: look it up in `env` (index 0 is the head).
* `const n us`: evaluate the definition in the *empty* environment if there is one,
  after instantiating its level parameters with `us` (`Term.instLevels`). Otherwise
  it is a stuck `neutral (.global n us) #[]`.
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
  --<sol
  | .var ix => env[ix]!
  | .const n us => match g.find? n with
    | some { value := some v, levelParams, .. } => eval g [] (v.instLevels levelParams us)
    | _ => .neutral (.global n us) #[]
  | .sort l => .sort l
  | .pi x bi q dom cod => .pi x bi (eval g env q) (eval g env dom) (.mk env cod)
  | .lam x body => .lam x (.mk env body)
  | .app f a => vApp g (eval g env f) (eval g env a)
  | .letE _ _ _ val body => eval g (eval g env val :: env) body
  | .ann tm _ => eval g env tm
  | .mvar m => .neutral (.mvar m) #[]
  | .sigma x q a b => .sigma x (eval g env q) (eval g env a) (.mk env b)
  | .pair a b => .pair (eval g env a) (eval g env b)
  | .fst t => vFst (eval g env t)
  | .snd t => vSnd (eval g env t)
  | .split q s z m x y b => vSplit g (eval g env q) (eval g env s) z (.mk env m) x y (.mk env b)
  | .unit l => .unit l
  | .tt => .tt
  | .empty l => .empty l
  | .absurd m t => vAbsurd (eval g env m) (eval g env t)
  | .eq A a b => vEq g (eval g env A) (eval g env a) (eval g env b)
  | .eqTy A B => vEqType g (eval g env A) (eval g env B)
  | .cast A B e t => vCast g (eval g env A) (eval g env B) (eval g env e) (eval g env t)
  | .refl A a => .neutral (.refl (eval g env A) (eval g env a)) #[]
  | .reflTy X => .neutral (.reflTy (eval g env X)) #[]
  | .transp A a P p b e =>
    .neutral (.transp (eval g env A) (eval g env a) (eval g env P) (eval g env p)
      (eval g env b) (eval g env e)) #[]
  | .qty => .qty
  | .qlit r => .qlit r
  | .enum ls => .enum ls
  | .tag ls i => .tag ls i
  | .ecase z m s bs => vEcase g z (.mk env m) (eval g env s) env bs
  | .desc l I => .desc l (eval g env I)
  | .dret i => .dret (eval g env i)
  | .darg q S D => .darg (eval g env q) (eval g env S) (eval g env D)
  | .drec q j D => .drec (eval g env q) (eval g env j) (eval g env D)
  | .delim v P a b c D =>
    vDelim g v (eval g env P) (eval g env a) (eval g env b) (eval g env c) (eval g env D)
  | .mu l I D i h => .mu l (eval g env I) (eval g env D) (eval g env i) (evalHint g env h)
  | .con x => .con (eval g env x)
  | .ind l I D v P m i x =>
    vInd g l (eval g env I) (eval g env D) v (eval g env P) (eval g env m) (eval g env i) (eval g env x)
  | .nu l I D i h => .nu l (eval g env I) (eval g env D) (eval g env i) (evalHint g env h)
  | .out x => vOut g (eval g env x)
  | .coit l I D S st i s =>
    .coit l (eval g env I) (eval g env D) (eval g env S) (eval g env st) (eval g env i) (eval g env s)
  --|ex
  --| | .var ix => sorry
  --| | .const n us => sorry
  --| | .sort l => sorry
  --| | .pi x bi q dom cod => sorry
  --| | .lam x body => sorry
  --| | .app f a => sorry
  --| | .letE _ _ _ val body => sorry
  --| | .ann tm _ => sorry
  --| | .mvar m => .neutral (.mvar m) #[]
  --| -- Exercise 4.3
  --| | .sigma x q a b => sorry
  --| | .pair a b => sorry
  --| | .fst t => sorry
  --| | .snd t => sorry
  --| | .split q s z m x y b => sorry
  --| | .unit l => sorry
  --| | .tt => sorry
  --| | .empty l => sorry
  --| | .absurd m t => sorry
  --| -- Exercise 4.10
  --| | .eq A a b => sorry
  --| | .eqTy A B => sorry
  --| | .cast A B e t => sorry
  --| | .refl A a => sorry
  --| | .reflTy X => sorry
  --| | .transp A a P p b e => sorry
  --| | .qty => .qty
  --| | .qlit r => .qlit r
  --| -- Exercise 4.18: constructors evaluate their parts; eliminators use
  --| -- vEcase, vDelim, vInd and vOut.
  --| | .enum ls => sorry
  --| | .tag ls i => sorry
  --| | .ecase z m s bs => sorry
  --| | .desc l I => sorry
  --| | .dret i => sorry
  --| | .darg q S D => sorry
  --| | .drec q j D => sorry
  --| | .delim v P a b c D => sorry
  --| | .mu l I D i h => sorry
  --| | .con x => sorry
  --| | .ind l I D v P m i x => sorry
  --| | .nu l I D i h => sorry
  --| | .out x => sorry
  --| | .coit l I D S st i s => sorry
  --sol>

/-- Evaluate a display hint's arguments. -/
partial def evalHint (g : Globals R) (env : Env R) :
    Option (Name × List Level × List (Term R)) → Option (Name × List Level × List (Val R))
  | some (n, us, as) => some (n, us, as.map (eval g env))
  | none => none

/-- **Exercise 1.2a.** Semantic application.
A `lam` β-reduces; a neutral grows its spine (with `Elim.app`). Anything else is a
type error that the checker should have ruled out (use `panic!`). -/
partial def vApp (g : Globals R) : Val R → Val R → Val R
  --<sol
  | .lam _ c, a => Closure.inst g c a
  | .neutral h sp, a => .neutral h (sp.push (.app a))
  | _, _ => panic! "vApp: ill-typed application"
  --|ex
  --| | f, a => sorry
  --sol>

/-- **Exercise 1.2b.** Instantiate a closure with a value for its bound variable. -/
partial def Closure.inst (g : Globals R) : Closure R → Val R → Val R
  --<sol
  | .mk env body, a => eval g (a :: env) body
  --|ex
  --| | .mk env body, a => sorry
  --sol>

/-- Instantiate a closure over two binders (`a` first, then `b`). -/
partial def Closure.inst2 (g : Globals R) : Closure R → Val R → Val R → Val R
  | .mk env body, a, b => eval g (b :: a :: env) body

/-- **Exercise 4.4a.** `let (x, y) := s; body`: β-reduces on a `pair`, gets stuck on a
neutral. -/
partial def vSplit (g : Globals R) (q : Val R) (s : Val R) (z : Name) (m : Closure R) (x y : Name)
    (body : Closure R) : Val R :=
  --<sol
  match s with
  | .pair a b => Closure.inst2 g body a b
  | .neutral h sp => .neutral h (sp.push (.split q z m x y body))
  | _ => panic! "vSplit: ill-typed"
  --|ex
  --| sorry
  --sol>

/- ### Data (stage 4d)

`vEcase`, `vDelim`, `vInd` and `vOut` compute on canonical arguments and are stuck on
neutrals. `vInd` and `vOut` use the description templates of `Wiz.Core.Templates`. -/

/-- `λ j. μ D j`, the family being defined, as a value. -/
partial def muFamily (l : Level) (I D : Val R) : Val R :=
  .lam "j" (.mk [D, I] (.mu l (.var 2) (.var 1) (.var 0) none))

partial def nuFamily (l : Level) (I D : Val R) : Val R :=
  .lam "j" (.mk [D, I] (.nu l (.var 2) (.var 1) (.var 0) none))

/-- `⟦D⟧ X i` -/
partial def vInterp (g : Globals R) (l : Level) (I D X i : Val R) : Val R :=
  [I, D, X, i].foldl (vApp g) (eval g [] (Templates.interpTm l))

/-- `All D X P i xs` -/
partial def vAll (g : Globals R) (l v : Level) (I D X P i xs : Val R) : Val R :=
  [I, D, X, P, i, xs].foldl (vApp g) (eval g [] (Templates.allTm l v))

/-- **Exercise 4.19a.** `ecase` on a tag picks the branch (evaluated in `env`). -/
partial def vEcase (g : Globals R) (z : Name) (m : Closure R) (s : Val R) (env : Env R)
    (bs : List (Term R)) : Val R :=
  --<sol
  match s with
  | .tag _ i => eval g env (bs[i]?.getD (.var 0))
  | .neutral h sp => .neutral h (sp.push (.ecase z m env bs))
  | _ => panic! "vEcase: ill-typed"
  --|ex
  --| sorry
  --sol>

/-- **Exercise 4.19b.** The description eliminator:

    delim (ret i)     ↦ mret i
    delim (arg q S D) ↦ marg q S D (fun s => delim (D s))
    delim (rec q j D) ↦ mrec q j D (delim D)

The `fun s => …` is a closure over a small template, as in `vEq`. -/
partial def vDelim (g : Globals R) (v : Level) (P mret marg mrec D : Val R) : Val R :=
  --<sol
  match D with
  | .dret i => vApp g mret i
  | .darg q S E =>
    -- s0 E1 mrec2 marg3 mret4 P5
    let ih : Val R := .lam "s" (.mk [E, mrec, marg, mret, P]
      (.delim v (.var 5) (.var 4) (.var 3) (.var 2) (.app (.var 1) (.var 0))))
    [q, S, E, ih].foldl (vApp g) marg
  | .drec q j E => [q, j, E, vDelim g v P mret marg mrec E].foldl (vApp g) mrec
  | .neutral h sp => .neutral h (sp.push (.delim v P mret marg mrec))
  | _ => panic! "vDelim: ill-typed"
  --|ex
  --| sorry
  --sol>

/-- **Exercise 4.19c.** Induction computes on constructors:

    ind P m i (con xs) ↦ m i xs (hyps D (μ D) P (fun j y => ind P m j y) i xs)

(`Templates.hypsTm`; the `fun j y => …` is a template closure). -/
partial def vInd (g : Globals R) (l : Level) (I D : Val R) (v : Level) (P m i x : Val R) : Val R :=
  --<sol
  match x with
  | .con xs =>
    -- y0 j1 m2 P3 D4 I5
    let f : Val R := .lam "j" (.mk [m, P, D, I]
      (.lam "y" (.ind l (.var 5) (.var 4) v (.var 3) (.var 2) (.var 1) (.var 0))))
    let hyps := [I, D, muFamily l I D, P, f, i, xs].foldl (vApp g) (eval g [] (Templates.hypsTm l v))
    [i, xs, hyps].foldl (vApp g) m
  | .neutral h sp => .neutral h (sp.push (.ind l I D v P m i))
  | _ => panic! "vInd: ill-typed"
  --|ex
  --| sorry
  --sol>

/-- **Exercise 4.19d.** Observing an unfolding runs one step and re-wraps the
recursive positions:

    out (coit S step i s) ↦ map D S (ν D) (fun j s => coit S step j s) i (step i s) -/
partial def vOut (g : Globals R) (x : Val R) : Val R :=
  --<sol
  match x with
  | .coit l I D S step i s =>
    -- s0 j1 step2 S3 D4 I5
    let f : Val R := .lam "j" (.mk [step, S, D, I]
      (.lam "s" (.coit l (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))))
    [I, D, S, nuFamily l I D, f, i, [i, s].foldl (vApp g) step].foldl (vApp g) (eval g [] (Templates.mapTm l))
  | .neutral h sp => .neutral h (sp.push .out)
  | _ => panic! "vOut: ill-typed"
  --|ex
  --| sorry
  --sol>

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
  --<sol
  let v (i : Nat) : Term R := .var i
  match A with
  | .pi x _ _ A₁ B =>
    -- (x :0 A₁) → (B x ∋ a x = b x); env: b, a, B
    .pi x .default (.qlit 0) A₁ (.mk [b, a, .lam x B] (.eq (.app (v 3) (v 0)) (.app (v 2) (v 0)) (.app (v 1) (v 0))))
  | .sigma x _ A₁ B =>
    -- env (inside the Σ, after `e`): b, a, B, A₁
    let P : Term R := .lam "y" (.lam "_" (.eqTy (.app (v 5) (.fst (v 4))) (.app (v 5) (v 1))))
    let apB : Term R := .transp (v 4) (.fst (v 2)) P (.reflTy (.app (v 3) (.fst (v 2)))) (.fst (v 1)) (v 0)
    let body : Term R := .eq (.app (v 3) (.fst (v 1)))
      (.cast (.app (v 3) (.fst (v 2))) (.app (v 3) (.fst (v 1))) apB (.snd (v 2))) (.snd (v 1))
    .sigma "e" (.qlit 0) (vEq g A₁ (vFst a) (vFst b)) (.mk [b, a, .lam x B, A₁] body)
  | .unit _ | .empty _ => .unit 0
  | .enum _ => match a, b with
    | .tag _ i, .tag _ j => if i == j then .unit 0 else .empty 0
    | _, _ => .neutral (.eq A a b) #[]
  | .mu l I D i _ => match a, b with
    | .con x, .con y => vEq g (vInterp g l I D (muFamily l I D) i) x y
    | _, _ => .neutral (.eq A a b) #[]
  | .sort l =>
    if l.equiv 0 then
      -- (a → b) × (b → a)
      .sigma "_" (.qlit 0) (.pi "_" .default (.qlit 0) a (.mk [b] (v 1))) (.mk [a, b] (.pi "_" .default (.qlit 0) (v 2) (v 2)))
    else if l.isNeverZero then vEqType g a b
    else .neutral (.eq A a b) #[]
  | _ => .neutral (.eq A a b) #[]
  --|ex
  --| sorry
  --sol>

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
  --<sol
  let v (i : Nat) : Term R := .var i
  let levels (u w : Level) : Val R :=
    if u.equiv w then .unit 0
    else if u.toNat?.isSome && w.toNat?.isSome then .empty 0
    else .neutral (.eqTy X Y) #[]
  let canonical : Val R → Bool
    | .pi .. | .sigma .. | .sort _ | .unit _ | .empty _ | .enum _ | .desc .. | .mu .. | .nu .. => true
    | _ => false
  match X, Y with
  | .pi _ _ q A B, .pi _ _ q' A' B' =>
    if sameQty q q' == some false then .empty 0 else if sameQty q q' == none then .neutral (.eqTy X Y) #[] else
    -- env (inside the Σ, after `e`): B', B, A', A; inside the Π add `x`
    .sigma "e" (.qlit 0) (vEqType g A' A) (.mk [.lam "x" B', .lam "x" B, A', A]
      (.pi "x" .default (.qlit 0) (v 3) (.eqTy (.app (v 3) (.cast (v 4) (v 5) (v 1) (v 0))) (.app (v 2) (v 0)))))
  | .sigma _ q A B, .sigma _ q' A' B' =>
    if sameQty q q' == some false then .empty 0 else if sameQty q q' == none then .neutral (.eqTy X Y) #[] else
    .sigma "e" (.qlit 0) (vEqType g A A') (.mk [.lam "x" B', .lam "x" B, A', A]
      (.pi "x" .default (.qlit 0) (v 4) (.eqTy (.app (v 3) (v 0)) (.app (v 2) (.cast (v 5) (v 4) (v 1) (v 0))))))
  | .sort u, .sort w | .unit u, .unit w | .empty u, .empty w => levels u w
  | .enum ls, .enum ls' => if ls.length == ls'.length then .unit 0 else .empty 0
  | .desc .., .desc .. | .mu .., .mu .. | .nu .., .nu .. => .neutral (.eqTy X Y) #[]
  | _, _ => if canonical X && canonical Y then .empty 0 else .neutral (.eqTy X Y) #[]
  --|ex
  --| sorry
  --sol>

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
  --<sol
  let v (i : Nat) : Term R := .var i
  let stuck : Val R := .neutral (.cast A B e t) #[]
  match A, B with
  | .pi x _ q A₁ B₁, .pi _ _ q' A₂ B₂ =>
    if sameQty q q' != some true then stuck else
    -- env: t, e, B₂, B₁, A₂, A₁; index 0 is the new `x`
    let c : Term R := .cast (v 5) (v 6) (.fst (v 2)) (v 0)
    .lam x (.mk [t, e, .lam x B₂, .lam x B₁, A₂, A₁]
      (.cast (.app (v 4) c) (.app (v 3) (v 0)) (.app (.snd (v 2)) (v 0)) (.app (v 1) c)))
  | .sigma _ q A₁ B₁, .sigma _ q' A₂ B₂ =>
    if sameQty q q' != some true then stuck else
    let t₁ := vFst t
    let c₁ := vCast g A₁ A₂ (vFst e) t₁
    .pair c₁ (vCast g (Closure.inst g B₁ t₁) (Closure.inst g B₂ c₁) (vApp g (vSnd e) t₁) (vSnd t))
  | .sort u, .sort w | .empty u, .empty w => if u.equiv w then t else stuck
  | .unit u, .unit w => if u.equiv w then .tt else stuck
  | .enum ls, .enum ls' => if ls.length == ls'.length then t else stuck
  | _, _ => stuck
  --|ex
  --| sorry
  --sol>

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
    | .delim lv P a b c => vDelim g lv P a b c v
    | .ind l I D lv P m i => vInd g l I D lv P m i v
    | .out => vOut g v

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
  --<sol
  | .neutral h sp =>
    let hd : Term R := match h with
      | .local x => .var (l - x - 1)
      | .global n us => .const n us
      | .mvar m => .mvar m
      | .eq A a b => .eq (quote g l A) (quote g l a) (quote g l b)
      | .eqTy A B => .eqTy (quote g l A) (quote g l B)
      | .cast A B e t => .cast (quote g l A) (quote g l B) (quote g l e) (quote g l t)
      | .refl A a => .refl (quote g l A) (quote g l a)
      | .reflTy X => .reflTy (quote g l X)
      | .transp A a P p b e =>
        .transp (quote g l A) (quote g l a) (quote g l P) (quote g l p) (quote g l b) (quote g l e)
    sp.foldl (init := hd) fun acc e => match e with
      | .app v => .app acc (quote g l v)
      | .fst => .fst acc
      | .snd => .snd acc
      | .split q z m x y b =>
        .split (quote g l q) acc z (quote g (l + 1) (Closure.inst g m (Val.var l)))
          x y (quote g (l + 2) (Closure.inst2 g b (Val.var l) (Val.var (l + 1))))
      | .absurd m => .absurd (quote g l m) acc
      | .ecase z m env bs =>
        .ecase z (quote g (l + 1) (Closure.inst g m (Val.var l))) acc
          (bs.map fun b => quote g l (eval g env b))
      | .delim v P a b c => .delim v (quote g l P) (quote g l a) (quote g l b) (quote g l c) acc
      | .ind lv I D v P m i => .ind lv (quote g l I) (quote g l D) v (quote g l P) (quote g l m) (quote g l i) acc
      | .out => .out acc
  | .sort k => .sort k
  | .pi x bi q a b => .pi x bi (quote g l q) (quote g l a) (quote g (l + 1) (Closure.inst g b (Val.var l)))
  | .lam x b => .lam x (quote g (l + 1) (Closure.inst g b (Val.var l)))
  | .sigma x q a b => .sigma x (quote g l q) (quote g l a) (quote g (l + 1) (Closure.inst g b (Val.var l)))
  | .pair a b => .pair (quote g l a) (quote g l b)
  | .unit k => .unit k
  | .tt => .tt
  | .empty k => .empty k
  | .qty => .qty
  | .qlit r => .qlit r
  | .enum ls => .enum ls
  | .tag ls i => .tag ls i
  | .desc k I => .desc k (quote g l I)
  | .dret i => .dret (quote g l i)
  | .darg q S D => .darg (quote g l q) (quote g l S) (quote g l D)
  | .drec q j D => .drec (quote g l q) (quote g l j) (quote g l D)
  | .mu k I D i h => .mu k (quote g l I) (quote g l D) (quote g l i) (h.map fun (n, us, as) => (n, us, as.map (quote g l)))
  | .con x => .con (quote g l x)
  | .nu k I D i h => .nu k (quote g l I) (quote g l D) (quote g l i) (h.map fun (n, us, as) => (n, us, as.map (quote g l)))
  | .coit k I D S st i s =>
    .coit k (quote g l I) (quote g l D) (quote g l S) (quote g l st) (quote g l i) (quote g l s)
  --|ex
  --| | v => sorry
  --sol>

/-- Normal form of a closed term. -/
def nf (g : Globals R) (t : Term R) : Term R :=
  quote g 0 (eval g [] t)

end Wiz
