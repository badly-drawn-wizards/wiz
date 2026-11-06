import Wiz.Core.Value

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

variable {R : Type} [Zero R] [DecidableEq R]

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
  | .pi x bi q dom cod => .pi x bi q (eval g env dom) (.mk env cod)
  | .lam x body => .lam x (.mk env body)
  | .app f a => vApp g (eval g env f) (eval g env a)
  | .letE _ _ _ val body => eval g (eval g env val :: env) body
  | .ann tm _ => eval g env tm
  | .mvar m => .neutral (.mvar m) #[]
  | .sigma x q a b => .sigma x q (eval g env a) (.mk env b)
  | .pair a b => .pair (eval g env a) (eval g env b)
  | .fst t => vFst (eval g env t)
  | .snd t => vSnd (eval g env t)
  | .split q s z m x y b => vSplit g q (eval g env s) z (.mk env m) x y (.mk env b)
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
  --sol>

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
partial def vSplit (g : Globals R) (q : R) (s : Val R) (z : Name) (m : Closure R) (x y : Name)
    (body : Closure R) : Val R :=
  --<sol
  match s with
  | .pair a b => Closure.inst2 g body a b
  | .neutral h sp => .neutral h (sp.push (.split q z m x y body))
  | _ => panic! "vSplit: ill-typed"
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
    .pi x .default 0 A₁ (.mk [b, a, .lam x B] (.eq (.app (v 3) (v 0)) (.app (v 2) (v 0)) (.app (v 1) (v 0))))
  | .sigma x _ A₁ B =>
    -- env (inside the Σ, after `e`): b, a, B, A₁
    let P : Term R := .lam "y" (.lam "_" (.eqTy (.app (v 5) (.fst (v 4))) (.app (v 5) (v 1))))
    let apB : Term R := .transp (v 4) (.fst (v 2)) P (.reflTy (.app (v 3) (.fst (v 2)))) (.fst (v 1)) (v 0)
    let body : Term R := .eq (.app (v 3) (.fst (v 1)))
      (.cast (.app (v 3) (.fst (v 2))) (.app (v 3) (.fst (v 1))) apB (.snd (v 2))) (.snd (v 1))
    .sigma "e" 0 (vEq g A₁ (vFst a) (vFst b)) (.mk [b, a, .lam x B, A₁] body)
  | .unit _ | .empty _ => .unit 0
  | .sort l =>
    if l.equiv 0 then
      -- (a → b) × (b → a)
      .sigma "_" 0 (.pi "_" .default 0 a (.mk [b] (v 1))) (.mk [a, b] (.pi "_" .default 0 (v 2) (v 2)))
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
    | .pi .. | .sigma .. | .sort _ | .unit _ | .empty _ => true
    | _ => false
  match X, Y with
  | .pi _ _ q A B, .pi _ _ q' A' B' =>
    if q != q' then .empty 0 else
    -- env (inside the Σ, after `e`): B', B, A', A; inside the Π add `x`
    .sigma "e" 0 (vEqType g A' A) (.mk [.lam "x" B', .lam "x" B, A', A]
      (.pi "x" .default 0 (v 3) (.eqTy (.app (v 3) (.cast (v 4) (v 5) (v 1) (v 0))) (.app (v 2) (v 0)))))
  | .sigma _ q A B, .sigma _ q' A' B' =>
    if q != q' then .empty 0 else
    .sigma "e" 0 (vEqType g A A') (.mk [.lam "x" B', .lam "x" B, A', A]
      (.pi "x" .default 0 (v 4) (.eqTy (.app (v 3) (v 0)) (.app (v 2) (.cast (v 5) (v 4) (v 1) (v 0))))))
  | .sort u, .sort w | .unit u, .unit w | .empty u, .empty w => levels u w
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
    if q != q' then stuck else
    -- env: t, e, B₂, B₁, A₂, A₁; index 0 is the new `x`
    let c : Term R := .cast (v 5) (v 6) (.fst (v 2)) (v 0)
    .lam x (.mk [t, e, .lam x B₂, .lam x B₁, A₂, A₁]
      (.cast (.app (v 4) c) (.app (v 3) (v 0)) (.app (.snd (v 2)) (v 0)) (.app (v 1) c)))
  | .sigma _ q A₁ B₁, .sigma _ q' A₂ B₂ =>
    if q != q' then stuck else
    let t₁ := vFst t
    let c₁ := vCast g A₁ A₂ (vFst e) t₁
    .pair c₁ (vCast g (Closure.inst g B₁ t₁) (Closure.inst g B₂ c₁) (vApp g (vSnd e) t₁) (vSnd t))
  | .sort u, .sort w | .empty u, .empty w => if u.equiv w then t else stuck
  | .unit u, .unit w => if u.equiv w then .tt else stuck
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
        .split q acc z (quote g (l + 1) (Closure.inst g m (Val.var l)))
          x y (quote g (l + 2) (Closure.inst2 g b (Val.var l) (Val.var (l + 1))))
      | .absurd m => .absurd (quote g l m) acc
  | .sort k => .sort k
  | .pi x bi q a b => .pi x bi q (quote g l a) (quote g (l + 1) (Closure.inst g b (Val.var l)))
  | .lam x b => .lam x (quote g (l + 1) (Closure.inst g b (Val.var l)))
  | .sigma x q a b => .sigma x q (quote g l a) (quote g (l + 1) (Closure.inst g b (Val.var l)))
  | .pair a b => .pair (quote g l a) (quote g l b)
  | .unit k => .unit k
  | .tt => .tt
  | .empty k => .empty k
  --|ex
  --| | v => sorry
  --sol>

/-- Normal form of a closed term. -/
def nf (g : Globals R) (t : Term R) : Term R :=
  quote g 0 (eval g [] t)

end Wiz
