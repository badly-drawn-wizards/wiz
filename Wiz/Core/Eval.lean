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

variable {R : Type}

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
