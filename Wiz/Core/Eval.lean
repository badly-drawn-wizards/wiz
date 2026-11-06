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
  | v => sorry

/-- **Exercise 4.4c.** Second projection. -/
def vSnd : Val R → Val R
  | v => sorry

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
  | .var ix => sorry
  | .const n us => sorry
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

/-- **Exercise 1.2a.** Semantic application.
A `lam` β-reduces; a neutral grows its spine (with `Elim.app`). Anything else is a
type error that the checker should have ruled out (use `panic!`). -/
partial def vApp (g : Globals R) : Val R → Val R → Val R
  | f, a => sorry

/-- **Exercise 1.2b.** Instantiate a closure with a value for its bound variable. -/
partial def Closure.inst (g : Globals R) : Closure R → Val R → Val R
  | .mk env body, a => sorry

/-- Instantiate a closure over two binders (`a` first, then `b`). -/
partial def Closure.inst2 (g : Globals R) : Closure R → Val R → Val R → Val R
  | .mk env body, a, b => eval g (b :: a :: env) body

/-- **Exercise 4.4a.** `let (x, y) := s; body`: β-reduces on a `pair`, gets stuck on a
neutral. -/
partial def vSplit (g : Globals R) (q : R) (s : Val R) (z : Name) (m : Closure R) (x y : Name)
    (body : Closure R) : Val R :=
  sorry

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
  | v => sorry

/-- Normal form of a closed term. -/
def nf (g : Globals R) (t : Term R) : Term R :=
  quote g 0 (eval g [] t)

end Wiz
