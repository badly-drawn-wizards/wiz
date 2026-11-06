import Wiz.Core.Value

/-!
# Evaluation, quotation, normalisation

Normalisation by evaluation (NbE) in two halves:

* `eval : Env → Term → Val` interprets syntax into the semantic domain. β-reduction
  happens for free, because applying a `Val.lam` just evaluates its closure body.
* `quote : Lvl → Val → Term` reads a value back into β-normal syntax, going under
  binders by applying closures to fresh variables `Val.var l`.

`nf = quote ∘ eval`.

Globals are δ-unfolded eagerly: `const n` evaluates to the value of `n`'s definition.
Axioms (no definition) become neutrals. (Eager unfolding makes error messages huge and
is slow; "glued evaluation" is the standard fix, see the optional exercises.)

These are `partial` because the untyped evaluator need not terminate (`Ω = (λx. x x)(λx. x x)`).
On well-typed terms they do.
-/

namespace Wiz

variable {R : Type}

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
* `mvar`: (given) metavariables are stuck neutrals. -/
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
  --sol>

/-- **Exercise 1.2a.** Semantic application.
A `lam` β-reduces; a neutral grows its spine. Anything else is a type error that the
checker should have ruled out (use `panic!`). -/
partial def vApp (g : Globals R) : Val R → Val R → Val R
  --<sol
  | .lam _ c, a => Closure.inst g c a
  | .neutral h sp, a => .neutral h (sp.push a)
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

end

/-- **Exercise 1.3.** Read a value back into syntax in a context of `l` local variables.
To quote under a binder, instantiate the closure with `Val.var l` and quote the
result at `l + 1`. Remember to convert levels back into indices. A neutral's head can
be a local, a global or a metavariable. -/
partial def quote (g : Globals R) (l : Lvl) : Val R → Term R
  --<sol
  | .neutral h sp =>
    let hd : Term R := match h with
      | .local x => .var (l - x - 1)
      | .global n us => .const n us
      | .mvar m => .mvar m
    sp.foldl (fun acc v => .app acc (quote g l v)) hd
  | .sort k => .sort k
  | .pi x bi q a b => .pi x bi q (quote g l a) (quote g (l + 1) (Closure.inst g b (Val.var l)))
  | .lam x b => .lam x (quote g (l + 1) (Closure.inst g b (Val.var l)))
  --|ex
  --| | v => sorry
  --sol>

/-- Normal form of a closed term. -/
def nf (g : Globals R) (t : Term R) : Term R :=
  quote g 0 (eval g [] t)

end Wiz
