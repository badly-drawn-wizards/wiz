import Wiz.Core.Term

/-!
# Values: the semantic domain for normalisation by evaluation

Values are terms that have been evaluated as far as possible:

* binders are represented by **closures** (an environment plus an unevaluated body), so
  instantiating a binder is just "evaluate the body in an extended environment";
* stuck computations are **neutrals**: a head (a local variable or an axiom) applied
  to a spine of arguments.

Local variables inside values use **de Bruijn levels** (counting from the *outside*:
the first variable ever bound is level 0). Levels don't need shifting when you go under
a binder, which is why NbE uses them for values while terms use indices.

Converting level `x` to an index in a context of size `l`: `ix = l - x - 1`.

Reference: András Kovács, *elaboration-zoo* (github.com/AndrasKovacs/elaboration-zoo),
especially `01-eval-closures-debruijn` and `02-typecheck-closures-debruijn`.
-/

namespace Wiz

abbrev Lvl := Nat

inductive Head where
  | local (lvl : Lvl)
  | global (name : Name)
  deriving Repr, BEq, DecidableEq

mutual
inductive Val (R : Type) where
  /-- `head spine[0] spine[1] ...` -/
  | neutral (head : Head) (spine : Array (Val R))
  | sort (level : Nat)
  | pi (x : Name) (q : R) (dom : Val R) (cod : Closure R)
  | lam (x : Name) (body : Closure R)

/-- A body waiting for the value of its bound variable. `env` gives the values of the
body's free variables, with the most recent binder at the head of the list. -/
inductive Closure (R : Type) where
  | mk (env : List (Val R)) (body : Term R)
end

abbrev Env (R : Type) := List (Val R)
abbrev VTy (R : Type) := Val R

instance {R : Type} : Inhabited (Val R) := ⟨.sort 0⟩

/-- The value of the local variable at level `l`. -/
def Val.var {R : Type} (l : Lvl) : Val R := .neutral (.local l) #[]

end Wiz
