import Wiz.Core.Term

/-!
# Values: the semantic domain for normalisation by evaluation

Values are terms that have been evaluated as far as possible:

* binders are represented by **closures** (an environment plus an unevaluated body), so
  instantiating a binder is just "evaluate the body in an extended environment";
* stuck computations are **neutrals**: a head (a local variable, an axiom or a
  metavariable) followed by a **spine** of eliminations waiting on it, such as
  applications `f a`, projections `p.1`, or a `let (x, y) := p; …` split.

Local variables inside values use **de Bruijn levels** (counting from the *outside*:
the first variable ever bound is level 0). Levels don't need shifting when you go under
a binder, which is why NbE uses them for values while terms use indices.

Converting level `x` to an index in a context of size `l`: `ix = l - x - 1`.

Reference: András Kovács, *elaboration-zoo* (github.com/AndrasKovacs/elaboration-zoo),
especially `01-eval-closures-debruijn` and `02-typecheck-closures-debruijn`.
-/

namespace Wiz

abbrev Lvl := Nat

mutual
/-- What a neutral is stuck on. Besides variables, globals and metas, stage 4c adds
stuck observational constructs: an equality or cast whose type is a neutral, and
proofs (`refl`, `transp`), which never compute because proofs are irrelevant. -/
inductive Head (R : Type) where
  | local (lvl : Lvl)
  | global (name : Name) (levels : List Level)
  /-- an unsolved (as far as the kernel knows) metavariable -/
  | mvar (id : Nat)
  | eq (A a b : Val R)
  | eqTy (A B : Val R)
  | cast (A B e t : Val R)
  | refl (A a : Val R)
  | reflTy (X : Val R)
  | transp (A a P p b e : Val R)

inductive Val (R : Type) where
  /-- `head` followed by the eliminations in `spine`, innermost first -/
  | neutral (head : Head R) (spine : Array (Elim R))
  | sort (level : Level)
  | pi (x : Name) (bi : BinderInfo) (q : R) (dom : Val R) (cod : Closure R)
  | lam (x : Name) (body : Closure R)
  | sigma (x : Name) (q : R) (fst : Val R) (snd : Closure R)
  | pair (a b : Val R)
  | unit (level : Level)
  | tt
  | empty (level : Level)

/-- An elimination stuck on a neutral. -/
inductive Elim (R : Type) where
  | app (arg : Val R)
  | fst
  | snd
  /-- `motive` is under one binder, `body` under two -/
  | split (q : R) (z : Name) (motive : Closure R) (x y : Name) (body : Closure R)
  | absurd (motive : Val R)

/-- A body waiting for the values of its bound variables. `env` gives the values of
the body's free variables, with the most recent binder at the head of the list. -/
inductive Closure (R : Type) where
  | mk (env : List (Val R)) (body : Term R)
end

abbrev Env (R : Type) := List (Val R)
abbrev VTy (R : Type) := Val R

instance {R : Type} : Inhabited (Val R) := ⟨.sort 0⟩

/-- The value of the local variable at level `l`. -/
def Val.var {R : Type} (l : Lvl) : Val R := .neutral (.local l) #[]

/-- Heads are equal if they are the same variable, or the same global at equivalent
levels. (The stage 4c heads contain values, which `convNe` compares.) -/
def Head.equiv {R : Type} : Head R → Head R → Bool
  | .local a, .local b => a == b
  | .global n us, .global m vs =>
    n == m && us.length == vs.length && (us.zip vs).all fun (u, v) => u.equiv v
  | .mvar a, .mvar b => a == b
  | _, _ => false

end Wiz
