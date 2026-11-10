import Wiz.Compiler.Erase

/-!
# Inlining (stage 22i)

`attribute [inline] f` asks compiled code to substitute `f`'s erased body wherever `f`
is applied to all its arguments. The point is higher-order combinators such as the
borrow scopes of `lib/Region.wiz`: `Uniq.borrow σ s (fun ρ h v r => …)` would build a
closure for the body and call it through `ap`. Inlined, the scope is
`(λ S B σ s body. … body σ ◾ ◾ s …) ◾ ◾ σ s (λ ρ h v r. …)`, and a small simplifier
finishes the job:

* a redex `(λ x. b) a` is `let x := a; b`;
* `let x := v; b` is substituted away when `v` is a variable or `◾` (copying them costs
  nothing), or when `v` is a lambda that `b` uses exactly once, not under a lambda (so
  the lambda is neither duplicated nor moved into a loop). The lambda then lands in the
  head of an application and is reduced again.

So the body runs in place: no closure, no `ap`. Inlining a recursive definition stops
after a few levels (`fuel`). The pass only runs over definitions that mention an inline
definition, so other code is untouched.
-/

namespace Wiz

/-- The builtin key that marks a definition `inline`. -/
def inlineKey : Name := "inline"

namespace ETerm

/-- Uses of the variable `k`: how many, and whether one is under a lambda or `fix`. -/
partial def uses (k : Nat) : ETerm → Nat × Bool
  | var i => (if i == k then 1 else 0, false)
  | lam _ b | fix _ b => let (n, _) := uses (k + 1) b; (n, n > 0)
  | app f a => add (uses k f) (uses k a)
  | letE _ v b => add (uses k v) (uses (k + 1) b)
  | obj _ fs | prim _ fs => fs.foldl (fun acc f => add acc (uses k f)) (0, false)
  | proj _ t => uses k t
  | case s bs => bs.foldl (fun acc b => add acc (uses k b)) (uses k s)
  | _ => (0, false)
where
  add : Nat × Bool → Nat × Bool → Nat × Bool
    | (a, b), (c, d) => (a + c, b || d)

/-- Substitute `v` (a term outside the binder) for the variable `k`, removing the binder. -/
partial def subst (k : Nat) (v : ETerm) : ETerm → ETerm
  | var i => if i == k then v.lift k else if i > k then var (i - 1) else var i
  | lam x b => lam x (subst (k + 1) v b)
  | fix x b => fix x (subst (k + 1) v b)
  | app f a => app (subst k v f) (subst k v a)
  | letE x a b => letE x (subst k v a) (subst (k + 1) v b)
  | obj t fs => obj t (fs.map (subst k v))
  | proj i t => proj i (subst k v t)
  | case s bs => case (subst k v s) (bs.map (subst k v))
  | prim op as => prim op (as.map (subst k v))
  | t => t

private def lamArity : ETerm → Nat
  | lam _ b => lamArity b + 1
  | _ => 0

private def spine : ETerm → List ETerm → ETerm × List ETerm
  | app f a, acc => spine f (a :: acc)
  | t, acc => (t, acc)

/-- `(λ x… . b) a…` as `let x := a; …` (the arguments lifted past the earlier lets). -/
private def toLets : ETerm → List ETerm → Nat → ETerm
  | lam x b, a :: as, k => letE x (a.lift k) (toLets b as (k + 1))
  | b, as, k => apps b (as.map (·.lift k))

/-- Inline the definitions `body?` knows (their erased code, closed), and simplify. -/
partial def inlineSimp (body? : Name → Option ETerm) (fuel : Nat := 8) : ETerm → ETerm
  | t@(app ..) =>
    let (h, args) := spine t []
    let args := args.map (inlineSimp body? fuel)
    match h with
    | global n =>
      match body? n, fuel with
      | some b, fuel' + 1 =>
        if args.length ≥ lamArity b then inlineSimp body? fuel' (toLets b args 0)
        else apps h args
      | _, _ => apps h args
    | lam .. => inlineSimp body? fuel (toLets h args 0)
    | h => apps (inlineSimp body? fuel h) args
  | letE x v b =>
    let v := inlineSimp body? fuel v
    let substitutable := match v with
      | var _ | erased => true
      | lam .. => uses 0 b == (1, false)
      | _ => false
    if substitutable then inlineSimp body? fuel (subst 0 v b)
    else letE x v (inlineSimp body? fuel b)
  | lam x b => lam x (inlineSimp body? fuel b)
  | fix x b => fix x (inlineSimp body? fuel b)
  | obj t fs => obj t (fs.map (inlineSimp body? fuel))
  | proj i t => proj i (inlineSimp body? fuel t)
  | case s bs => case (inlineSimp body? fuel s) (bs.map (inlineSimp body? fuel))
  | prim op as => prim op (as.map (inlineSimp body? fuel))
  | t => t

end ETerm

end Wiz
