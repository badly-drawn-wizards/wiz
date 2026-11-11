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

/-!
## Case-shaped functions (stage 15h)

Application is call by value: `Bool.and a b` computed `b` before looking at `a`, so
`p x && all p xs` walked the whole list after the answer was known (and the recursive
call was not a tail call). A **case-shaped** definition is one whose erased body is

    λ x₁ … xₙ. case s [b₀, …, bₖ]

where `s` and the branches are *cheap*: built from the parameters, constants, objects,
projections and tags only (no application, no binder), and small. `Bool.and`, `Bool.or`,
`Bool.not`, `Option.getD`, `cond`-like functions have this shape. A call with all `n`
arguments is compiled as the `case` itself:

* an argument whose parameter the scrutinee uses, or that every branch uses (or more
  than one), is computed first (`let`), as before;
* an argument whose parameter is used in one branch only is computed in that branch;
* an argument whose parameter is not used is not computed at all.

This changes when (and whether) an argument is evaluated, never what the call returns:
the language is pure, so the only observable difference is for an argument that
does not return (a `partial` definition that loops, an absurd case): the call now returns
when the branch taken does not use it, as it does in the kernel's evaluator. An argument
of type `IO A` is a value (a function of the world): building it or not performs nothing.
-/

/-- The parts of a case-shaped definition: parameter names, scrutinee and branches (with
the parameters as the only variables, `var 0` the last). -/
structure CaseShape where
  params : Array Name
  scrut : ETerm
  branches : Array ETerm
  deriving Inhabited

/-- The size of a cheap term (no application, no binder), if it is one. -/
partial def cheapSize? : ETerm → Option Nat
  | var _ | erased | natLit _ | global _ => some 1
  | obj _ fs => fs.foldlM (fun n f => (n + ·) <$> cheapSize? f) 1
  | proj _ t => (· + 1) <$> cheapSize? t
  | prim op as =>
    if op matches .tag | .natTag | .natPred | .natSucc then
      as.foldlM (fun n f => (n + ·) <$> cheapSize? f) 1
    else none
  | _ => none

/-- Copying it costs nothing, and evaluating it does nothing. -/
private def atomic : ETerm → Bool
  | var _ | erased | natLit _ | global _ => true
  | _ => false

/-- A projection (of a projection…) of a variable. -/
private def isPath : ETerm → Bool
  | var _ => true
  | proj _ t => isPath t
  | _ => false

/-- Substitute away the `let`s of atomic values and of fields (a compiled `match` binds
its payload, its fields and its arguments this way). -/
private partial def substAtomLets : ETerm → ETerm
  | letE x v b =>
    let v := substAtomLets v
    if atomic v || isPath v then substAtomLets (subst 0 v b) else letE x v (substAtomLets b)
  | obj t fs => obj t (fs.map substAtomLets)
  | proj i t => proj i (substAtomLets t)
  | case s bs => case (substAtomLets s) (bs.map substAtomLets)
  | prim op as => prim op (as.map substAtomLets)
  | t => t

/-- Is this erased definition case-shaped? -/
def caseShape? (e : ETerm) (maxSize : Nat := 16) : Option CaseShape :=
  let rec peel : ETerm → Array Name → Array Name × ETerm
    | lam x b, xs => peel b (xs.push x)
    | t, xs => (xs, t)
  let (params, body) := peel e #[]
  match params, substAtomLets body with
  | params, case s bs =>
    if params.isEmpty then none else
    match cheapSize? s, bs.foldlM (fun n b => (n + ·) <$> cheapSize? b) 0 with
    | some _, some n =>
      -- the scrutinee tests a parameter (else there is nothing to learn at a call)
      if n ≤ maxSize && (List.range params.size).any (fun i => (uses i s).1 > 0) then
        some { params, scrut := s, branches := bs }
      else none
    | _, _ => none
  | _, _ => none

/-- A cheap term with its variables replaced (`σ[i]` for `var i`). -/
private partial def inst (σ : Array ETerm) : ETerm → ETerm
  | var i => σ[i]?.getD erased
  | obj t fs => obj t (fs.map (inst σ))
  | proj i t => proj i (inst σ t)
  | prim op as => prim op (as.map (inst σ))
  | t => t

/-- The call `f args` of a case-shaped `f` (exactly `params.size` arguments, in the
caller's scope) as a `case` (see above). -/
def CaseShape.call (c : CaseShape) (args : Array ETerm) : ETerm :=
  let n := c.params.size
  -- parameter `j` (in order) is `var (n - 1 - j)`
  let usedIn (j : Nat) (t : ETerm) : Bool := (uses (n - 1 - j) t).1 > 0
  let branchesUsing (j : Nat) : List Nat := (List.range c.branches.size).filter fun k => usedIn j c.branches[k]!
  let isStrict (j : Nat) : Bool := usedIn j c.scrut || (branchesUsing j).length ≥ 2 ||
    (c.branches.size == 1 && usedIn j c.branches[0]!)
  let needsLet (j : Nat) : Bool := !atomic args[j]!
  -- the arguments computed first, in order
  let strict := (List.range n).filter fun j => isStrict j && needsLet j
  let m := strict.length
  -- `σ` under `d` more binders than the caller's scope, with `local j` for the `let`s
  let mkσ (d : Nat) (bound : Nat → Option Nat) : Array ETerm :=
    -- (indexed by variable: `var i` is parameter `n - 1 - i`)
    (Array.range n).map fun i =>
      let j := n - 1 - i
      match bound j with
      | some v => var v
      | none => if atomic args[j]! then args[j]!.lift d else erased
  let branch (k : Nat) : ETerm :=
    let lazy := (List.range n).filter fun j => !isStrict j && needsLet j && branchesUsing j == [k]
    let r := lazy.length
    let σ := mkσ (m + r) fun j =>
      match lazy.idxOf? j with
      | some u => some (r - 1 - u)
      | none => (strict.idxOf? j).map fun t => m - 1 - t + r
    let rec inner : List Nat → Nat → ETerm
      | [], _ => inst σ c.branches[k]!
      | j :: js, u => letE c.params[j]! (args[j]!.lift (m + u)) (inner js (u + 1))
    inner lazy 0
  let σ0 := mkσ m fun j => (strict.idxOf? j).map fun t => m - 1 - t
  let rec lets : List Nat → Nat → ETerm
    | [], _ => case (inst σ0 c.scrut) ((Array.range c.branches.size).map branch)
    | j :: js, t => letE c.params[j]! (args[j]!.lift t) (lets js (t + 1))
  lets strict 0

/-- Compile the calls of case-shaped definitions (`shape?`) with all their arguments as
`case`s. -/
partial def caseInline (shape? : Name → Option CaseShape) : ETerm → ETerm
  | t@(app ..) =>
    let (h, args) := spine t []
    let args := args.map (caseInline shape?)
    match h with
    | global f =>
      match shape? f with
      | some c =>
        let n := c.params.size
        if args.length ≥ n then apps (c.call (args.take n).toArray) (args.drop n)
        else apps h args
      | none => apps h args
    | h => apps (caseInline shape? h) args
  | letE x v b => letE x (caseInline shape? v) (caseInline shape? b)
  | lam x b => lam x (caseInline shape? b)
  | fix x b => fix x (caseInline shape? b)
  | obj t fs => obj t (fs.map (caseInline shape?))
  | proj i t => proj i (caseInline shape? t)
  | case s bs => case (caseInline shape? s) (bs.map (caseInline shape?))
  | prim op as => prim op (as.map (caseInline shape?))
  | t => t

end ETerm


end Wiz
