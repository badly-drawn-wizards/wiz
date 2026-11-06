import Wiz.Elab.Zonk

/-!
# Elaborating terms

Bidirectional, like the kernel, but on `Syntax` and with metavariables:

    check ctx stx A : ElabM (Term R)          -- elaborate stx against type A
    infer ctx stx   : ElabM (Term R × VTy R)  -- elaborate stx and compute its type

## Implicit arguments

Two mechanisms, following elaboration-zoo `04-implicit-args`:

* **Insertion of implicit applications.** (When the implicit argument is a type, its
  universe is recorded with `addSortConstraint`.) When a term of type `{A : Type} → A → A` is
  used where something that isn't an implicit function is expected, `?A` is inserted:
  `id` becomes `id ?A`. This happens before each explicit argument and in `check`'s
  fallback case. `@f` turns it off.
* **Insertion of implicit lambdas.** Checking a term against `{A : Type} → B`, unless
  the term is itself a `fun {A} => …`, elaborates it under an extra implicit binder.
  So `fun x => x` checks against `{A : Type} → A → A`.

## The node kinds handled here

See `Wiz.Parser.Builtin` for their children. Anything else is reported as
"no elaborator for syntax kind ...". Stage 6 makes that table extensible.
-/

namespace Wiz.Elab

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

/-! ## Reading binders -/

/-- One binder name with everything that applies to it. -/
structure BinderView where
  name : Name
  info : SourceInfo
  bi : BinderInfo
  qty : Option Syntax
  type : Option Syntax

private def binderName (s : Syntax) : Name :=
  match s with
  | .ident _ n => n
  | _ => "_"

/-- Expand a binder (`x`, `_`, `(1 x y : A)`, `{A}`, ...) into one view per name. -/
def binderViews (stx : Syntax) : Array BinderView :=
  match stx.kind with
  | "binder.explicit" | "binder.implicit" =>
    let bi := if stx.isOfKind "binder.implicit" then .implicit else .default
    let qty := (stx.getArg 1).args[0]?
    let type := (stx.getArg 3).args[1]?
    (stx.getArg 2).args.map fun n => { name := binderName n, info := n.info, bi, qty, type }
  | _ => #[{ name := binderName stx, info := stx.info, bi := .default, qty := none, type := none }]

def elabQuantity (ctx : LocalCtx R) (bi : BinderInfo) : Option Syntax → ElabM R R
  | none => pure (if bi == .implicit then QuantitySyntax.implicitDefault else QuantitySyntax.explicitDefault)
  | some q =>
    let lit := match q.getArg 0 with
      | .atom _ v => v
      | n => (n.getNat?.map toString).getD "?"
    match QuantitySyntax.ofLiteral lit with
    | some r => pure r
    | none => throwAt (ctx.withInfo q).info s!"'{lit}' is not a quantity of this rig"

/-- **Exercise 4.2.** Elaborate a universe level (see `Builtin.levelLeading` for the
node kinds). A `level.param` must be one of the declaration's universe parameters
(`(← get).levelParams`); `_` is a fresh level metavariable. -/
partial def elabLevel (stx : Syntax) : ElabM R Level := do
  sorry

/-- Look a name up in the local context, innermost first. -/
def lookupLocal (ctx : LocalCtx R) (x : Name) : Option (Nat × VTy R) := Id.run do
  for n in ctx.names, ty in ctx.types, i in [0:ctx.lvl] do
    if n == x && x != "_" then return some (i, ty)
  none

/-- **Exercise 4.9.** Field access by name: `t.f₁.f₂…`. Starting from `t : ty`, for
each field name walk the Σ telescope of the (forced) type: if the current Σ's binder
name is the field, project with `fst`; otherwise move on with `snd`, instantiating the
second component's type with the first projection. Throw if the field isn't found.
Returns the projected term and its type. -/
partial def elabFields (ctx : LocalCtx R) (t : Term R) (ty : VTy R) (fields : List Name) :
    ElabM R (Term R × VTy R) := do
  sorry

/-- **Exercise 3.7.** Insert implicit applications: while the type forces to an
*implicit* Π, apply the term to a fresh metavariable and instantiate the codomain with
the metavariable's value. -/
partial def insertImplicits (ctx : LocalCtx R) (t : Term R) (ty : VTy R) :
    ElabM R (Term R × VTy R) := do
  sorry

/-- Unify, turning a failure into a readable type mismatch at `stx`.

Unification is untyped, so it misses the η-rule for `Unit` (`P x =?= P ()` with
`x : Unit`). When it fails, we ask the kernel's type-directed `convTy`, which treats
unsolved metas as rigid, before giving up. -/
def unifyAt (ctx : LocalCtx R) (stx : Syntax) (expected inferred : VTy R) : ElabM R Unit :=
  fun s => match unify ctx.lvl expected inferred s with
    | .ok r => .ok r
    | .error e =>
      if convTy s.globals ctx.types.reverse.toArray expected inferred then .ok ((), s) else
      let show' (v : VTy R) := (quote s.globals ctx.lvl v).pretty ctx.names
      .error { info := (ctx.withInfo stx).info,
               msg := s!"type mismatch\n  expected: {show' expected}\n  inferred: {show' inferred}\n  ({e.msg})" }

/-- Is this a `fun` whose first binder is implicit? -/
private def isImplicitFun (stx : Syntax) : Bool :=
  stx.isOfKind "term.fun" &&
    match (stx.getArg 1).args[0]? with
    | some b => b.isOfKind "binder.implicit"
    | none => false

mutual

/-- Elaborate a type, returning it and its universe level (possibly a level
metavariable). -/
partial def checkType (ctx : LocalCtx R) (stx : Syntax) : ElabM R (Term R × Level) := do
  if stx.isOfKind "term.hole" then
    let m ← freshMeta (ctx.withInfo stx) "type"
    let u ← freshLevelMeta
    addSortConstraint ctx m u
    return (m, u)
  let (t, ty) ← infer ctx stx
  match ← force ty with
  | .sort l => pure (t, l)
  | ty@(.neutral (.mvar _) _) =>
    let u ← freshLevelMeta
    unifyAt ctx stx (.sort u) ty
    pure (t, u)
  | ty => throwAt (ctx.withInfo stx).info s!"type expected, got a term of type {← showVal ctx ty}"

/-- **Exercise 3.8.** Elaborate `stx` against `expected`. Force `expected` first.

1. If `expected` is an implicit Π and `stx` is not an implicit `fun`
   (`isImplicitFun`), insert an implicit lambda: elaborate `stx` against the codomain
   in a context extended with the Π's variable, and wrap the result in `.lam`.
2. `term.fun`: the given `checkFun` does the work.
3. `term.let`: `elabLet` with the expected type.
4. `term.hole` / `term.syntheticHole`: a fresh meta. Use the hole's name for
   `?x` as its description.
5. `term.paren`: check the inner term.
6. Otherwise infer, insert implicits (unless `stx` is `term.explicit`), and
   `unifyAt` the expected and inferred types. -/
partial def check (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) : ElabM R (Term R) := do
  let ctx := ctx.withInfo stx
  sorry

/-- Check `fun b₁ … bₙ => body` against `expected`, one binder at a time.

* If `expected` is a Π with the same binder info as `b₁`: the binder's type (if
  given) must unify with the domain, and its quantity (if given) must equal the Π's.
* If `expected` is an implicit Π and `b₁` is explicit: insert an implicit lambda.
* Otherwise, fall back to inferring the whole `fun` and unifying. -/
partial def checkFun (ctx : LocalCtx R) (bs : List BinderView) (body : Syntax) (expected : VTy R) :
    ElabM R (Term R) := do
  match bs with
  | [] => check ctx body expected
  | b :: rest =>
    match ← force expected with
    | .pi x bi q dom cod =>
      if bi == b.bi then
        if let some tyStx := b.type then
          let (ty, _) ← checkType ctx tyStx
          unifyAt ctx tyStx dom (← evalIn ctx ty)
        if b.qty.isSome then
          let q' ← elabQuantity ctx b.bi b.qty
          unless q == q' do
            throwAt b.info s!"binder quantity {QuantitySyntax.display q'} does not match the expected {QuantitySyntax.display q}"
        let t ← checkFun (ctx.bind b.name dom) rest body (← instM cod (Val.var ctx.lvl))
        return .lam b.name t
      else if bi == .implicit then
        let t ← checkFun (ctx.bind x dom) bs body (← instM cod (Val.var ctx.lvl))
        return .lam x t
      else throwAt b.info "unexpected implicit binder: the expected type takes an explicit argument"
    | expected =>
      let (t, ty) ← inferFun ctx bs body
      unifyAt ctx body expected ty
      pure t

/-- Check `(a, b, c)` against a (right-nested) Σ. -/
partial def checkTuple (ctx : LocalCtx R) (items : List Syntax) (expected : VTy R) :
    ElabM R (Term R) := do
  match items with
  | [] => throwAt ctx.info "empty tuple"
  | [t] => check ctx t expected
  | t :: rest =>
    match ← force expected with
    | .sigma _ _ A B =>
      let a ← check ctx t A
      let b ← checkTuple ctx rest (← instM B (← evalIn ctx a))
      pure (.pair a b)
    | expected =>
      let (tm, ty) ← inferTuple ctx items
      unifyAt ctx t expected ty
      pure tm

/-- Infer a tuple's type as a non-dependent Σ. -/
partial def inferTuple (ctx : LocalCtx R) (items : List Syntax) : ElabM R (Term R × VTy R) := do
  match items with
  | [] => throwAt ctx.info "empty tuple"
  | [t] => infer ctx t
  | t :: rest =>
    let (a, aty) ← infer ctx t
    let (b, bty) ← inferTuple ctx rest
    let g ← getGlobals
    -- the second component's type, weakened under the Σ binder
    let bTerm := quote g (ctx.lvl + 1) bty
    return (.pair a b, .sigma "_" QuantitySyntax.explicitDefault aty (.mk (Val.var ctx.lvl :: ctx.env) bTerm))

/-- `let q (x, y) := s; body`, check mode only (the motive is the expected type). -/
partial def elabLetPair (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) : ElabM R (Term R) := do
  let q ← elabQuantity ctx .default (stx.getArg 1).args[0]?
  let x := ((stx.getArg 3).getId?).getD "_"
  let y := ((stx.getArg 5).getId?).getD "_"
  let (s, sty) ← infer ctx (stx.getArg 8)
  match ← force sty with
  | .sigma _ _ A B =>
    let g ← getGlobals
    let motive := quote g (ctx.lvl + 1) expected
    let ctx₂ := (ctx.bind x A).bind y (← instM B (Val.var ctx.lvl))
    let body ← check ctx₂ (stx.getArg 10) expected
    pure (.split q s "z" motive x y body)
  | sty => throwAt (ctx.withInfo (stx.getArg 8)).info s!"let (x, y) := ... expects a pair, got {← showVal ctx sty}"

/-- `fun` in inference mode: untyped binders get a metavariable as their type. -/
partial def inferFun (ctx : LocalCtx R) (bs : List BinderView) (body : Syntax) :
    ElabM R (Term R × VTy R) := do
  match bs with
  | [] => infer ctx body
  | b :: rest =>
    let ty ← match b.type with
      | some s => pure (← checkType ctx s).1
      | none => freshMeta ctx s!"the type of {b.name}"
    let q ← elabQuantity ctx b.bi b.qty
    let vty ← evalIn ctx ty
    let ctx' := ctx.bind b.name vty
    let (t, bty) ← inferFun ctx' rest body
    let g ← getGlobals
    return (.lam b.name t, .pi b.name b.bi q vty (.mk ctx.env (quote g ctx'.lvl bty)))

/-- `let` in either mode. -/
partial def elabLet (ctx : LocalCtx R) (stx : Syntax) (expected : Option (VTy R)) :
    ElabM R (Term R × VTy R) := do
  let x := ((stx.getArg 2).getId?).getD "_"
  let q ← elabQuantity ctx .default (stx.getArg 1).args[0]?
  let (ty, val) ← match (stx.getArg 3).args[1]? with
    | some tyStx =>
      let (ty, _) ← checkType ctx tyStx
      pure (ty, ← check ctx (stx.getArg 5) (← evalIn ctx ty))
    | none =>
      let (val, vty) ← infer ctx (stx.getArg 5)
      pure (quote (← getGlobals) ctx.lvl vty, val)
  let ctx' := ctx.define x (← evalIn ctx ty) (← evalIn ctx val)
  let body := stx.getArg 7
  match expected with
  | some e => return (.letE x q ty val (← check ctx' body e), e)
  | none =>
    let (b, bty) ← infer ctx' body
    return (.letE x q ty val b, bty)

/-- A Π telescope `b₁ → … → bₙ → body` (used by `depArrow` and `∀`). -/
partial def elabPis (ctx : LocalCtx R) (bs : List BinderView) (body : Syntax) :
    ElabM R (Term R × Level) := do
  match bs with
  | [] => checkType ctx body
  | b :: rest =>
    let (ty, l₁) ← match b.type with
      | some s => checkType ctx s
      | none => pure (← freshMeta ctx s!"the type of {b.name}", ← freshLevelMeta)
    let q ← elabQuantity ctx b.bi b.qty
    let (cod, l₂) ← elabPis (ctx.bind b.name (← evalIn ctx ty)) rest body
    return (.pi b.name b.bi q ty cod, .imax l₁ l₂)

/-- `(x : A) × (y : B) × C`, like `elabPis`. -/
partial def elabSigmas (ctx : LocalCtx R) (bs : List BinderView) (body : Syntax) :
    ElabM R (Term R × VTy R) := do
  match bs with
  | [] =>
    let (t, l) ← checkType ctx body
    return (t, .sort l)
  | b :: rest =>
    let (ty, l₁) ← match b.type with
      | some s => checkType ctx s
      | none => pure (← freshMeta ctx s!"the type of {b.name}", ← freshLevelMeta)
    let q ← elabQuantity ctx b.bi b.qty
    let (cod, s) ← elabSigmas (ctx.bind b.name (← evalIn ctx ty)) rest body
    let l₂ ← match ← force s with
      | .sort l => pure l
      | _ => freshLevelMeta
    return (.sigma b.name q ty cod, .sort (.max l₁ l₂))

/-- **Exercise 3.9.** Infer the type of an application `f a₁ … aₙ` (`term.app`, with
`f` = `stx.getArg 0` and the arguments in `(stx.getArg 1).args`).

Infer `f`. Then for each argument: unless `f` was written `@f`, insert implicits; force
the function type; if it is a Π, check the argument against the domain and instantiate
the codomain with the argument's value. If the function type is an unsolved meta,
unify it with a fresh Π `(x : ?A) → ?B x` first. Anything else is "not a function".

With `@f`, each argument fills the next Π whether implicit or explicit. -/
partial def inferApp (ctx : LocalCtx R) (stx : Syntax) : ElabM R (Term R × VTy R) := do
  sorry

/-- Infer the type of `stx`. -/
partial def infer (ctx : LocalCtx R) (stx : Syntax) : ElabM R (Term R × VTy R) := do
  let ctx := ctx.withInfo stx
  match stx.kind with
  | "term.ident" | "term.explicit" | "term.identUniv" =>
    let x := (stx.getArg (if stx.isOfKind "term.explicit" then 1 else 0)).getId?.getD "_"
    let explicitLevels : Option (Array Syntax) := if stx.isOfKind "term.identUniv" then
        some ((stx.getArg 2).args.filter (!· matches .atom ..)) else none
    if explicitLevels.isNone then
      if let some (ix, ty) := lookupLocal ctx x then return (.var ix, ty)
    match (← getGlobals).find? x with
    | some d =>
      let us ← match explicitLevels with
        | some ls =>
          unless ls.size == d.levelParams.length do
            throwAt ctx.info s!"{x} has {d.levelParams.length} universe parameters, {ls.size} given"
          ls.toList.mapM elabLevel
        | none => d.levelParams.mapM fun _ => freshLevelMeta
      return (.const x us, ← evalIn {} (d.type.instLevels d.levelParams us))
    | none =>
      -- built-in types
      let builtinLevel : Option Level := match explicitLevels with
        | some _ => none
        | none => some (if x == "True" || x == "False" then 0 else 1)
      match x, explicitLevels with
      | "Unit", some #[l] | "Empty", some #[l] =>
        let l ← elabLevel l
        return (if x == "Unit" then .unit l else .empty l, .sort l)
      | "Unit", none | "True", none => return (.unit builtinLevel.get!, .sort builtinLevel.get!)
      | "Empty", none | "False", none => return (.empty builtinLevel.get!, .sort builtinLevel.get!)
      | _, _ =>
      -- field access: `p.x.y`
      match x.splitOn "." with
      | base :: f :: fs =>
        let (t, ty) ← infer ctx (.node stx.info "term.ident" #[.ident stx.info base])
        elabFields ctx t ty (f :: fs)
      | _ => throwAt ctx.info s!"unknown identifier '{x}'"
  | "term.type" | "term.sort" =>
    let l ← match (stx.getArg 1).args[0]? with
      | some ls => elabLevel ls
      | none => pure .zero
    let l := if stx.isOfKind "term.type" then .succ l else l
    return (.sort l, .sort (.succ l))
  | "term.prop" => return (.sort .zero, .sort (.succ .zero))
  | "term.paren" => infer ctx (stx.getArg 1)
  | "term.ascription" =>
    let (ty, _) ← checkType ctx (stx.getArg 3)
    let vty ← evalIn ctx ty
    let t ← check ctx (stx.getArg 1) vty
    return (.ann t ty, vty)
  | "term.hole" | "term.syntheticHole" =>
    let a ← freshMeta ctx "the type of a hole"
    let desc := if stx.isOfKind "term.hole" then "_" else s!"?{((stx.getArg 1).getId?).getD "_"}"
    return (← freshMeta ctx desc, ← evalIn ctx a)
  | "term.app" => inferApp ctx stx
  | "term.fun" => inferFun ctx ((stx.getArg 1).args.flatMap binderViews).toList (stx.getArg 3)
  | "term.let" => elabLet ctx stx none
  | "term.arrow" =>
    let (a, l₁) ← checkType ctx (stx.getArg 0)
    let (b, l₂) ← checkType (ctx.bind "_" (← evalIn ctx a)) (stx.getArg 2)
    return (.pi "_" .default QuantitySyntax.explicitDefault a b, .sort (.imax l₁ l₂))
  | "term.depArrow" =>
    let (t, l) ← elabPis ctx (binderViews (stx.getArg 0)).toList (stx.getArg 2)
    return (t, .sort l)
  | "term.forall" =>
    let (t, l) ← elabPis ctx ((stx.getArg 1).args.flatMap binderViews).toList (stx.getArg 3)
    return (t, .sort l)
  | "term.depSigma" =>
    let bs := (binderViews (stx.getArg 0)).toList
    elabSigmas ctx bs (stx.getArg 2)
  | "term.prod" =>
    let (a, l₁) ← checkType ctx (stx.getArg 0)
    let (b, l₂) ← checkType (ctx.bind "_" (← evalIn ctx a)) (stx.getArg 2)
    return (.sigma "_" QuantitySyntax.explicitDefault a b, .sort (.max l₁ l₂))
  | "term.tuple" =>
    inferTuple ctx (#[stx.getArg 1] ++ ((stx.getArg 3).args.filter (!· matches .atom ..))).toList
  | "term.unitVal" => return (.tt, .unit 1)
  | "term.proj" =>
    let (t, ty) ← infer ctx (stx.getArg 0)
    match ← force ty, (stx.getArg 2).getNat? with
    | .sigma _ _ A _, some 1 => return (.fst t, A)
    | .sigma _ _ _ B, some 2 => return (.snd t, ← instM B (vFst (← evalIn ctx t)))
    | ty, _ => throwAt ctx.info s!"cannot project from a value of type {← showVal ctx ty}"
  | "term.eq" =>
    let (a, A) ← infer ctx (stx.getArg 0)
    let b ← check ctx (stx.getArg 2) A
    return (.eq (quote (← getGlobals) ctx.lvl A) a b, .sort 0)
  | "term.refl" =>
    let (a, A) ← infer ctx (stx.getArg 1)
    let g ← getGlobals
    let va ← evalIn ctx a
    match ← force A with
    | .sort _ => return (.reflTy a, vEqType g va va)
    | A => return (.refl (quote g ctx.lvl A) a, vEq g A va va)
  | "term.transp" =>
    let (e, ety) ← infer ctx (stx.getArg 3)
    let g ← getGlobals
    match ← force ety with
    | .neutral (.eq A a b) #[] =>
      let motiveTy : Val R := .pi "b" .default 0 A
        (.mk [a, A] (.pi "_" .default 0 (.eq (.var 2) (.var 1) (.var 0)) (.sort 0)))
      let P ← check ctx (stx.getArg 1) motiveTy
      let vP ← evalIn ctx P
      let p ← check ctx (stx.getArg 2) (vApp g (vApp g vP a) (.neutral (.refl A a) #[]))
      let q := quote g ctx.lvl
      return (.transp (q A) (q a) P p (q b) e, vApp g (vApp g vP b) (← evalIn ctx e))
    | ety => throwAt ctx.info s!"transp: expected a proof of an equation, got {← showVal ctx ety}"
  | "term.cast" =>
    let (e, ety) ← infer ctx (stx.getArg 1)
    match ← force ety with
    | .neutral (.eqTy X Y) #[] =>
      let t ← check ctx (stx.getArg 2) X
      let g ← getGlobals
      return (.cast (quote g ctx.lvl X) (quote g ctx.lvl Y) e t, Y)
    | _ => throwAt ctx.info "cannot infer the type of this cast; add a type ascription"
  | "term.letPair" | "term.absurd" | "term.rfl" =>
    throwAt ctx.info "cannot infer the type of this expression; add a type ascription"
  | "term.num" | "term.str" => throwAt ctx.info "literals need data types (stage 4)"
  | k => throwAt ctx.info s!"no elaborator for syntax kind {k}"

end

end Wiz.Elab
