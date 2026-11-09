import Wiz.Elab.Zonk
import Wiz.Elab.Macro
import Wiz.Elab.Tactic
import Wiz.Elab.Class

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
  | "binder.inst" =>
    let name := (((stx.getArg 1).args[0]?).bind Syntax.getId?).getD "inst✝"
    #[{ name, info := stx.info, bi := .instImplicit, qty := none, type := some (stx.getArg 2) }]
  | _ => #[{ name := binderName stx, info := stx.info, bi := .default, qty := none, type := none }]

/-- A quantity literal (`0`, `1`, `ω`, …) as a term. -/
def elabQtyLit (ctx : LocalCtx R) (stx : Syntax) (lit : String) : ElabM R (Term R) :=
  match QuantitySyntax.ofLiteral lit with
  | some r => pure (.qlit r)
  | none => throwAt (ctx.withInfo stx).info s!"'{lit}' is not a quantity of this rig"

def defaultQty (bi : BinderInfo) : Term R :=
  .qlit (if bi == .implicit then QuantitySyntax.implicitDefault else QuantitySyntax.explicitDefault)

/-- **Exercise 4.2.** Elaborate a universe level (see `Builtin.levelLeading` for the
node kinds). A `level.param` must be one of the declaration's universe parameters
(`(← get).levelParams`); `_` is a fresh level metavariable. -/
partial def elabLevel (stx : Syntax) : ElabM R Level := do
  --<sol
  match stx.kind with
  | "level.num" => pure (Level.ofNat ((stx.getArg 0).getNat?.getD 0))
  | "level.param" =>
    let u := ((stx.getArg 0).getId?).getD "_"
    unless (← get).levelParams.contains u do
      throwAt stx.info s!"unknown universe level '{u}'"
    pure (.param u)
  | "level.hole" => freshLevelMeta
  | "level.paren" => elabLevel (stx.getArg 1)
  | "level.max" => return .max (← elabLevel (stx.getArg 1)) (← elabLevel (stx.getArg 2))
  | "level.imax" => return .imax (← elabLevel (stx.getArg 1)) (← elabLevel (stx.getArg 2))
  | "level.add" =>
    return (← elabLevel (stx.getArg 0)).addOffset ((stx.getArg 2).getNat?.getD 0)
  | k => throwAt stx.info s!"unexpected level syntax {k}"
  --|ex
  --| sorry
  --sol>

/-- Look a name up in the local context, innermost first. -/
def lookupLocal (ctx : LocalCtx R) (x : Name) : Option (Nat × VTy R) := Id.run do
  for n in ctx.names, ty in ctx.types, i in [0:ctx.lvl] do
    if n == x && x != "_" then return some (i, ty)
  none

/-- **Exercise 3.7.** Insert implicit applications: while the type forces to an
*implicit* Π, apply the term to a fresh metavariable and instantiate the codomain with
the metavariable's value. -/
partial def insertImplicits (ctx : LocalCtx R) (t : Term R) (ty : VTy R) :
    ElabM R (Term R × VTy R) := do
  -- (given, stage 7) an instance argument: a hole for instance resolution
  if let .pi x .instImplicit _ dom cod _ ← force ty then
    let m ← freshMeta ctx s!"instance {x}"
    addInstProblem ctx m dom
    return ← insertImplicits ctx (.app t m) (← instM cod (← evalIn ctx m))
  --<sol
  match ← force ty with
  | .pi x .implicit _ dom cod _ =>
    let m ← freshMeta ctx s!"implicit argument {x}"
    if let .sort l ← force dom then addSortConstraint ctx m l
    insertImplicits ctx (.app t m) (← instM cod (← evalIn ctx m))
  | _ => pure (t, ty)  -- the type as it was (forcing would lose glued names)
  --|ex
  --| sorry
  --sol>

/-- Names the elaborator treats as data primitives when applied (and not shadowed). -/
def builtinNames : List Name :=
  ["Desc", "Desc.ret", "Desc.arg", "Desc.rec", "Desc.hrec", "Desc.elim", "Desc.interp", "Desc.All",
   "μ", "ν", "con", "ind", "out", "coit", "cocon"]

/-- `f a₁ … aₙ` where `f` is an unshadowed built-in name. -/
def builtinApp? (ctx : LocalCtx R) (stx : Syntax) : ElabM R (Option (Name × Array Syntax)) := do
  unless stx.isOfKind "term.app" do return none
  let head := stx.getArg 0
  unless head.isOfKind "term.ident" do return none
  let some n := (head.getArg 0).getId? | return none
  if (lookupLocal ctx n).isSome then return none
  let n := stripScope n
  unless builtinNames.contains n do return none
  if (lookupLocal ctx n).isSome || (← getGlobals).contains n then return none
  return some (n, (stx.getArg 1).args)

/-- The term for a string literal, `String.mk [Char.mk n, …]` with numerals `n`. The
prelude's names are fixed here. -/
def mkStringLit (str : String) (us : List Level := []) : ElabM R (Term R) := do
  let S := ((← get).builtins.lookup "string").getD "String"
  let charTy : Term R := .const "Char" []
  let chr (c : Char) : Term R := .app (.const "Char.mk" []) (.natLit c.toNat)
  let list := str.toList.foldr (fun c t => Term.app (.app (.app (.const "List.cons" []) charTy) (chr c)) t)
    (.app (.const "List.nil" []) charTy)
  pure (.app (.const (S ++ ".mk") us) list)

/-- Expand a macro at `stx`, with a fresh scope. -/
def expand? (stx : Syntax) : ElabM R (Option Syntax) := do
  let s ← get
  let rules := s.macros.map fun (kind, pattern, template, vars) => ({ kind, pattern, template, vars } : MacroRule)
  match expandMacro? rules stx s.nextScope with
  | some stx' => modify (fun s => { s with nextScope := s.nextScope + 1 }); pure (some stx')
  | none =>
    let some f := s.procMacros.lookup stx.kind | pure none
    match s.runProcMacro f stx s.nextScope with
    | .ok (stx', next) => modify (fun s => { s with nextScope := next }); pure (some stx')
    | .error e => throwAt stx.info e

/-- Unify, turning a failure into a readable type mismatch at `stx`.

Unification is untyped, so it misses the η-rule for `Unit` (`P x =?= P ()` with
`x : Unit`). When it fails, we ask the kernel's type-directed `convTy`, which treats
unsolved metas as rigid, before giving up. -/
def unifyAt (ctx : LocalCtx R) (stx : Syntax) (expected inferred : VTy R) : ElabM R Unit :=
  fun s => match unify ctx.lvl expected inferred s with
    | .ok r => .ok r
    | .error e =>
      if subTy s.globals ctx.types.reverse.toArray inferred expected then .ok ((), s) else
      let show' (v : VTy R) := (quote s.globals ctx.lvl v).pretty ctx.names
      .error { info := (ctx.withInfo stx).info,
               msg := s!"type mismatch\n  expected: {show' expected}\n  inferred: {show' inferred}\n  ({e.msg})" }

/-- Is this a `fun` whose first binder is implicit? -/
private def isImplicitFun (stx : Syntax) : Bool :=
  stx.isOfKind "term.fun" &&
    match (stx.getArg 1).args[0]? with
    | some b => b.isOfKind "binder.implicit"
    | none => false

/-- **Exercise 4.9.** Field access by name: `t.f₁.f₂…`. Starting from `t : ty`, for
each field name walk the Σ telescope of the (forced) type: if the current Σ's binder
name is the field, project with `fst`; otherwise move on with `snd`, instantiating the
second component's type with the first projection. Throw if the field isn't found.
Returns the projected term and its type. -/
partial def elabFields (ctx : LocalCtx R) (t : Term R) (ty : VTy R) (fields : List Name) :
    ElabM R (Term R × VTy R) := do
  --<sol
  match fields with
  | [] => pure (t, ty)
  | f :: rest =>
    -- generalised field notation: `t.f` is `T.f t` for a nominal type `T`
    let hint? : Option (Name × List Level × List (Val R)) := match ← force ty with
      | .mu _ _ _ _ _ h | .nu _ _ _ _ _ h => h
      | _ => none
    if let some (T, us, args) := hint? then
      if let some d := (← getGlobals).find? (T ++ "." ++ f) then
        -- `T.f : {…} → T … → F`: insert the implicits as metavariables, then unify
        let fty : VTy R := eval (← getGlobals) [] (d.type.instLevels d.levelParams us)
        let (tm, fty) ← insertImplicits ctx (.const (T ++ "." ++ f) us) fty
        let .pi _ _ _ dom cod _ ← force fty | throwAt ctx.info s!"{T}.{f} is not a function of {T}"
        unifyAt ctx (.missing) dom ty
        let tm' := Term.app tm t
        return ← elabFields ctx tm' (← instM cod (← evalIn ctx t)) rest
    let rec walk (t : Term R) (ty : VTy R) : ElabM R (Term R × VTy R) := do
      match ← force ty with
      | .sigma x _ A B _ =>
        if x == f then pure (.fst t, A)
        else walk (.snd t) (← instM B (vFst (← evalIn ctx t)))
      | ty => throwAt ctx.info s!"no field '{f}' in a value of type {← showVal ctx ty}"
    let (t, ty) ← walk t ty
    elabFields ctx t ty rest
  --|ex
  --| sorry
  --sol>

/-! ## Pattern matching (stage 4e)

`match` and equation-style definitions compile to a **case tree** over local
variables, built from the generated `T.casesOn` (and `T.rec` for structural recursion).
Splitting a variable `x : T Δ ξ`:

* the variables matched *after* `x` are reverted into the motive and re-introduced in
  every branch, so their types can mention `x`;
* if the indices `ξ` are distinct variables, the motive generalises them, and each
  branch sees them replaced by the constructor's indices (Cockx's *solution* rule);
* otherwise the motive takes an equation `idx_c = ξ`. Observational equality
  *computes* it: for an impossible constructor it contains `False`, and the branch is
  closed with `absurd` (so impossible cases can be left out). Injectivity and
  conflict therefore need no code of their own.

Structural recursion: in `def f : … | pats => rhs` where the right-hand sides call
`f`, the first column is split with `T.rec`, and a call `f y a…` on a recursive field
`y` becomes the induction hypothesis for `y` applied to `a…` (the other arguments are
generalised by the motive, so they may change in recursive calls). -/

/-- A clause of a case tree: one pattern per remaining variable, the right-hand side,
and the pattern variables bound so far (name, type, value). -/
structure MClause (R : Type) where
  pats : List Syntax
  rhs : Syntax
  binds : List (Name × VTy R × Val R) := []

inductive PatView where
  | var (n : Name)
  | wild
  /-- a constructor pattern: optional type name (from `T.c`), constructor, arguments -/
  | ctor (T : Option Name) (c : Name) (args : List Syntax)
  /-- a pair pattern `(a, b)` (`(a, b, c)` is `(a, (b, c))`) -/
  | tuple (a b : Syntax)
  deriving Inhabited

def holeStx : Syntax := .node {} "term.hole" #[.atom {} "_"]

/-- Recursion context: the function's name, and which field levels have hypotheses.
A recursive call `f p… a…` passes the explicit parameters (`params`, the binders before
the colon) unchanged, and recurses on its argument number `pos` (after the parameters);
its other arguments go to the hypothesis. -/
structure RecCtx where
  fn : Name
  ihs : List (Lvl × Lvl) := []
  params : List Name := []
  pos : Nat := 0
  /-- the number of matched arguments: a call with no more arguments than that leaves
  the parameters out (they are fixed anyway) -/
  cols : Nat := 0

partial def patView (g : Globals R) (stx : Syntax) : Except String PatView :=
  let ctorOf (n : Name) : Option (Name × Name) :=
    match n.splitOn "." with
    | [T, c] => if g.contains (T ++ ".desc") && g.contains n then some (T, c) else none
    | _ => none
  match stx.kind with
  | "term.paren" => patView g (stx.getArg 1)
  | "term.tuple" =>
    let rest := (stx.getArg 3).args.filter (!· matches .atom ..)
    match rest[0]? with
    | none => .error "invalid tuple pattern"
    | some b =>
      let b := if rest.size == 1 then b else
        .node stx.info "term.tuple" #[.atom {} "(", b, .atom {} ",", .node {} "null" (rest.extract 1 rest.size), .atom {} ")"]
      pure (.tuple (stx.getArg 1) b)
  | "term.hole" => pure .wild
  | "term.dotIdent" => pure (.ctor none ((stx.getArg 1).getId?.getD "_") [])
  | "term.ident" =>
    let n := (stx.getArg 0).getId?.getD "_"
    match ctorOf n with
    | some (T, c) => pure (.ctor (some T) c [])
    | none => pure (.var n)
  | "term.app" =>
    let h := stx.getArg 0
    let args := (stx.getArg 1).args.toList
    match h.kind with
    | "term.dotIdent" => pure (.ctor none ((h.getArg 1).getId?.getD "_") args)
    | "term.ident" => match ctorOf ((h.getArg 0).getId?.getD "_") with
      | some (T, c) => pure (.ctor (some T) c args)
      | none => .error "only constructors may be applied in patterns"
    | _ => .error "invalid pattern"
  | k => .error s!"invalid pattern ({k})"

/-- Find a component of type `False`/`Empty` inside a (Σ-nested) proof `e : ty`. -/
partial def findAbsurd (g : Globals R) (ty e : Val R) : Option (Val R) :=
  match ty with
  | .empty _ => some e
  | .sigma _ _ A B _ =>
    (findAbsurd g A (vFst e)).orElse fun _ => findAbsurd g (Closure.inst g B (vFst e)) (vSnd e)
  | _ => none

/-- The equations `a = b` (stuck, at a type `A`) inside a (Σ-nested) proof `e : ty`,
as `(proof, A, a, b)`. -/
partial def findEqs (g : Globals R) (ty e : Val R) : List (Val R × Val R × Val R × Val R) :=
  match ty with
  | .neutral (.eq A a b) #[] => [(e, A, a, b)]
  | .sigma _ _ A B _ => findEqs g A (vFst e) ++ findEqs g (Closure.inst g B (vFst e)) (vSnd e)
  | _ => []

/-- The number of leading Π binders of a type term, with their binder infos. -/
def piInfos : Term R → List (Name × BinderInfo × Term R)
  | .pi x bi _ A b _ => (x, bi, A) :: piInfos b
  | _ => []

/-- A proof of a proposition that holds by computation: `Unit`, pairs of such, and stuck
equations `a = b` (which hold by `refl` when they arise from a match on a family with a
concrete index, `SyntaxF .false`). -/
partial def trivialProof (g : Globals R) (ty : Val R) : Option (Val R) :=
  match whnf ty with
  | .unit _ => some .tt
  | .sigma _ _ A B _ => do
    let a ← trivialProof g A
    let b ← trivialProof g (Closure.inst g B a)
    pure (.pair a b)
  | .neutral (.eq A a _) _ => some (.neutral (.refl A a) #[])
  | .neutral (.eqTy X _) _ => some (.neutral (.reflTy X) #[])
  | _ => none

/-- Replace recursive calls `f y a…` (with `y` a field that has a hypothesis `h`) by
`h a…`, and `f (k e) a…` (with `k` an infinitary field) by `h e a…`. Returns the
rewritten syntax and the hypothesis bindings it needs. -/
partial def rewriteRecCalls (g : Globals R) (rc : RecCtx) (binds : List (Name × VTy R × Val R))
    (ihType : Lvl → Option (VTy R)) (lvl : Lvl) (stx : Syntax) :
    Except String (Syntax × List (Name × VTy R × Val R)) := do
  let isF (h : Syntax) := h.isOfKind "term.ident" && (h.getArg 0).getId? == some rc.fn
  if stx.isOfKind "term.app" && isF (stx.getArg 0) then
    let args := (stx.getArg 1).args
    let np := if args.size ≤ rc.cols then 0 else rc.params.length
    for p in rc.params.take np, i in [0:np] do
      let ok := match args[i]? with
        | some a => a.isOfKind "term.ident" && (a.getArg 0).getId? == some p
        | none => false
      unless ok do throw s!"recursive call of {rc.fn} must pass the parameter {p} unchanged"
    let some a := args[np + rc.pos]? | throw s!"recursive call of {rc.fn} without its structural argument"
    let rec unparen (s : Syntax) : Syntax := if s.isOfKind "term.paren" then unparen (s.getArg 1) else s
    let a := unparen a
    -- `y`, or `k e…` for an infinitary field `k`
    let (yStx, kargs) :=
      if a.isOfKind "term.app" then (a.getArg 0, (a.getArg 1).args) else (a, #[])
    let some y := (if yStx.isOfKind "term.ident" then (yStx.getArg 0).getId? else none)
      | throw s!"recursive call of {rc.fn} must be on a variable"
    let some (_, _, .neutral (.local fl) #[]) := binds.find? (·.1 == y)
      | throw s!"recursive call of {rc.fn} on {y}, which is not a recursive field"
    let some (_, ihl) := rc.ihs.find? (·.1 == fl)
      | throw s!"recursive call of {rc.fn} on {y}, which is not structurally smaller"
    let some ty := ihType ihl | throw "internal error: hypothesis without a type"
    -- a family matched at a concrete index: the hypothesis first wants the (trivial)
    -- proof that the field's index is that index
    let ihVal : Val R := .neutral (.local ihl) #[]
    let (ihVal, ty) := match whnf ty with
      | .pi _ _ q dom cod _ => match q.toPoly?, trivialProof g dom with
        | some [], some p => (vApp g ihVal p, Closure.inst g cod p)
        | _, _ =>
          -- an infinitary field: the proof comes after `h`, so the hypothesis becomes
          -- `fun h => ih h proof : (h : H) → R[e := proof]` (built at level `lvl`, the
          -- right-hand side's context, by quoting and evaluating back)
          match kargs.isEmpty, whnf ty with
          | false, .pi hn hbi hq H hcod _ =>
            match whnf (Closure.inst g hcod (Val.var lvl)) with
            | .pi _ _ q' E cod2 _ => match q'.toPoly?, trivialProof g E with
              | some [], some p =>
                let env : Env R := (List.range lvl).reverse.map Val.var
                let pTm := quote g (lvl + 1) p
                let tyTm : Term R := .pi hn hbi (quote g lvl hq) (quote g lvl H)
                  (quote g (lvl + 1) (Closure.inst g cod2 p)) none
                let valTm : Term R := .lam hn (.app (.app (.var (lvl - ihl)) (.var 0)) pTm)
                (eval g env valTm, eval g env tyTm)
              | _, _ => (ihVal, ty)
            | _ => (ihVal, ty)
          | _, _ => (ihVal, ty)
      | _ => (ihVal, ty)
    let ihName := "_ih_" ++ y
    let ident : Syntax := .node a.info "term.ident" #[.ident a.info ihName]
    let others := args.extract np (np + rc.pos) ++ args.extract (np + rc.pos + 1) args.size
    let rest ← (kargs ++ others).mapM (rewriteRecCalls g rc binds ihType lvl ·)
    let restStx := rest.map (·.1)
    let newBinds := [(ihName, ty, ihVal)] ++ rest.toList.flatMap (·.2)
    let stx' := if restStx.isEmpty then ident
      else .node stx.info "term.app" #[ident, .node {} "null" restStx]
    return (stx', newBinds)
  if isF stx then throw s!"{rc.fn} may only be used in structurally recursive calls"
  match stx with
  | .node i k as =>
    let rs ← as.mapM (rewriteRecCalls g rc binds ihType lvl ·)
    return (.node i k (rs.map (·.1)), rs.toList.flatMap (·.2))
  | s => return (s, [])

/-- `rfl` at an equation that has already computed: `succ a = succ b` at `Nat` is a Σ of
`True`s and `a = b`, an equation of functions a Π. Build the proof by the same shape
(pairs, lambdas, `()`), with `refl` at the equations left; the kernel checks them. -/
partial def rflProof (ctx : LocalCtx R) (ty : VTy R) : ElabM R (Option (Term R)) := do
  let g ← getGlobals
  match ← force ty with
  | .neutral (.eq A a _) #[] => pure (some (.refl (quote g ctx.lvl A) (quote g ctx.lvl a)))
  | .neutral (.eqTy X _) #[] => pure (some (.reflTy (quote g ctx.lvl X)))
  | .unit _ => pure (some .tt)
  | .sigma _ _ A B _ =>
    let some a ← rflProof ctx A | pure none
    let some b ← rflProof ctx (← instM B (← evalIn ctx a)) | pure none
    pure (some (.pair a b))
  | .pi x _ _ A B _ =>
    let some b ← rflProof (ctx.bind x A) (← instM B (Val.var ctx.lvl)) | pure none
    pure (some (.lam x b))
  | _ => pure none

mutual

/-- A binder's quantity: the default, a literal (`0`, `1`, `ω`), or (stage 4d)
`%t` for a term `t : Qty`, such as a quantity variable. -/
partial def elabQuantity (ctx : LocalCtx R) (bi : BinderInfo) : Option Syntax → ElabM R (Term R)
  | none => pure (defaultQty bi)
  | some q => match q.getArg 0 with
    | .atom _ "%" => check ctx (q.getArg 1) .qty
    | .atom _ v => elabQtyLit ctx q v
    | n => elabQtyLit ctx q ((n.getNat?.map toString).getD "?")

/-- Elaborate a type, returning it and its universe level (possibly a level
metavariable). -/
partial def checkType (ctx : LocalCtx R) (stx : Syntax) : ElabM R (Term R × Level) := do
  if stx.isOfKind "term.hole" then
    let m ← freshMeta (ctx.withInfo stx) "type"
    let u ← freshLevelMeta
    addSortConstraint ctx m u
    return (m, u)
  let (t, ty) ← infer ctx stx
  -- a type may still take implicit or instance arguments (`Commute e₁ e₂ m` with its
  -- `[Monad m]` …): insert them
  let (t, ty) ← if stx.isOfKind "term.explicit" then pure (t, ty) else insertImplicits ctx t ty
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
  if let some stx' ← expand? stx then return ← check ctx stx' expected
  if let some t ← checkData? ctx stx expected then return t
  -- (given, stage 7) against `[x : C A] → B`, bind the instance as a local
  if let .pi x .instImplicit _ dom cod _ ← force expected then
    return .lam x (← check (ctx.bind x dom) stx (← instM cod (Val.var ctx.lvl)))
  --<sol
  match ← force expected with
  | .pi x .implicit _ dom cod _ =>
    if !isImplicitFun stx then
      let body ← check (ctx.bind x dom) stx (← instM cod (Val.var ctx.lvl))
      return .lam x body
    checkOther ctx stx expected
  -- pass the expected type unforced: glued names help unification
  | _ => checkOther ctx stx expected
where
  checkOther (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) : ElabM R (Term R) := do
    match stx.kind with
    | "term.fun" =>
      let bs := (stx.getArg 1).args.flatMap binderViews
      checkFun ctx bs.toList (stx.getArg 3) expected
    | "term.let" => return (← elabLet ctx stx (some expected)).1
    | "term.tuple" =>
      let items := #[stx.getArg 1] ++ ((stx.getArg 3).args.filter (!· matches .atom ..))
      checkTuple ctx items.toList expected
    | "term.unitVal" =>
      match ← force expected with
      | .unit _ => pure .tt
      | _ => do let (t, ty) ← infer ctx stx; unifyAt ctx stx expected ty; pure t
    | "term.letPair" => elabLetPair ctx stx expected
    | "term.match" => elabMatch ctx stx expected
    | "term.by" => elabBy ctx stx expected
    | "term.num" =>
      match ← force expected with
      | .qty => elabQtyLit ctx stx (((stx.getArg 0).getNat?.map toString).getD "?")
      | .mu _ _ _ _ _ (some (T, us, _)) =>
        -- a numeral of the `builtin nat` type: `succ (… (succ zero))` (the kernel's Nat
        -- is unary; the runtime uses native numbers)
        let s ← get
        match s.builtins.lookup "nat" with
        | some N =>
          if N != T then throwAt ctx.info s!"numerals are for {N}, not {T}" else
          pure (.natLit ((stx.getArg 0).getNat?.getD 0))
        | none => throwAt ctx.info "numerals need `builtin nat := …`"
      | _ => do let (t, ty) ← infer ctx stx; unifyAt ctx stx expected ty; pure t
    | "term.str" =>
      match ← force expected with
      | .mu _ _ _ _ _ (some (T, us, _)) =>
        -- a string of the `builtin string` type: `String.mk [Char.mk n, …]`
        let s ← get
        match s.builtins.lookup "string" with
        | some S =>
          if S != T then throwAt ctx.info s!"string literals are for {S}, not {T}" else
          mkStringLit (((stx.getArg 0).getStr?).getD "") us
        | none => throwAt ctx.info "string literals need `builtin string := …`"
      | _ => do let (t, ty) ← infer ctx stx; unifyAt ctx stx expected ty; pure t
    | "term.rfl" =>
      let g ← getGlobals
      match ← force expected with
      | .neutral (.eq A a _) #[] => pure (.refl (quote g ctx.lvl A) (quote g ctx.lvl a))
      | .neutral (.eqTy X _) #[] => pure (.reflTy (quote g ctx.lvl X))
      | .unit _ => pure .tt
      | e => match ← rflProof ctx e with
        | some t => pure t
        | none => throwAt ctx.info s!"rfl: the expected type is not an equation (it may have computed further): {← showVal ctx e}\n  try `refl x`"
    | "term.cast" =>
      let (t, A) ← infer ctx (stx.getArg 2)
      let e ← check ctx (stx.getArg 1) (vEqType (← getGlobals) A expected)
      let g ← getGlobals
      pure (.cast (quote g ctx.lvl A) (quote g ctx.lvl expected) e t)
    | "term.absurd" =>
      let (e, ety) ← infer ctx (stx.getArg 1)
      match ← force ety with
      | .empty _ => return .absurd (quote (← getGlobals) ctx.lvl expected) e
      | ety => throwAt (ctx.withInfo (stx.getArg 1)).info s!"absurd expects a proof of False or Empty, got {← showVal ctx ety}"
    | "term.hole" => freshMeta ctx
    | "term.syntheticHole" => freshMeta ctx s!"?{((stx.getArg 1).getId?).getD "_"}"
    | "term.paren" => check ctx (stx.getArg 1) expected
    | "term.app" =>
      if (stx.getArg 0).isOfKind "term.explicit" || (← builtinApp? ctx stx).isSome ||
          !(stx.getArg 1).args.any needsExpected then
        let (t, ty) ← infer ctx stx
        unifyAt ctx stx expected ty
        pure t
      else checkApp ctx stx expected
    | _ =>
      let (t, ty) ← infer ctx stx
      let (t, ty) ← if stx.isOfKind "term.explicit" then pure (t, ty) else insertImplicits ctx t ty
      unifyAt ctx stx expected ty
      pure t
  --|ex
  --| sorry
  --sol>

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
    | .pi x bi q dom cod _ =>
      if bi == b.bi then
        if let some tyStx := b.type then
          let (ty, _) ← checkType ctx tyStx
          unifyAt ctx tyStx dom (← evalIn ctx ty)
        if b.qty.isSome then
          let q' ← elabQuantity ctx b.bi b.qty
          let vq' ← evalIn ctx q'
          let ok ← tryCatch (do unify ctx.lvl q vq'; pure true) (fun _ => pure false)
          unless ok do
            throwAt b.info s!"binder quantity {showTerm ctx q'} does not match the expected {← showVal ctx q}"
        let t ← checkFun (ctx.bind b.name dom) rest body (← instM cod (Val.var ctx.lvl))
        return .lam b.name t
      else if bi == .implicit || bi == .instImplicit then
        let t ← checkFun (ctx.bind x dom) bs body (← instM cod (Val.var ctx.lvl))
        return .lam x t
      else throwAt b.info "unexpected implicit binder: the expected type takes an explicit argument"
    | expected =>
      let (t, ty) ← inferFun ctx bs body
      unifyAt ctx body expected ty
      pure t

/-- Stage 4d: data forms that need their expected type: tags, `ecase` (which
generalises its scrutinee in the expected type), and the constructors `Desc.ret`,
`Desc.arg`, `Desc.rec`, `Desc.hrec`, `con`, `coit`, `cocon`. -/
partial def checkData? (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) :
    ElabM R (Option (Term R)) := do
  let g ← getGlobals
  let q := quote g ctx.lvl
  let w := QuantitySyntax.explicitDefault (R := R)
  let expected ← force expected
  let shapeError (what : String) : ElabM R (Option (Term R)) := do
    throwAt ctx.info s!"{what}, but the expected type is {← showVal ctx expected}"
  -- `.c` and `.c args`: a constructor of the expected (nominal) type
  let dot? : Option (Syntax × Name) := match stx.kind with
    | "term.dotIdent" => some (stx, ((stx.getArg 1).getId?).getD "_")
    | "term.app" =>
      let h := stx.getArg 0
      if h.isOfKind "term.dotIdent" then some (h, ((h.getArg 1).getId?).getD "_") else none
    | _ => none
  if let some (h, c) := dot? then
    match expected with
    | .mu l I D i sz (some (T, us, args)) =>
      unless (← getGlobals).contains (T ++ "." ++ c) do
        throwAt h.info s!"{T} has no constructor {c}"
      let ident : Syntax := .node h.info "term.ident" #[.ident h.info (T ++ "." ++ c)]
      let stx' := if stx.isOfKind "term.app" then .node stx.info "term.app" #[ident, stx.getArg 1] else ident
      let sizedBase := match (sizeView sz).1 with
        | some (.neutral (.local _) #[]) | some (.neutral (.mvar _) _) => true
        | _ => false
      if !sizedBase then return some (← check ctx stx' expected)
      -- a sized expected type: the value has size `↑m`, where `m` is the size of its
      -- recursive arguments (the generated constructors themselves return `T^∞`)
      let m ← freshMeta ctx "a size"
      let vm ← evalIn ctx m
      if stx.isOfKind "term.app" then
        for a in (stx.getArg 1).args do
          let some (_, aty) ← tryCatch (some <$> infer ctx a) (fun _ => pure none) | continue
          if let .mu _ _ _ _ asz (some (T', _, _)) ← force aty then
            if T' == T then unifyAt ctx a vm asz
      let (t, _) ← infer ctx stx'
      let payload := quote g ctx.lvl (← evalIn ctx t)
      let ty : Val R := .mu l I D i (.szSuc vm) (some (T, us, args))
      unifyAt ctx stx expected ty
      return some (.ann payload (q ty))
    | .nu _ _ _ _ _ (some (T, _, _)) =>
      -- `.mk h t`: the coconstructor of a coinductive type (`T.mk`, a `cocon`)
      unless (← getGlobals).contains (T ++ "." ++ c) do
        throwAt h.info s!"{T} has no coconstructor {c}"
      let ident : Syntax := .node h.info "term.ident" #[.ident h.info (T ++ "." ++ c)]
      let stx' := if stx.isOfKind "term.app" then .node stx.info "term.app" #[ident, stx.getArg 1] else ident
      return some (← check ctx stx' expected)
    | _ => return ← shapeError s!".{c} needs an expected inductive type"
  match stx.kind with
  | "term.tag" =>
    let x := ((stx.getArg 1).getId?).getD "_"
    let .enum ls := expected | shapeError s!"'{x} is a tag"
    match ls.idxOf? x with
    | some i => return some (.tag ls i)
    | none => throwAt ctx.info s!"'{x} is not one of the tags {ls}"
  | "term.ecase" =>
    let (s, sty) ← infer ctx (stx.getArg 1)
    let .enum ls ← force sty | throwAt ctx.info s!"ecase expects a tag, got {← showVal ctx sty}"
    let bs := (stx.getArg 3).args.filter (!· matches .atom ..)
    unless bs.size == ls.length do throwAt ctx.info s!"ecase needs {ls.length} branches"
    let s := q (← evalIn ctx s)
    let motive := (q expected).abstract s
    let bs ← bs.toList.mapIdxM fun k b => do
      check ctx b (eval g (.tag ls k :: ctx.env) motive)
    return some (.ecase "z" motive s bs)
  | _ =>
  let some (n, args) ← builtinApp? ctx stx | return none
  match n, args, expected with
  | "Desc.ret", #[i], .desc _ I => return some (.dret (← check ctx i I))
  | "Desc.arg", #[qs, S, D], .desc l I =>
    let qt ← check ctx qs .qty
    let S' ← check ctx S (.sort (.succ l))
    let vS ← evalIn ctx S'
    let D' ← check ctx D (ctx.sortVal g (.pi "s" .default (.qlit w) vS (.mk [I] (.desc l (.var 1))) none))
    return some (.darg qt S' D')
  | "Desc.rec", #[qs, j, D], .desc l I =>
    return some (.drec (← check ctx qs .qty) (← check ctx j I) (← check ctx D (.desc l I)))
  | "Desc.hrec", #[qs, H, j, D], .desc l I =>
    let (H', lH) ← checkType ctx H
    unifyLevel lH (.succ l)
    let jTy : VTy R := ctx.sortVal g (.pi "h" .default (.qlit w) (← evalIn ctx H') (.mk ctx.env (quote g (ctx.lvl + 1) I)) none)
    return some (.dhrec (← check ctx qs .qty) H' (← check ctx j jTy) (← check ctx D (.desc l I)))
  | "con", #[x], .mu l I D i _ _ => return some (.con (← check ctx x (vInterp g l I D (muFamily l I D) i)))
  | "coit", #[S, st, s], .nu l I D i _ _ =>
    let S' ← check ctx S (coitStateTy l I w)
    let vS ← evalIn ctx S'
    let st' ← check ctx st (coitStepTy g l I D vS w)
    let s' ← check ctx s (vApp g vS i)
    return some (.coit l (q I) (q D) S' st' (q i) s')
  | "cocon", #[x], .nu l I D i sz _ =>
    -- `cocon xs : ν^{↑s} D i` for a payload whose recursive fields are at `ν^s`
    let some s' := sizePred? sz
      | throwAt ctx.info s!"cocon builds a value of size ↑s, but the expected type is {← showVal ctx expected}"
    return some (.cocon (← check ctx x (vInterp g l I D (nuFamilyAt l I D s') i)))
  | "Desc.ret", _, _ | "Desc.arg", _, _ | "Desc.rec", _, _ | "Desc.hrec", _, _ =>
    shapeError s!"{n} builds a description"
  | "con", _, _ => shapeError "con builds an inductive value"
  | "coit", _, _ => shapeError "coit builds a coinductive value"
  | "cocon", _, _ => shapeError "cocon builds a coinductive value"
  | _, _, _ => return none

/-- Stage 4d: data primitives whose type can be inferred. -/
partial def inferData? (ctx : LocalCtx R) (stx : Syntax) : ElabM R (Option (Term R × VTy R)) := do
  let g ← getGlobals
  let q := quote g ctx.lvl
  let w := QuantitySyntax.explicitDefault (R := R)
  let some (n, args) ← builtinApp? ctx stx | return none
  let descOf (D : Syntax) : ElabM R (Term R × Level × VTy R) := do
    let (D', dty) ← infer ctx D
    let .desc l I ← force dty | throwAt ctx.info s!"expected a description, got {← showVal ctx dty}"
    pure (D', l, I)
  match n, args with
  | "Desc", #[I] =>
    let (I', lI) ← checkType ctx I
    let l ← freshLevelMeta
    unifyLevel lI (.succ l)
    return some (.desc l I', .sort (.succ (.succ l)))
  | "μ", #[D, i] | "ν", #[D, i] =>
    let (D', l, I) ← descOf D
    let i' ← check ctx i I
    return some ((if n == "μ" then Term.mu else Term.nu) l (q I) D' i' .szInf none, .sort (.succ l))
  | "Desc.elim", #[P, a, b, c, h, D] =>
    let (D', l, I) ← descOf D
    let v ← freshLevelMeta
    let P' ← check ctx P (delimMotiveTy l v I w)
    let vP ← evalIn ctx P'
    let (ta, tb, tc, th) := delimMethodTys g l I vP w
    return some (.delim v P' (← check ctx a ta) (← check ctx b tb) (← check ctx c tc) (← check ctx h th) D',
                 vApp g vP (← evalIn ctx D'))
  | "Desc.interp", #[D, X, i] =>
    let (D', l, I) ← descOf D
    let X' ← check ctx X (coitStateTy l I w)
    let i' ← check ctx i I
    -- β-reduce the template: the kernel can't infer a type for a bare lambda
    let v ← evalIn ctx ([q I, D', X', i'].foldl .app (Templates.interpTm l))
    return some (q v, .sort (.succ l))
  | "Desc.All", #[D, X, P, i, xs] =>
    let (D', l, I) ← descOf D
    let X' ← check ctx X (coitStateTy l I w)
    let vX ← evalIn ctx X'
    let v ← freshLevelMeta
    -- (i : I) → X i → Sort v
    let Pty : VTy R := ctx.sortVal g <| eval g [vX, I] (.pi "i" .default (.qlit w) (.var 1)
      (.pi "_" .default (.qlit w) (.app (.var 1) (.var 0)) (.sort v) none) none)
    let P' ← check ctx P Pty
    let i' ← check ctx i I
    let xs' ← check ctx xs (vInterp g l I (← evalIn ctx D') vX (← evalIn ctx i'))
    let all ← evalIn ctx ([q I, D', X', P', i', xs'].foldl .app (Templates.allTm l v))
    return some (q all, .sort (.max (.succ l) v))
  | "ind", #[P, m, x] =>
    let (x', xty) ← infer ctx x
    let .mu l I D i _ _ ← force xty | throwAt ctx.info s!"ind expects an inductive value, got {← showVal ctx xty}"
    let v ← freshLevelMeta
    let P' ← check ctx P (indMotiveTy g l v I D w)
    let vP ← evalIn ctx P'
    let m' ← check ctx m (indMethodTy g l v I D vP w)
    return some (.ind l (q I) (q D) v P' m' (q i) x', vApp g (vApp g vP i) (← evalIn ctx x'))
  | "out", #[x] =>
    let (x', xty) ← infer ctx x
    let .nu l I D i _ _ ← force xty | throwAt ctx.info s!"out expects a coinductive value, got {← showVal ctx xty}"
    return some (.out x', vInterp g l I D (nuFamily l I D) i)
  | _, _ => return none

/-- Check `(a, b, c)` against a (right-nested) Σ. -/
partial def checkTuple (ctx : LocalCtx R) (items : List Syntax) (expected : VTy R) :
    ElabM R (Term R) := do
  match items with
  | [] => throwAt ctx.info "empty tuple"
  | [t] => check ctx t expected
  | t :: rest =>
    match ← force expected with
    | .sigma _ _ A B _ =>
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
    return (.pair a b, ctx.sortVal g (.sigma "_" (.qlit QuantitySyntax.explicitDefault) aty (.mk ctx.env bTerm) none))

/-- `let q (x, y) := s; body`, check mode only (the motive is the expected type). -/
partial def elabLetPair (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) : ElabM R (Term R) := do
  let q ← elabQuantity ctx .default (stx.getArg 1).args[0]?
  let x := ((stx.getArg 3).getId?).getD "_"
  let y := ((stx.getArg 5).getId?).getD "_"
  let (s, sty) ← infer ctx (stx.getArg 8)
  match ← force sty with
  | .sigma _ _ A B _ =>
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
    return (.lam b.name t, ctx.sortVal g (.pi b.name b.bi (← evalIn ctx q) vty (.mk ctx.env (quote g ctx'.lvl bty)) none))

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
    return (.pi b.name b.bi q ty cod (some (.imax l₁ l₂)), .imax l₁ l₂)

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
    return (.sigma b.name q ty cod (some (.max l₁ l₂)), .sort (.max l₁ l₂))

/-- Does elaborating this argument need its expected type to be known? -/
partial def needsExpected (stx : Syntax) : Bool :=
  (stx.isOfKind "term.paren" && needsExpected (stx.getArg 1)) ||
  stx.isOfKind "term.dotIdent" || stx.isOfKind "term.tag" || stx.isOfKind "term.rfl" ||
  (stx.isOfKind "term.app" && (stx.getArg 0).isOfKind "term.dotIdent") ||
  -- check-only forms, also as the body of a `fun` (as in `bind x (fun y => match …)`);
  -- `term.block` is the prelude's `do`
  stx.isOfKind "term.match" || stx.isOfKind "term.by" || stx.isOfKind "term.block" ||
  -- a lambda's binder types usually come from the expected type
  stx.isOfKind "term.fun"

/-- An application in check mode, using the **expected type first**: every explicit
argument gets a placeholder metavariable, the resulting type is unified with the
expected type (failure is fine here), and only then are the arguments elaborated,
against domains that are now usually known. That is what lets `.cons .zero .nil` find
its constructors. Each placeholder is then unified with its argument. -/
partial def checkApp (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) : ElabM R (Term R) := do
  let (f, fty) ← infer ctx (stx.getArg 0)
  let mut f := f
  let mut fty := fty
  let mut pending : Array (Syntax × Term R × VTy R) := #[]
  for arg in (stx.getArg 1).args do
    (f, fty) ← insertImplicits ctx f fty
    match ← force fty with
    | .pi _ _ _ dom cod _ =>
      let m ← freshMeta (ctx.withInfo arg) "an argument"
      pending := pending.push (arg, m, dom)
      f := .app f m
      fty ← instM cod (← evalIn ctx m)
    | _ => return ← (do let (t, ty) ← inferApp ctx stx; unifyAt ctx stx expected ty; pure t)
  (f, fty) ← insertImplicits ctx f fty
  let _ ← tryCatch (unify ctx.lvl expected fty) (fun _ => pure ())
  let mut args : Array (Term R × Term R) := #[]
  for (arg, m, dom) in pending do
    let a ← check ctx arg dom
    args := args.push (m, a)
    -- solve the placeholder with `fun Γ => a` directly when we can: unification would
    -- quote `a`'s value, which can be expensive (normalising under binders)
    let unsolved ← match (Term.spine m).1 with
      | .mvar id => pure (if (← lookupMeta id).solution.isNone then some id else none)
      | _ => pure none
    match unsolved with
    | some mid =>
      if ctx.bound.all (· == true) then
        solveMeta mid (eval (← getGlobals) [] (ctx.names.reverse.foldr (fun x b => Term.lam x b) a))
      else unifyAt ctx arg (← evalIn ctx m) (← evalIn ctx a)
    | none => unifyAt ctx arg (← evalIn ctx m) (← evalIn ctx a)
  unifyAt ctx stx expected fty
  -- the application itself takes the arguments as written, not the placeholders (whose
  -- solutions would zonk to normal forms)
  let rec respine (t : Term R) : Term R := match t with
    | .app g x => .app (respine g) (((args.find? (·.1 == x)).map (·.2)).getD x)
    | t => t
  pure (respine f)

/-- **Exercise 3.9.** Infer the type of an application `f a₁ … aₙ` (`term.app`, with
`f` = `stx.getArg 0` and the arguments in `(stx.getArg 1).args`).

Infer `f`. Then for each argument: unless `f` was written `@f`, insert implicits; force
the function type; if it is a Π, check the argument against the domain and instantiate
the codomain with the argument's value. If the function type is an unsolved meta,
unify it with a fresh Π `(x : ?A) → ?B x` first. Anything else is "not a function".

With `@f`, each argument fills the next Π whether implicit or explicit. -/
partial def inferApp (ctx : LocalCtx R) (stx : Syntax) : ElabM R (Term R × VTy R) := do
  --<sol
  let fStx := stx.getArg 0
  let explicitMode := fStx.isOfKind "term.explicit"
  let (f, fty) ← infer ctx fStx
  let mut f := f
  let mut fty := fty
  for arg in (stx.getArg 1).args do
    if !explicitMode then
      (f, fty) ← insertImplicits ctx f fty
    let fty' ← match ← force fty with
      | ty@(.pi ..) => pure ty
      | ty@(.neutral (.mvar _) _) =>
        let a ← freshMeta ctx "a function domain"
        let va ← evalIn ctx a
        let b ← freshMeta (ctx.bind "x" va) "a function codomain"
        let pi : Val R := .pi "x" .default (.qlit QuantitySyntax.explicitDefault) va (.mk ctx.env b) none
        unifyAt ctx fStx ty pi
        pure pi
      | ty => do
        let msg := s!"function expected\n  {showTerm ctx f} : {← showVal ctx ty}"
        throwAt (ctx.withInfo fStx).info msg
    match fty' with
    | .pi _ _ _ dom cod _ =>
      let a ← check ctx arg dom
      f := .app f a
      fty ← instM cod (← evalIn ctx a)
    | _ => throwAt {} "unreachable"
  pure (f, fty)
  --|ex
  --| sorry
  --sol>

/-- Compile clauses over the variables `vars` (levels) against `goal`. -/
partial def compileMatch (ctx : LocalCtx R) (vars : List Lvl) (clauses : List (MClause R))
    (goal : VTy R) (rc : Option RecCtx) (top : Bool) : ElabM R (Term R) := do
  let g ← getGlobals
  let q (v : Val R) : Term R := quote g ctx.lvl v
  let varTm (l : Lvl) : Term R := .var (ctx.lvl - l - 1)
  let typeOf (l : Lvl) : VTy R := ctx.types[ctx.lvl - l - 1]!
  let nameOf (l : Lvl) : Name := ctx.names[ctx.lvl - l - 1]!
  let some cl := clauses.head? | throwAt ctx.info "missing cases"
  -- A catch-all last row of a multi-column match would be copied into every leaf of the
  -- split (one per pair of constructors, say): elaborate it once, as a local function
  -- of the scrutinees, and make the row call it. If it doesn't check generically (its
  -- right-hand side relies on what the other rows learnt), copy it as before.
  let isCatchAll (c : MClause R) : Bool := c.binds.isEmpty && c.pats.all fun p =>
    match patView g p with
    | .ok (.var _) | .ok .wild => true
    | _ => false
  if let some last := clauses.getLast? then
    let n := vars.length
    -- (a small right-hand side is cheaper to copy than to call)
    let rec size : Syntax → Nat
      | .node _ _ args => args.foldl (fun acc a => acc + size a) 1
      | _ => 1
    if top && rc.isNone && n ≥ 2 && clauses.length ≥ 2 && isCatchAll last && !isCatchAll cl &&
        size last.rhs > 24 &&
        vars == (List.range n).map (ctx.lvl - n + ·) then
      let shared? ← tryCatch (some <$> do
        let w : Term R := .qlit QuantitySyntax.explicitDefault
        let body ← compileMatch ctx vars [last] goal none false
        let mut fn := body
        let mut fnTy := q goal
        for x in vars.reverse do
          fn := .lam (nameOf x) (fn.abstract (varTm x))
          fnTy := .pi (nameOf x) .default w (q (typeOf x)) (fnTy.abstract (varTm x)) none
        fnTy := ctx.sortType g fnTy
        let fnTyV ← evalIn ctx fnTy
        let ctx' := ctx.define "dflt✝" fnTyV (← evalIn ctx fn)
        let names := (List.range n).map fun i => s!"a✝{i}"
        let idStx (x : Name) : Syntax := .node {} "term.ident" #[.ident {} x]
        let callRhs : Syntax := .node {} "term.app" #[idStx "dflt✝", .node {} "null" (names.map idStx).toArray]
        let call : MClause R := { pats := names.map idStx, rhs := callRhs }
        let rest ← compileMatch ctx' vars (clauses.dropLast ++ [call]) goal none true
        pure (Term.letE "dflt✝" w fnTy fn rest)) (fun _ => pure none)
      if let some t := shared? then return t
  -- find the first constructor pattern of the first clause
  let views ← cl.pats.mapM fun p => match patView g p with
    | .ok v => pure v
    | .error e => throwAt p.info e
  let some k := views.findIdx? (fun v => v matches .ctor .. || v matches .tuple ..) | do
    -- all variables: bind them and elaborate the right-hand side
    let mut binds := cl.binds
    for v in views, x in vars do
      if let .var n := v then binds := binds ++ [(n, typeOf x, Val.var x)]
    let mut rhs := cl.rhs
    if let some rc := rc then
      let ihType (l : Lvl) : Option (VTy R) := ctx.types[ctx.lvl - l - 1]?
      match rewriteRecCalls g rc binds ihType ctx.lvl cl.rhs with
      | .ok (r, extra) => rhs := r; binds := binds ++ extra
      | .error e => throwAt cl.rhs.info e
    let mut ctx' := ctx
    for (n, ty, val) in binds do ctx' := ctx'.define n ty val
    let body ← check ctx' rhs goal
    -- wrap the lets, innermost last. A pattern variable that names a variable (a field)
    -- is substituted instead: a `let` at ω would use an erased field at ω.
    let mut t := body
    let mut lvl := ctx'.lvl
    for (n, ty, val) in binds.reverse do
      lvl := lvl - 1
      match quote g lvl val with
      | v@(.var _) => t := t.instantiateAt 0 v
      | v => t := .letE n (.qlit QuantitySyntax.explicitDefault) (quote g lvl ty) v t
    return t
  -- a pair pattern: match the components, as two new (defined) variables
  if views[k]! matches .tuple .. then
    let x := vars[k]!
    let .sigma _ _ A B _ ← force (typeOf x)
      | throwAt (cl.pats[k]!).info s!"a tuple pattern needs a pair, not {← showVal ctx (typeOf x)}"
    let xv ← evalIn ctx (varTm x)
    let v1 := vFst xv
    let ty2 := Closure.inst g B v1
    let v2 := vSnd xv
    let ctx2 := (ctx.define "fst✝" A v1).define "snd✝" ty2 v2
    let vars' := vars.take k ++ [ctx.lvl, ctx.lvl + 1] ++ vars.drop (k + 1)
    let clauses' ← clauses.mapM fun c => do
      let p := c.pats[k]!
      let (ps, binds) ← match patView g p with
        | .ok (.tuple a b) => pure ([a, b], c.binds)
        | .ok (.var n) => pure ([holeStx, holeStx], c.binds ++ [(n, typeOf x, xv)])
        | .ok .wild => pure ([holeStx, holeStx], c.binds)
        | _ => throwAt p.info "expected a tuple pattern"
      pure { c with pats := c.pats.take k ++ ps ++ c.pats.drop (k + 1), binds }
    let body ← compileMatch ctx2 vars' clauses' goal rc top
    let w : Term R := .qlit QuantitySyntax.explicitDefault
    return .letE "fst✝" w (q A) (q v1) (.letE "snd✝" w (quote g (ctx.lvl + 1) ty2) (quote g (ctx.lvl + 1) v2) body)
  if rc.isSome && top && k != 0 then
    throwAt cl.rhs.info "structural recursion: the first argument must be matched first"
  let x := vars[k]!
  let rs := vars.drop (k + 1)
  let xty ← force (typeOf x)
  let .mu _ _ _ ξi xsz (some (T, us, args)) := xty
    | throwAt (cl.pats[k]!).info s!"cannot match on a value of type {← showVal ctx xty}"
  let some descD := g.find? (T ++ ".desc") | throwAt ctx.info s!"{T} is not an inductive type"
  let nΔ := (piInfos descD.type).length
  let Δargs := args.take nΔ
  let ξ := args.drop nΔ
  let ξLvls := ξ.filterMap fun v => match v with
    | .neutral (.local l) #[] => some l
    | _ => none
  let modeA := ξLvls.length == ξ.length && ξLvls.eraseDups.length == ξLvls.length &&
    !ξLvls.contains x && ξLvls.all (fun l => !rs.contains l)
  let useRec := rc.isSome && top
  -- a scrutinee of finite size is split with the sized eliminator, keeping field sizes
  let sized := !(xsz matches .szInf)
  if sized && useRec then
    throwAt ctx.info "structural recursion on a sized argument: give the definition a sized signature instead"
  -- G := Π rs. goal
  let w : Term R := .qlit QuantitySyntax.explicitDefault
  let mut G := q goal
  for r in rs.reverse do
    let wr : Term R := if ctx.erasedLvls.contains r then .qlit 0 else w
    G := .pi (nameOf r) .default wr (q (typeOf r)) (G.abstract (varTm r)) none
  G := ctx.sortType g G
  -- the motive's universe
  let tys := ctx.types.reverse.toArray
  let Gv ← evalIn ctx G
  let vG := typeSort? g tys Gv
  let ctors : List Name := match descD.value.map (fun v => (piInfos descD.type).foldl (fun t _ => match t with
      | .lam _ b => b
      | t => t) v) with
    | some (.darg _ (.enum ls) _) => ls
    | _ => []
  let nΞ := ξ.length
  let motive : Term R ←
    if modeA then
      -- each abstraction puts `body` under one more binder, so later targets are lifted
      let mut body := G
      for l in ξLvls, i in [0:ξLvls.length] do body := body.abstract ((varTm l).lift i)
      body := body.abstract ((varTm x).lift ξLvls.length)
      pure ((ξLvls.map nameOf ++ [nameOf x]).foldr .lam body)
    else
      if G.hasVar (ctx.lvl - x - 1) then
        throwAt (cl.pats[k]!).info "this match needs index unification whose goal depends on the scrutinee; not supported yet"
      let .mu _ I _ _ _ _ := xty | unreachable!
      let lhs : Term R := (List.range nΞ).foldr (fun k acc => .pair (.var (nΞ - k)) acc) .tt
      let eqTm : Term R := .eq ((q I).lift (nΞ + 1)) lhs ((q ξi).lift (nΞ + 1))
      let body : Term R := .pi "e" .default (.qlit 0) eqTm (G.lift (nΞ + 2)) (vG.map (.imax 0 ·))
      pure ((List.range nΞ).foldr (fun k acc => .lam s!"i{k}" acc) (.lam "x" body))
  -- a type still to be found (an inferred `match`) is taken to be in `Type`
  let unknown := match whnf Gv with
    | .neutral (.mvar _) _ => true
    | _ => false
  let some v := vG.orElse fun _ => if unknown then some (.succ .zero) else none
    | throwAt ctx.info "could not determine the universe of the match's type"
  let elimName := T ++ (if sized then ".scasesOn" else if useRec then ".rec" else ".casesOn")
  let some ed := g.find? elimName | throwAt ctx.info s!"{elimName} is missing"
  let elimHead : Term R := .const elimName (us ++ [v])
  let sizeArgs : List (Val R) := if sized then [xsz] else []
  let mut f : Term R := ((Δargs ++ sizeArgs).map q).foldl .app elimHead |>.app motive
  -- the eliminator's type, instantiated with the parameters (size) and the motive
  let mut fty : VTy R := eval g [] (ed.type.instLevels ed.levelParams (us ++ [v]))
  for a in Δargs ++ sizeArgs ++ [← evalIn ctx motive] do
    let .pi _ _ _ _ cod _ ← force fty | throwAt ctx.info "internal error: eliminator type"
    fty ← instM cod a
  -- one method per constructor
  for c in ctors do
    let some cd := g.find? (T ++ "." ++ c) | throwAt ctx.info s!"missing constructor {c}"
    let fieldInfos := (piInfos cd.type).drop nΔ
    -- `T …`, or `(h : H) → T …` (an infinitary field: its hypothesis is a function)
    let isRecField (A : Term R) : Bool :=
      let head : Term R → Bool := fun A => match (Term.spine A).1 with
        | .const n _ => n == T
        | _ => false
      match A with
      | .pi _ _ _ _ B _ => head B
      | A => head A
    let nRec := if useRec then (fieldInfos.filter fun (_, _, A) => isRecField A).length else 0
    let .pi _ _ _ mTy cod _ ← force fty | throwAt ctx.info "internal error: eliminator type"
    -- introduce fields, hypotheses, the equation, and the reverted variables
    let mut ctx' := ctx
    let mut mt := mTy
    if sized then
      -- the fields' size `j : Size< s`
      let .pi _ _ _ A B _ ← force mt | throwAt ctx.info "internal error: sized method"
      mt ← instM B (Val.var ctx'.lvl)
      ctx' := ctx'.bind "_j" A
    let mut fieldLvls : Array Lvl := #[]
    for (n, _, _) in fieldInfos do
      let .pi _ _ fq A B _ ← force mt | throwAt ctx.info "internal error: method type"
      fieldLvls := fieldLvls.push ctx'.lvl
      if ((Val.toPoly? fq).bind (·.isConst?)) == some 0 then
        ctx' := { ctx' with erasedLvls := ctx'.lvl :: ctx'.erasedLvls }
      mt ← instM B (Val.var ctx'.lvl)
      -- hidden: the patterns name the fields (`.ok items s1`), and a field's own name
      -- (`s`) must not shadow a variable of the same name in the right-hand side
      ctx' := ctx'.bind (n ++ "✝") A
    let mut ihLvls : Array Lvl := #[]
    for _ in [0:nRec] do
      let .pi _ _ _ A B _ ← force mt | throwAt ctx.info "internal error: hypothesis type"
      ihLvls := ihLvls.push ctx'.lvl
      mt ← instM B (Val.var ctx'.lvl)
      ctx' := ctx'.bind "_ih" A
    let mut absurdBody : Option (Term R) := none
    let mut eInfo : Option (Lvl × VTy R) := none
    if !modeA then
      let .pi _ _ _ E B _ ← force mt | throwAt ctx.info "internal error: equation"
      let eLvl := ctx'.lvl
      eInfo := some (eLvl, E)
      mt ← instM B (Val.var eLvl)
      ctx' := ctx'.bind "e✝" E
      if let some prf := findAbsurd g (← force E) (Val.var eLvl) then
        absurdBody := some (.absurd (quote g ctx'.lvl mt) (quote g ctx'.lvl prf))
    let body ← match absurdBody with
      | some b => pure b
      | none =>
        -- the solution rule with an equation: find `y = t` (or `t = y`) with `y` a field
        -- of this constructor, and substitute it in the later fields by re-binding them
        let mut solution : Option (Lvl × Val R × Bool × Val R × Val R) := none
        if let some (eLvl, E) := eInfo then
          for (prf, A, a, b) in findEqs g (← force E) (Val.var eLvl) do
            if solution.isSome then break
            for (yv, tv, yFirst) in [(a, b, true), (b, a, false)] do
              if let .neutral (.local y) #[] := yv then
                let later := fieldLvls.toList.filter (· ≥ y)
                let tTm := quote g ctx'.lvl tv
                if fieldLvls.contains y && later.all (fun l => !tTm.hasVar (ctx'.lvl - l - 1)) &&
                    solution.isNone then
                  solution := some (y, tv, yFirst, prf, A)
        let mut subst : List (Lvl × Val R) := []
        let mut fieldLvls' := fieldLvls
        let ctxBefore := ctx'
        if let some (y, tv, _, _, _) := solution then
          -- re-bind the fields after `y` with `y := t` (and earlier re-bound fields)
          subst := [(y, tv)]
          for d in fieldLvls.toList.filter (· > y) do
            let tyTm := quote g ctx'.lvl ctx'.types[ctx'.lvl - d - 1]!
            let env : Env R := (List.range ctx'.lvl).reverse.map fun l =>
              ((subst.find? (·.1 == l)).map (·.2)).getD (Val.var l)
            let ty' := eval g env tyTm
            subst := subst ++ [(d, Val.var ctx'.lvl)]
            fieldLvls' := fieldLvls'.map fun l => if l == d then ctx'.lvl else l
            if ctx'.erasedLvls.contains d then
              ctx' := { ctx' with erasedLvls := ctx'.lvl :: ctx'.erasedLvls }
            ctx' := ctx'.bind ctx'.names[ctx'.lvl - d - 1]! ty'
        let mut rsLvls : Array Lvl := #[]
        -- the motive over the reverted variables (the solution rule casts under them too)
        let mtRs := mt
        for r in rs do
          let .pi _ _ _ A B _ ← force mt | throwAt ctx.info "internal error: reverted variable"
          rsLvls := rsLvls.push ctx'.lvl
          mt ← instM B (Val.var ctx'.lvl)
          ctx' := ctx'.bind (nameOf r) A
        -- the value of `x` in this branch, for variable patterns
        let ctorVal ← evalIn ctx' ((Δargs.map (quote g ctx'.lvl) ++ fieldLvls.toList.map
          (fun l => (.var (ctx'.lvl - l - 1) : Term R))).foldl .app (.const (T ++ "." ++ c) us))
        let explicitIdx := fieldInfos.zipIdx.filter (fun ((_, bi, _), _) => bi == .default) |>.map (·.2)
        let mut cls : List (MClause R) := []
        for cl' in clauses do
          let pv ← match patView g (cl'.pats[k]!) with
            | .ok v => pure v
            | .error e => throwAt (cl'.pats[k]!).info e
          let before := cl'.pats.take k
          let after := cl'.pats.drop (k + 1)
          match pv with
          | .ctor _ c' ps =>
            if c' == c then
              unless ps.length == explicitIdx.length do
                throwAt (cl'.pats[k]!).info s!"{c} expects {explicitIdx.length} explicit arguments"
              let sub := (List.range fieldInfos.length).map fun i =>
                match explicitIdx.idxOf? i with
                | some j => ps[j]!
                | none => holeStx
              cls := cls ++ [{ cl' with pats := before ++ sub ++ after }]
          | .var n =>
            let sub := fieldInfos.map fun _ => holeStx
            -- the variable is `x` itself (no object is rebuilt from its fields), unless
            -- the goal depends on `x` (then only the constructor has the refined type) or
            -- this is the recursor's split: its method also runs for the hypotheses,
            -- where the value at hand is the constructor, not `x`
            let xVal := if useRec || G.hasVar (ctx.lvl - x - 1) then ctorVal else Val.var x
            let binds := cl'.binds ++ [(n, xty, xVal)]
            cls := cls ++ [{ cl' with pats := before ++ sub ++ after, binds := binds }]
          | .wild =>
            cls := cls ++ [{ cl' with pats := before ++ (fieldInfos.map fun _ => holeStx) ++ after }]
          | .tuple .. => throwAt (cl'.pats[k]!).info "a tuple pattern needs a pair"
        if cls.isEmpty then throwAt ctx.info s!"missing case for constructor {c}"
        -- reverted variables are re-introduced at new levels: their hypotheses follow them
        let moved := rs.zip rsLvls.toList
        let rc := rc.map fun r => { r with ihs := r.ihs.map fun (a, b) => ((moved.lookup a).getD a, (moved.lookup b).getD b) }
        let rc' := rc.map fun r => { r with ihs := r.ihs ++ (if useRec then
          ((fieldLvls'.toList.zip (fieldInfos.map fun (f : Name × BinderInfo × Term R) => f.2.2)).filter
            (fun (_, A) => isRecField A)).map (·.1) |>.zip ihLvls.toList else []) }
        -- the hypotheses are extra (wildcard) columns, so that nested splits revert them too:
        -- their types mention the fields being split
        let ihCols := if useRec then ihLvls.toList else []
        let cls2 := cls.map fun cl => { cl with pats := cl.pats ++ ihCols.map fun _ => holeStx }
        let inner ← compileMatch ctx' (vars.take k ++ fieldLvls'.toList ++ rsLvls.toList ++ ihCols) cls2 mt rc' false
        let body0 := (rs.map nameOf).foldr .lam inner
        match solution with
        | none => pure body0
        | some (y, tv, yFirst, prf, A) =>
          -- cast `fun deps' => body0 : (Π deps[y := t]. M)` to `(Π deps. M)`, apply to deps
          let L := ctxBefore.lvl
          let deps := fieldLvls.toList.filter (· > y)
          let vt (l : Lvl) : Term R := .var (L - l - 1)
          let mut Gd := quote g L mtRs
          for d in deps.reverse do
            Gd := .pi ctxBefore.names[L - d - 1]! .default
              (if ctxBefore.erasedLvls.contains d then .qlit 0 else .qlit QuantitySyntax.explicitDefault)
              (quote g L ctxBefore.types[L - d - 1]!) (Gd.abstract (vt d)) none
          Gd := ctxBefore.sortType g Gd
          let Gdz := Gd.abstract (vt y)              -- under a binder for `y`
          let tTm := quote g L tv
          let Gdt := Gdz.instantiateAt 0 tTm
          let F := (deps.map fun d => ctxBefore.names[L - d - 1]!).foldr .lam body0
          let (aT, bT, Q, refl) :=
            if yFirst then  -- prf : y = t; Q z _ := (Π deps(z)) = (Π deps(y))
              (vt y, tTm, Term.lam "z" (.lam "h" (.eqTy (Gdz.lift 1) (Gd.lift 2))), Term.reflTy Gd)
            else            -- prf : t = y; Q z _ := (Π deps(t)) = (Π deps(z))
              (tTm, vt y, Term.lam "z" (.lam "h" (.eqTy (Gdt.lift 2) (Gdz.lift 1))), Term.reflTy Gdt)
          let eqPrf : Term R := .transp (quote g L A) aT Q refl bT (quote g L prf)
          let _ := Q
          let castTm : Term R := .cast Gdt Gd (if yFirst then eqPrf else eqPrf) F
          -- `body0` was built under the re-bound fields, which sit after `e` in the context
          pure (deps.foldl (fun acc d => .app acc (vt d)) castTm)
    -- lambdas for fields, hypotheses and the equation
    let names := (if sized then ["_j"] else []) ++ fieldInfos.map (·.1) ++ (List.replicate nRec "_ih") ++
      (if modeA then [] else ["e"])
    let method := names.foldr .lam body
    f := .app f method
    fty ← instM cod (← evalIn ctx method)
  -- indices, scrutinee, equation proof, reverted variables
  for vξ in ξ do f := .app f (q vξ)
  f := .app f (varTm x)
  if !modeA then
    let .mu _ I _ _ _ _ := xty | unreachable!
    f := .app f (.refl (q I) (q ξi))
  for r in rs do f := .app f (varTm r)
  pure f
where
  nameOf' (_ : Lvl) : Name := "_"

/-- Elaborate `match e₁, …, eₙ with | p₁, …, pₙ => rhs …` against `expected`. -/
partial def elabMatch (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) : ElabM R (Term R) := do
  let g ← getGlobals
  let scruts := (stx.getArg 1).args.filter (!· matches .atom ..)
  let alts := (stx.getArg 3).args
  let clauses : List (MClause R) := alts.toList.map fun a =>
    { pats := ((a.getArg 1).args.filter (!· matches .atom ..)).toList, rhs := a.getArg 3 }
  -- bind every scrutinee to a fresh variable, generalising it in the goal
  let mut ctx' := ctx
  let mut ts : Array (Term R) := #[]
  -- zonk: solved metas in the expected type would otherwise hide its universe
  let mut goalTm ← zonk ctx.lvl (quote g ctx.lvl expected)
  let mut binders : Array (Name × Term R) := #[]
  for s in scruts do
    let (t, ty) ← infer ctx s
    ts := ts.push t
    -- an inaccessible name, so the user's own `x` isn't shadowed
    binders := binders.push ("x✝", quote g ctx.lvl ty)
  -- abstract the scrutinees, last first
  let mut absGoal := goalTm
  for t in ts.reverse do absGoal := absGoal.abstract t
  let _ := goalTm
  let mut lvls : List Lvl := []
  for (n, tyTm) in binders, i in [0:binders.size] do
    -- scrutinee types are taken as they are (they may not depend on earlier scrutinees)
    let vTy ← evalIn ctx' (tyTm.lift i)
    lvls := lvls ++ [ctx'.lvl]
    ctx' := ctx'.bind n vTy
  goalTm := absGoal
  let goal ← evalIn ctx' goalTm
  let body ← compileMatch ctx' lvls clauses goal none true
  let lam := (binders.toList.map (·.1)).foldr .lam body
  -- (the `i`-th scrutinee's type is under the `i` binders before it)
  let piTy := binders.toList.zipIdx.foldr (fun ((n, A), i) acc => Term.pi n .default (.qlit QuantitySyntax.explicitDefault) (A.lift i) acc none) goalTm
  let piTy := ctx.sortType g piTy
  pure (ts.foldl .app (.ann lam piTy))

/-- **Exercise 6.2.** Elaborate the body of a quotation to a term that builds it as a
Wiz `Syntax` value: `SyntaxF.missing`, `SyntaxF.atom "v"`, `SyntaxF.node "k" args` with
`args` a chain of `SyntaxF.cons`/`SyntaxF.nil`, and `SyntaxF.ident "x✝"`: an
identifier gets the `✝` mark (its scope is chosen when the macro runs) unless it is
dotted or under one of the `unscopedParents`, as in `instantiate`. An antiquotation
`$x` is the local `x`, checked against `Syntax`. `mkStringLit` builds strings. -/
partial def elabQuote (ctx : LocalCtx R) (syntaxTy : VTy R) (parent : Name) (stx : Syntax) :
    ElabM R (Term R) := do
  --<sol
  let c (n : Name) : Term R := .const ("SyntaxF." ++ n) []
  if let some x := antiquotName? stx then
    return ← check ctx (.node stx.info "term.ident" #[.ident stx.info x]) syntaxTy
  match stx with
  | .missing => pure (c "missing")
  | .atom _ v => pure (.app (c "atom") (← mkStringLit v))
  | .ident _ n =>
    let n := if unscopedParents.contains parent || n.contains '.' then n else n ++ "✝"
    pure (.app (c "ident") (← mkStringLit n))
  | .node _ k args =>
    let mut list := c "nil"
    for a in args.reverse do
      list := .app (.app (c "cons") (← elabQuote ctx syntaxTy k a)) list
    pure (.app (.app (c "node") (← mkStringLit k)) list)
  --|ex
  --| sorry
  --sol>

/-- Infer the type of `stx`. -/
partial def infer (ctx : LocalCtx R) (stx : Syntax) : ElabM R (Term R × VTy R) := do
  let ctx := ctx.withInfo stx
  if let some stx' ← expand? stx then return ← infer ctx stx'
  match stx.kind with
  | "term.ident" | "term.explicit" | "term.identUniv" =>
    let x := (stx.getArg (if stx.isOfKind "term.explicit" then 1 else 0)).getId?.getD "_"
    let explicitLevels : Option (Array Syntax) := if stx.isOfKind "term.identUniv" then
        some ((stx.getArg 2).args.filter (!· matches .atom ..)) else none
    -- (stage 11) remember identifiers and their types, for hovers and go-to-definition
    let record (n : Name) (c : LocalCtx R) (ty : VTy R) : ElabM R Unit := do
      if stx.info.stop > 0 then
        let shown ← showVal c ty
        modify fun s => { s with hovers := s.hovers.push (stx.info, n, shown) }
    if explicitLevels.isNone then
      if let some (ix, ty) := lookupLocal ctx x then
        record x ctx ty
        return (.var ix, ty)
    -- a macro-scoped name that isn't a local refers to the global of its base name
    let x := stripScope x
    match (← getGlobals).find? x with
    | some d =>
      let us ← match explicitLevels with
        | some ls =>
          unless ls.size == d.levelParams.length do
            throwAt ctx.info s!"{x} has {d.levelParams.length} universe parameters, {ls.size} given"
          ls.toList.mapM elabLevel
        | none => d.levelParams.mapM fun _ => freshLevelMeta
      let ty ← evalIn {} (d.type.instLevels d.levelParams us)
      record x {} ty
      return (.const x us, ty)
    | none =>
      -- built-in types
      let builtinLevel : Option Level := match explicitLevels with
        | some _ => none
        | none => some (if x == "True" || x == "False" then 0 else 1)
      match x, explicitLevels with
      | "Unit", some #[l] | "Empty", some #[l] =>
        let l ← elabLevel l
        return (if x == "Unit" then .unit l else .empty l, .sort l)
      | "Qty", none => return (.qty, .sort 1)
      | "Size", none => return (.size, .sort 1)
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
  | "term.app" =>
    if let some r ← inferData? ctx stx then return r
    inferApp ctx stx
  | "term.enum" =>
    let ls := ((stx.getArg 2).args.filterMap Syntax.getId?).toList
    return (.enum ls, .sort 1)
  | "term.ecase" =>
    -- non-dependent: the first branch's type is the type of every branch
    let (s, sty) ← infer ctx (stx.getArg 1)
    let .enum ls ← force sty | throwAt ctx.info s!"ecase expects a tag, got {← showVal ctx sty}"
    let bs := ((stx.getArg 3).args.filter (!· matches .atom ..)).toList
    let b₀ :: rest := bs | throwAt ctx.info "ecase needs branches"
    unless bs.length == ls.length do throwAt ctx.info s!"ecase needs {ls.length} branches"
    let (t₀, ty) ← infer ctx b₀
    let ts ← rest.mapM fun b => check ctx b ty
    let motive := (quote (← getGlobals) ctx.lvl ty).lift 1
    return (.ecase "z" motive s (t₀ :: ts), ty)
  | "term.fun" =>
    -- annotate: the kernel can't infer the type of a bare lambda (e.g. `(fun x => b) a`)
    let (t, ty) ← inferFun ctx ((stx.getArg 1).args.flatMap binderViews).toList (stx.getArg 3)
    return (.ann t (quote (← getGlobals) ctx.lvl ty), ty)
  | "term.let" => elabLet ctx stx none
  | "term.arrow" =>
    let (a, l₁) ← checkType ctx (stx.getArg 0)
    let (b, l₂) ← checkType (ctx.bind "_" (← evalIn ctx a)) (stx.getArg 2)
    return (.pi "_" .default (defaultQty .default) a b (some (.imax l₁ l₂)), .sort (.imax l₁ l₂))
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
    return (.sigma "_" (defaultQty .default) a b (some (.max l₁ l₂)), .sort (.max l₁ l₂))
  | "term.tuple" =>
    inferTuple ctx (#[stx.getArg 1] ++ ((stx.getArg 3).args.filter (!· matches .atom ..))).toList
  | "term.unitVal" => return (.tt, .unit 1)
  | "term.szInf" => return (.szInf, .size)
  | "term.szSuc" => return (.szSuc (← check ctx (stx.getArg 1) .size), .size)
  | "term.sizeLt" => return (.sizeLt (← check ctx (stx.getArg 1) .size), .sort 1)
  | "term.sized" =>
    let (T, ty) ← infer ctx (stx.getArg 0)
    let s ← check ctx (stx.getArg 2) .size
    let g ← getGlobals
    let q := quote g ctx.lvl
    let qh (h : Option (Name × List Level × List (Val R))) := h.map fun (n, us, as) => (n, us, as.map q)
    match ← force (← evalIn ctx T) with
    | .mu l I D i _ h => return (.mu l (q I) (q D) (q i) s (qh h), ty)
    | .nu l I D i _ h => return (.nu l (q I) (q D) (q i) s (qh h), ty)
    | v => throwAt ctx.info s!"only inductive and coinductive types have sizes, not {← showVal ctx v}"
  | "term.field" =>
    let (t, ty) ← infer ctx (stx.getArg 0)
    -- `.a.b.c` lexes as one dotted identifier
    let path := (((stx.getArg 2).getId?).getD "_").splitOn "."
    elabFields ctx t ty path
  | "term.proj" =>
    let (t, ty) ← infer ctx (stx.getArg 0)
    match ← force ty, (stx.getArg 2).getNat? with
    | .sigma _ _ A _ _, some 1 => return (.fst t, A)
    | .sigma _ _ _ B _, some 2 => return (.snd t, ← instM B (vFst (← evalIn ctx t)))
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
      let motiveTy : Val R := ctx.sortVal g (.pi "b" .default (.qlit 0) A
        (.mk [a, A] (.pi "_" .default (.qlit 0) (.eq (.var 2) (.var 1) (.var 0)) (.sort 0) (some 1))) none)
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
  | "term.match" =>
    -- stage 13: the type is found from the alternatives (a metavariable, in `Type`)
    -- (not depending on the scrutinised variables: the motive abstracts them, which
    -- would leave the metavariable outside the pattern fragment)
    let scrut := (stx.getArg 1).args.toList.filterMap fun a =>
      if a.isOfKind "term.ident" then (a.getArg 0).getId? else none
    let firstIx (n : Name) : Option Nat := ctx.names.findIdx? (· == n)
    let hidden := scrut.filterMap firstIx
    let ctx' := { ctx with bound := ctx.bound.zipIdx.map fun (b, i) => b && !hidden.contains i }
    let ty ← evalIn ctx (← freshMeta ctx' "the type of this match")
    return (← check ctx stx ty, ty)
  | "term.letPair" | "term.absurd" | "term.rfl" =>
    throwAt ctx.info "cannot infer the type of this expression; add a type ascription"
  | "term.omega" => return (← elabQtyLit ctx stx "ω", .qty)
  | "term.num" =>
    -- an unannotated numeral is a `builtin nat`
    match (← get).builtins.lookup "nat" with
    | some N =>
      let ty := eval (← getGlobals) ctx.env (.const N [])
      -- (`check` comes back here unless the type is the data type `N`: don't loop)
      unless (← force ty) matches .mu _ _ _ _ _ (some _) do
        throwAt ctx.info s!"numerals need `builtin nat :=` a data type, and {N} is not one"
      return (← check ctx stx ty, ty)
    | none => throwAt ctx.info "numerals need `builtin nat := …` or a type ascription"
  | "term.str" =>
    match (← get).builtins.lookup "string" with
    | some S =>
      let ty := eval (← getGlobals) ctx.env (.const S [])
      return (← check ctx stx ty, ty)
    | none => throwAt ctx.info "string literals need `builtin string := …`"
  | k =>
    if k.startsWith "quote." then
      let syntaxTy ← evalIn {} (.const "Syntax" [])
      return (← elabQuote ctx syntaxTy "" (stx.getArg 3), syntaxTy)
    throwAt ctx.info s!"no elaborator for syntax kind {k}"


-- Tactics (see `Elab/Tactic.lean`)

/-- Run the tactic syntax `stx`: expand macros, find the Wiz function registered for
its kind, run it to a `Tac` request chain, and interpret that. -/
partial def evalTacticStx (code : Code) (st : TacState R) (stx : Syntax) : ElabM R (TacState R) := do
  if stx matches .atom .. then return st
  if let some stx' ← expand? stx then return ← evalTacticStx code st stx'
  let some f := (← get).tactics.lookup stx.kind | throwAt stx.info s!"no tactic for syntax kind {stx.kind}"
  let t := apply code (run code [] (.global "TacticM.run")) (apply code (run code [] (.global f)) (encodeSyntax stx))
  runTac code stx.info st t

/-- **Exercise 6.5** (the request loop). Interpret the requests of a `Tac` value (the
constructor numbers are in `TacTag`), threading the tactic state, until `done`.
Each request's last field is its continuation: apply it (`apply code`) to the encoded
answer and continue. A failure is an elaboration error; `catch` runs its handler
on the state from *before* the body (`ElabM` drops state changes on an exception). -/
partial def runTac (code : Code) (info : SourceInfo) (st : TacState R) (v : RVal) : ElabM R (TacState R) := do
  let g ← getGlobals
  let fld (i : Nat) : RVal := v.conField i
  let num (r : RVal) : ElabM R Nat := match r.toNat? with
    | some n => pure n
    | none => throwAt info "tactic: malformed number"
  let str (r : RVal) : ElabM R String := match r.toString? with
    | some s => pure s
    | none => throwAt info "tactic: malformed string"
  let stxOf (r : RVal) : ElabM R Syntax := match decodeSyntax info r with
    | some s => pure s
    | none => throwAt info "tactic: malformed syntax"
  let goalOf (r : RVal) : ElabM R (Goal R) := do
    let some gl := st.goals[← num r]? | throwAt info "tactic: unknown goal"
    pure gl
  -- reflect a term (zonked first) in a goal's context
  let refl (st : TacState R) (gl : Goal R) (t : Term R) (depth : Nat := gl.ctx.lvl) :
      ElabM R (RVal × TacState R) := do
    let t ← zonk depth t
    let (r, hs) := (reflect t depth).run st.handles
    pure (r, { st with handles := hs })
  let addGoal (st : TacState R) (gl : Goal R) : TacState R × Nat :=
    ({ st with goals := st.goals.push gl }, st.goals.size)
  let unifyGoal (gl : Goal R) (t : Term R) : ElabM R Unit := do
    unify gl.ctx.lvl (← evalIn gl.ctx gl.tm) (← evalIn gl.ctx t)
  --<sol
  let tag := (v.tag?).getD 1000
  if tag == TacTag.done then return st
  if tag == TacTag.result then throwAt info "a tactic may not return syntax"
  if tag == TacTag.fail then throwAt info (((fld 0).toString?).getD "tactic failed")
  if tag == TacTag.trace then return ← runTac code info st (fld 1)
  if tag == TacTag.fresh then
    let n := (← get).nextScope
    modify fun s => { s with nextScope := n + 1 }
    return ← runTac code info st (apply code (fld 0) (.nat n))
  if tag == TacTag.getGoals then
    let opens ← st.open.filterM fun i => match st.goals[i]? with
      | some gl => gl.isOpen
      | none => pure false
    return ← runTac code info { st with «open» := opens } (apply code (fld 0) (encodeList (opens.map encodeNat)))
  if tag == TacTag.setGoals then
    let some gs := decodeList (fld 0) | throwAt info "tactic: malformed goal list"
    return ← runTac code info { st with «open» := ← gs.mapM num } (fld 1)
  if tag == TacTag.evalTactic then
    let st ← evalTacticStx code st (← stxOf (fld 0))
    return ← runTac code info st (fld 1)
  if tag == TacTag.catch_ then
    let st' ← try runTac code info st (fld 0)
      catch e => runTac code info st (apply code (fld 1) (encodeString e.msg))
    return ← runTac code info st' (fld 2)
  -- the rest are about a goal, the first field
  let gl ← goalOf (fld 0)
  let lvl := gl.ctx.lvl
  if tag == TacTag.goalType then
    let (r, st) ← refl st gl (quote g lvl gl.ty)
    return ← runTac code info st (apply code (fld 1) r)
  if tag == TacTag.goalExpr then
    let (r, st) ← refl st gl gl.tm
    return ← runTac code info st (apply code (fld 1) r)
  if tag == TacTag.goalHyps then
    let mut st := st
    let mut hyps : Array RVal := #[]
    for j in [0:lvl] do
      let (r, st') ← refl st gl (quote g lvl gl.ctx.types[j]!)
      st := st'
      hyps := hyps.push (encodePair (encodeString gl.ctx.names[j]!) r)
    return ← runTac code info st (apply code (fld 1) (encodeList hyps.toList))
  if tag == TacTag.intro then
    let x ← str (fld 1)
    let .pi _ _ _ dom cod _ ← force gl.ty | throwAt info "intro: the goal is not a function type"
    let ctx' := gl.ctx.bind x dom
    let m ← freshMeta ctx' "goal"
    unifyGoal gl (.lam x m)
    let (st, id) := addGoal st { ctx := ctx', ty := ← instM cod (Val.var lvl), tm := m }
    return ← runTac code info st (apply code (fld 2) (.nat id))
  if tag == TacTag.exact then
    let stx ← stxOf (fld 1)
    let t ← check (gl.ctx.withInfo stx) stx gl.ty
    unifyGoal gl t
    return ← runTac code info st (fld 2)
  if tag == TacTag.elabInfer then
    let (t, ty) ← infer gl.ctx (← stxOf (fld 1))
    let (r₁, st) ← refl st gl t
    let (r₂, st) ← refl st gl (quote g lvl ty)
    return ← runTac code info st (apply code (fld 2) (encodePair r₁ r₂))
  if tag == TacTag.assign then
    let t ← zonk lvl (← reify st.handles (fld 1) lvl)
    if t.mvars.isEmpty then
      match (← get).kernelInfer (gl.kernelCtx g) t with
      | .ok ty => unifyAt gl.ctx .missing gl.ty ty
      | .error e => throwAt info s!"assign: {e}"
    unifyGoal gl t
    return ← runTac code info st (fld 2)
  if tag == TacTag.newGoal then
    let ty ← evalIn gl.ctx (← reify st.handles (fld 1) lvl)
    let m ← freshMeta gl.ctx "goal"
    let (st, id) := addGoal st { ctx := gl.ctx, ty, tm := m }
    return ← runTac code info st (apply code (fld 2) (.nat id))
  if tag == TacTag.normalize then
    let v' ← evalIn gl.ctx (← reify st.handles (fld 1) lvl)
    let (r, st) ← refl st gl (quote g lvl v')
    return ← runTac code info st (apply code (fld 2) r)
  if tag == TacTag.instantiate then
    let body ← reify st.handles (fld 1) (lvl + 1)
    let arg ← reify st.handles (fld 2) lvl
    let (r, st) ← refl st gl (body.instantiateAt 0 arg)
    return ← runTac code info st (apply code (fld 3) r)
  if tag == TacTag.isDefEq then
    let a ← evalIn gl.ctx (← reify st.handles (fld 1) lvl)
    let b ← evalIn gl.ctx (← reify st.handles (fld 2) lvl)
    let ok ← try unify lvl a b; pure true catch _ => pure false
    return ← runTac code info st (apply code (fld 3) (encodeBool ok))
  if tag == TacTag.inferType then
    let t ← zonk lvl (← reify st.handles (fld 1) lvl)
    unless t.mvars.isEmpty do throwAt info "inferType: the term has holes"
    let ty ← match (← get).kernelInfer (gl.kernelCtx g) t with
      | .ok ty => pure ty
      | .error e => throwAt info s!"inferType: {e}"
    let (r, st) ← refl st gl (quote g lvl ty)
    return ← runTac code info st (apply code (fld 2) r)
  throwAt info s!"tactic: unknown request {tag}"
  --|ex
  --| sorry
  --sol>

/-- `by tac₁; tac₂ …`: a hole of the expected type, filled by running the tactics. -/
partial def elabBy (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) : ElabM R (Term R) := do
  let s ← get
  let code ← match s.compileCode ("TacticM.run" :: s.tactics.map (·.2)) with
    | .ok c => pure c
    | .error e => throwAt ctx.info e
  let m ← freshMeta ctx "by"
  let mut st : TacState R := { goals := #[{ ctx, ty := expected, tm := m }], «open» := [0] }
  -- each step is `[tactic, [";"?]]`
  let tacs := (stx.getArg 1).args.filterMap fun step => step.args[0]?
  for t in tacs do
    st ← try evalTacticStx code st t
      catch e => throw (if e.info.stop == 0 then { e with info := (ctx.withInfo t).info } else e)
  let mut rest : Array String := #[]
  for i in st.open do
    if let some gl := st.goals[i]? then
      if ← gl.isOpen then rest := rest.push (← gl.show)
  unless rest.isEmpty do throwAt ctx.info s!"unsolved goals:\n{"\n\n".intercalate rest.toList}"
  pure m

end

end Wiz.Elab
