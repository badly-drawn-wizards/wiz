import Wiz.Elab.Recursor
import Wiz.Compiler.Run
import Wiz.Compiler.IRRun
import Wiz.Compiler.Lower
import Wiz.FFI.CParse
import Wiz.FFI.CGlue
import Wiz.Compiler.C
import Wiz.Elab.ProcMacro
import Wiz.Frontend.Parse

/-!
# Elaborating commands

* `def f binders : T := v`: elaborate the binders into a local context, then `T` and
  `v` inside it, abstract over the binders, zonk, and hand the result to the
  **kernel** (`addDecl`). The kernel re-checks everything, including quantities, so
  linearity errors come from there.
* `axiom f binders : T`
* `#check t`: print `t : T` without inserting implicit arguments.
* `#reduce t`: print the normal form of `t`.
* `syntax`, `declare_syntax_cat`: update the parser tables.

There is no recursion: a definition can't mention itself, because its name isn't in
the environment until the kernel has accepted it. Recursion over data arrives in
stage 4, through eliminators.
-/

namespace Wiz

open Elab

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

inductive Severity where
  | info
  | error
  deriving BEq, Repr, Inhabited

structure Msg where
  info : SourceInfo
  severity : Severity
  text : String
  deriving Repr, Inhabited

def Msg.render (input : String) (m : Msg) : String :=
  let (l, c) := lineCol input m.info.start
  let sev := if m.severity == .error then "error" else "info"
  s!"{l + 1}:{c + 1}: {sev}: {m.text}"

structure CommandState (R : Type) where
  globals : Globals R := {}
  tables : ParserTables := Builtin.tables
  messages : Array Msg := #[]
  /-- coinductive types and their observations (name, recursive?) -/
  coinductives : List (Name × List (Name × Bool)) := []
  /-- library sources by module name (supplied by the caller: the frontend is pure) -/
  loader : Name → Option String := fun _ => none
  imported : List Name := []
  /-- `builtin key := name` registrations -/
  builtins : List (Name × Name) := []
  /-- `attribute [macro k] f` registrations, latest first -/
  procMacros : List (Name × Name) := []
  /-- `attribute [tactic k] f` registrations, latest first -/
  tactics : List (Name × Name) := []
  /-- the erased code of every registered macro and tactic, made on first use (a `Thunk`
  remembers its value) and remade when one is registered -/
  metaCode : Thunk (Except String Code) := Thunk.pure (.ok {})
  /-- type classes and instances (stage 7) -/
  classes : List ClassInfo := []
  instances : Array InstanceInfo := #[]
  /-- preprocessed C headers, for `import_c` (the command line runs the preprocessor) -/
  cHeaders : String → Option String := fun _ => none
  /-- the C functions glue code may call: from imported headers, and earlier glue -/
  cFuncs : List (String × List FFI.GTy × FFI.GTy) := []
  /-- C code to emit: header includes and the glue functions -/
  cCode : Array String := #[]
  /-- foreign pointer types and their finalizers -/
  foreignTypes : List (Name × String) := []
  /-- for the language server (stage 11): identifiers with their types, and where each
  global was declared (its command's range, and module; `""` is the main file) -/
  hovers : Array (SourceInfo × Name × String) := #[]
  declSites : Std.HashMap Name (SourceInfo × String) := {}
  /-- the module being elaborated (`""` for the main file) -/
  module : String := ""
  /-- macro rules, latest first -/
  macros : List (Name × Syntax × Syntax × List Name) := []
  nextScope : Nat := 1000000

/-- Metas are untyped, so `?A : Sort ?u` never learns `?u` from `?A := A`. For each
recorded constraint whose hole is now solved, ask the kernel for the solution's type
and unify its level. -/
def solveSortConstraints : ElabM R Unit := do
  finishInstances
  -- size metavariables nothing constrained default to `∞`
  let ms := (← get).metas
  for e in ms, m in [0:ms.size] do
    if e.desc == "a size" && e.solution.isNone then
      let sol : Term R := (List.range e.arity).foldl (fun t _ => .lam "_" t) .szInf
      solveMeta m (eval (← getGlobals) [] sol)
  for _ in [0:2] do
    for (ctx, t, l) in (← get).sortConstraints do
      let t ← zonk ctx.lvl t
      if !t.mvars.isEmpty then continue
      let kctx : Ctx R := { globals := ← getGlobals, env := ctx.env, names := ctx.names,
                            qtys := ctx.names.map fun _ => QPoly.const QuantitySyntax.explicitDefault,
                            types := ctx.types, lvl := ctx.lvl }
      if let .ok (ty, _) := Wiz.infer kctx t then
        if let .sort l' ← force ty then
          try unifyLevel l l' catch e => throwAt ctx.info e.msg

/-- Elaborate the header and body of a `def` or `axiom` to closed, zonked terms. -/
def elabDeclTerms (binders : Array Syntax) (typeStx : Option Syntax) (valStx : Option Syntax)
    (info : SourceInfo) : ElabM R (Term R × Option (Term R)) := do
  let (ctx, tele) ← elabTelescope { info } (binders.flatMap binderViews).toList
  let ty ← match typeStx with
    | some s => pure (← Elab.checkType ctx s).1
    | none => freshMeta ctx "the type of this definition"
  let val ← valStx.mapM fun s => do Elab.check ctx s (← evalIn ctx ty)
  let ty := tele.foldr (fun (x, bi, q, a) b => Term.pi x bi q a b none) ty
  let val := val.map fun v => tele.foldr (fun (x, _, _, _) b => Term.lam x b) v
  solveSortConstraints
  let ty ← zonk 0 ty
  ensureNoMVars ty info
  let val ← val.mapM (zonk 0)
  if let some v := val then ensureNoMVars v info
  pure (ty, val)

partial def syntaxMentions (n : Name) : Syntax → Bool
  | .ident _ m => m == n
  | .node _ _ as => as.any (syntaxMentions n)
  | _ => false

/-- A recursive definition with a sized first argument, `def f {i : Size} : T^i → … | …`,
compiles to `sfix`. Inside, `f` is a local definition `fun {j : Size< s} y => rec j () y`,
so a recursive call type-checks only on an argument of a smaller size: that is the
termination check. Nested matches give fields of ever smaller sizes, so
course-of-values recursion (`fib (n + 2) = fib n + fib (n + 1)`) works. (Non-indexed
types only, for now.) -/
def elabSizedDef (name : Name) (cmd : Syntax) (ctx : LocalCtx R) (tele : Array (Name × BinderInfo × Term R × Term R))
    (ty : Term R) (si : Lvl) (clauses : List (MClause R)) : ElabM R (Term R × Term R) := do
  let info := cmd.info
  let g ← getGlobals
  let w : R := QuantitySyntax.explicitDefault
  let .pi x0 bi0 q0 A0 B s0 := ty | throwAt info "internal error: sized definition"
  -- the outer `fun x0 =>`
  let vA0 ← evalIn ctx A0
  let .mu l I D idx _ hint ← force vA0 | throwAt info "internal error: sized argument"
  unless (← force I) matches .unit _ do
    throwAt info "sized recursion is only supported on non-indexed types (for now)"
  let c1 := ctx.bind x0 vA0
  let q (c : LocalCtx R) (v : Val R) : Term R := quote g c.lvl v
  -- P := fun _ x' => B[x0 := x']   (B is under the x0 binder)
  let P : Term R := .lam "_" (.lam x0 (B.lift 1 1))
  let vP ← evalIn c1 P
  let some vlev := typeSort? g c1.types.reverse.toArray (← evalIn c1 B)
    | throwAt info "could not determine the universe of the result"
  -- F := fun s rec i x' => let f := …; fun rest => tree
  let fty := sfixFunTy g l I D vP w
  let .pi _ _ _ _ c_s _ ← force fty | throwAt info "internal error"
  let ctxS := c1.bind "s" .size
  let sv := Val.var c1.lvl
  let afterS ← instM c_s sv
  let .pi _ _ _ recTy c_rec _ ← force afterS | throwAt info "internal error"
  let ctxR := ctxS.bind "rec" recTy
  let recV := Val.var ctxS.lvl
  let afterRec ← instM c_rec recV
  let .pi _ _ _ iTy c_i _ ← force afterRec | throwAt info "internal error"
  let ctxI := ctxR.bind "i" iTy
  let iV := Val.var ctxR.lvl
  let afterI ← instM c_i iV
  let .pi _ _ _ xTy c_x _ ← force afterI | throwAt info "internal error"
  -- keep the nominal display (the match compiler finds `T` through it)
  let xTy := match xTy with
    | .mu l' I' D' i' s' _ => Val.mu l' I' D' i' s' hint
    | t => t
  let ctxX := ctxI.bind x0 xTy
  let xLvl := ctxI.lvl
  let goalP ← instM c_x (Val.var xLvl)
  -- the local `f : {j : Size< s} → (y : T^j) → P () y`
  let L := ctxX.lvl
  let sT : Term R := .var (L - c1.lvl - 1)
  let recT : Term R := .var (L - ctxS.lvl - 1)
  let hintT := hint.map fun (n, us, as) => (n, us, as.map (quote g (L + 2)))
  let fTyTm : Term R := .pi "j" .implicit (.qlit 0) (.sizeLt sT)
    (.pi "y" .default (.qlit w) (.mu l (q ctxX I |>.lift 1) (q ctxX D |>.lift 1) (q ctxX idx |>.lift 1) (.var 0) hintT)
      ((Term.app (Term.app ((P.lift (L - c1.lvl)).lift 2) .tt) (.var 0))) none) none
  -- β-reduce `P () y` (the kernel can't infer the type of an applied lambda)
  let fTyTm := quote g L (← evalIn ctxX fTyTm)
  let fValTm : Term R := .lam "j" (.lam "y" (.app (.app (.app (recT.lift 2) (.var 1)) .tt) (.var 0)))
  let ctxL := ctxX.define name (← evalIn ctxX fTyTm) (← evalIn ctxX fValTm)
  -- introduce the remaining arguments
  let mut ctx' := ctxL
  let mut goal := goalP
  let mut vars : List Lvl := [xLvl]
  let mut names : List Name := []
  let n := (clauses.head?.map (·.pats.length)).getD 1
  for k in [1:n] do
    let .pi x _ _ A Bc _ ← force goal | throwAt info s!"{name} takes fewer than {n} arguments"
    let x := if x == "_" then s!"a{k}" else x
    vars := vars ++ [ctx'.lvl]
    names := names ++ [x]
    goal ← instM Bc (Val.var ctx'.lvl)
    ctx' := ctx'.bind x A
  let tree ← compileMatch ctx' vars clauses goal none true
  let body := Term.letE name (.qlit w) fTyTm fValTm (names.foldr .lam tree)
  let F : Term R := .lam "s" (.lam "rec" (.lam "i" (.lam x0 body)))
  let sizeVarT : Term R := .var (c1.lvl - si - 1)
  let sfixT : Term R := .sfix l (q c1 I) (q c1 D) vlev P F sizeVarT .tt (.var 0)
  solveSortConstraints
  let val := tele.foldr (fun (x, _, _, _) b => Term.lam x b) (.lam x0 sfixT)
  let fullTy := tele.foldr (fun (x, bi, qq, a) b => Term.pi x bi qq a b none) (Term.pi x0 bi0 q0 A0 B s0)
  let val ← zonk 0 val
  ensureNoMVars val info
  pure (fullTy, val)

/-- `def f binders : T | p… => rhs …`: the alternatives match the leading explicit
arguments of `T`; a right-hand side that calls `f` makes it structurally recursive. -/
def elabDefEqns (name : Name) (cmd : Syntax) (isPartial : Bool := false) :
    ElabM R (Term R × Term R × Option (Term R)) := do
  let info := cmd.info
  let (ctx, tele) ← elabTelescope { info } (((cmd.getArg 3).args.flatMap binderViews)).toList
  let tyStx := (cmd.getArg 4).getArg 1
  let (ty, _) ← Elab.checkType ctx tyStx
  let ty ← zonk ctx.lvl ty
  ensureNoMVars ty info
  let alts := (cmd.getArg 5).args
  let clauses : List (MClause R) := alts.toList.map fun a =>
    { pats := ((a.getArg 1).args.filter (!· matches .atom ..)).toList, rhs := a.getArg 3 }
  let n := (clauses.head?.map (·.pats.length)).getD 0
  -- introduce `n` arguments of the type
  let mut ctx' := ctx
  let mut tyv ← evalIn ctx ty
  let mut vars : List Lvl := []
  let mut names : List Name := []
  for i in [0:n] do
    let .pi x _ _ A B _ ← force tyv | throwAt tyStx.info s!"{name} takes fewer than {n} arguments"
    let x := if x == "_" then s!"a{i}" else x
    vars := vars ++ [ctx'.lvl]
    names := names ++ [x]
    tyv ← instM B (Val.var ctx'.lvl)
    ctx' := ctx'.bind x A
  let mentions (stx : Syntax) : Bool := syntaxMentions name stx
  -- (a partial definition calls itself as a declared constant instead)
  let recursive := !isPartial && clauses.any (fun c => mentions c.rhs)
  -- structural recursion is on the first argument the first clause matches: put its
  -- column first (the others follow in order, as the hypotheses take them)
  let g ← getGlobals
  let pos : Nat := if !recursive then 0 else
    match clauses.head? with
    | some c => (c.pats.findIdx? fun p => match patView g p with
        | .ok (.ctor ..) => true
        | _ => false).getD 0
    | none => 0
  let perm {α : Type} (xs : List α) : List α :=
    match xs.drop pos with
    | x :: rest => if pos == 0 then xs else x :: (xs.take pos ++ rest)
    | [] => xs
  let params := (tele.filterMap fun (x, bi, _, _) => if bi == .default then some x else none).toList
  let rc : Option RecCtx := if recursive then some { fn := name, params, pos, cols := n } else none
  -- a recursive definition whose first argument has a size-variable size: compile to `sfix`
  if rc.isSome && pos == 0 then
    if let some x0 := vars.head? then
      if let .mu _ _ _ _ (.neutral (.local si) #[]) _ ← force ctx'.types[ctx'.lvl - x0 - 1]! then
        if si < ctx.lvl then
          let (t, v) ← elabSizedDef name cmd ctx tele ty si clauses
          return (t, v, none)
  let clauses := clauses.map fun c => { c with pats := perm c.pats }
  let body ← compileMatch ctx' (perm vars) clauses tyv rc true
  solveSortConstraints
  let val := tele.foldr (fun (x, _, _, _) b => Term.lam x b) (names.foldr .lam body)
  let fullTy := tele.foldr (fun (x, bi, q, a) b => Term.pi x bi q a b none) ty
  let val ← zonk 0 val
  ensureNoMVars val info
  -- for the compiler: the same equations with direct recursion (the definition, as an
  -- axiom for the moment, is called like any function) and case analysis, so that only
  -- the recursive calls the program makes are computed
  let impl ← if rc.isNone then pure none else do
    let saved ← get
    try
      modify fun s => { s with globals := s.globals.insert { name, levelParams := saved.levelParams, type := fullTy, value := none } }
      let body' ← compileMatch ctx' (perm vars) clauses tyv none true
      solveSortConstraints
      let v' ← zonk 0 (tele.foldr (fun (x, _, _, _) b => Term.lam x b) (names.foldr .lam body'))
      modify fun s => { s with globals := saved.globals }
      pure (if v'.mvars.isEmpty then some v' else none)
    catch _ =>
      set saved
      pure none
  pure (fullTy, val, impl)

/-- Copatterns: `def f binders : T args | .obs => rhs …` for a coinductive `T`
compiles to `coit`. The state is the tuple of the explicit binders; a recursive
observation must be a corecursive call `f e…` (that is the guardedness condition),
whose arguments become the next state. -/
def elabCopatterns (name : Name) (cmd : Syntax) (obs : List (Name × Bool)) : ElabM R (Term R × Term R) := do
  let info := cmd.info
  let g ← getGlobals
  let (ctx, tele) ← elabTelescope { info } (((cmd.getArg 3).args.flatMap binderViews)).toList
  let tyStx := (cmd.getArg 4).getArg 1
  let (ty, _) ← Elab.checkType ctx tyStx
  let ty ← zonk ctx.lvl ty
  ensureNoMVars ty info
  let .nu l I D i _ (some (T, us, args)) ← force (← evalIn ctx ty)
    | throwAt tyStx.info "copatterns need a coinductive result type"
  let q (lvl : Lvl) (v : Val R) : Term R := quote g lvl v
  -- the state: the explicit binders
  let explicit := (tele.toList.zipIdx.filter fun ((_, bi, _, _), _) => bi == .default)
  let w : Term R := .qlit QuantitySyntax.explicitDefault
  let stateTy : Term R := explicit.zipIdx.foldr (fun (((x, _, _, _), k), j) acc =>
    .sigma x w ((q ctx.lvl ctx.types[ctx.lvl - k - 1]!).lift j) acc none) (.unit (.succ l))
  let vS ← evalIn ctx stateTy
  -- the step function's context: i, s, then the explicit binders re-bound from s
  let mut sctx := (ctx.bind "i" I).bind "s" vS
  let sLvl := ctx.lvl + 1
  let mut sv : Val R := Val.var sLvl
  for ((x, _, _, _), k) in explicit do
    sctx := sctx.define x ctx.types[ctx.lvl - k - 1]! (vFst sv)
    sv := vSnd sv
  -- one component per observation, in order
  let alts := (cmd.getArg 5).args.toList
  let mut comps : List (Term R) := []
  for (o, isRec) in obs do
    let some alt := alts.find? fun a =>
        match (a.getArg 1).args[0]? with
        | some p => p.isOfKind "term.dotIdent" && (p.getArg 1).getId? == some o
        | none => false
      | throwAt info s!"missing copattern .{o}"
    let rhs := alt.getArg 3
    if isRec then
      -- `f e…`: the next state
      let (h, es) := if rhs.isOfKind "term.app" then (rhs.getArg 0, (rhs.getArg 1).args.toList) else (rhs, [])
      unless h.isOfKind "term.ident" && (h.getArg 0).getId? == some name do
        throwAt rhs.info s!"the observation .{o} must be a corecursive call of {name} (guardedness)"
      unless es.length == explicit.length do
        throwAt rhs.info s!"{name} takes {explicit.length} explicit arguments"
      let mut es' : List (Term R) := []
      for e in es, ((_, _, _, _), k) in explicit do
        es' := es' ++ [← Elab.check sctx e ctx.types[ctx.lvl - k - 1]!]
      comps := comps ++ [es'.foldr .pair .tt]
    else
      let some od := g.find? (T ++ "." ++ o) | throwAt info s!"unknown observation {o}"
      -- the observation's type at our parameters: {Δ} → T Δ → F
      let mut oty : VTy R := eval g [] (od.type.instLevels od.levelParams us)
      for a in args do
        let .pi _ _ _ _ cod _ ← force oty | throwAt info "internal error: observation type"
        oty ← instM cod a
      let .pi _ _ _ _ cod _ ← force oty | throwAt info "internal error: observation type"
      let F ← instM cod (Val.var 0)
      comps := comps ++ [← Elab.check sctx rhs F]
  let payload : Term R := comps.foldr .pair (.pair .tt .tt)
  -- wrap the lets for the re-bound binders
  let mut stepBody := payload
  let mut lvl := sctx.lvl
  for ((x, _, _, _), _) in explicit.reverse do
    lvl := lvl - 1
    stepBody := .letE x w (q lvl sctx.types[sctx.lvl - lvl - 1]!) (q lvl (vFst (Val.var 0))) stepBody
  -- recompute the let values properly (projections of s), innermost last
  let mut body := payload
  let mut j := explicit.length
  for ((x, _, _, _), k) in explicit.reverse do
    j := j - 1
    let lv := sLvl + 1 + j
    let proj : Term R := .fst ((List.range j).foldl (fun t _ => .snd t) (.var (lv - sLvl - 1)))
    body := .letE x w (q lv ctx.types[ctx.lvl - k - 1]!) proj body
  let _ := stepBody
  let step : Term R := .lam "i" (.lam "s" body)
  let Sfun : Term R := .lam "_" (stateTy.lift 1)
  let init : Term R := (explicit.map fun ((_, _, _, _), k) => (.var (ctx.lvl - k - 1) : Term R)).foldr .pair .tt
  let coit : Term R := .coit l (q ctx.lvl I) (q ctx.lvl D) Sfun step (q ctx.lvl i) init
  let val := tele.foldr (fun (x, _, _, _) b => Term.lam x b) coit
  let fullTy := tele.foldr (fun (x, bi, qq, a) b => Term.pi x bi qq a b none) ty
  let val ← zonk 0 val
  ensureNoMVars val info
  pure (fullTy, val)

/-- Run the elaborator; also returns the identifiers it saw (for hovers). -/
def runElabH (g : Globals R) (x : ElabM R α) (levelParams : List Name := [])
    (macros : List (Name × Syntax × Syntax × List Name) := []) (builtins : List (Name × Name) := [])
    (procMacros : List (Name × Name) := []) (tactics : List (Name × Name) := [])
    (metaCode : Thunk (Except String Code) := Thunk.pure (.ok {}))
    (classes : List ClassInfo := []) (instances : Array InstanceInfo := #[]) :
    Except ElabError (α × Array (SourceInfo × Name × String)) :=
  -- macros and tactics run against the globals as they are when this command starts
  let compileCode (roots : List Name) := match metaCode.get with
    | .ok c => if roots.all c.contains then .ok c
      else (compileReachable g builtins roots).mapError (s!"cannot compile the environment: {·}")
    | .error e => .error e
  let runProcMacro f stx scope := do Elab.runProcMacro (← compileCode [f, "Macro.run"]) f stx scope
  let kernelInfer (ctx : Ctx R) (t : Term R) := (Wiz.infer ctx t).map (·.1) |>.mapError toString
  (x.run { globals := g, levelParams, macros, builtins, procMacros, runProcMacro, tactics, compileCode,
           kernelInfer, classes, instances }).map fun (a, st) => (a, st.hovers)

def runElab (g : Globals R) (x : ElabM R α) (levelParams : List Name := [])
    (macros : List (Name × Syntax × Syntax × List Name) := []) (builtins : List (Name × Name) := [])
    (procMacros : List (Name × Name) := []) (tactics : List (Name × Name) := [])
    (metaCode : Thunk (Except String Code) := Thunk.pure (.ok {}))
    (classes : List ClassInfo := []) (instances : Array InstanceInfo := #[]) : Except ElabError α :=
  (runElabH g x levelParams macros builtins procMacros tactics metaCode classes instances).map (·.1)

/-- The erased code of the registered macros and tactics (and what they reach), on demand. -/
def mkMetaCode (g : Globals R) (builtins procMacros tactics : List (Name × Name)) :
    Thunk (Except String Code) :=
  Thunk.mk fun _ =>
    let roots := "TacticM.run" :: "Macro.run" :: (procMacros ++ tactics).map (·.2)
    (compileReachable g builtins roots).mapError (s!"cannot compile the macros and tactics: {·}")

/-- The method functions of a class `C` (from its structure declaration):
`C.f : {Δ} → [self : C Δ] → F`, the field `f` of `self`, where earlier fields in `F`
become projections of `self`. -/
def classMethods (sDecl : Decl R) (levelParams : List Name) : List (Decl R) := Id.run do
  let C := sDecl.name
  let us := levelParams.map Level.param
  let (Δ, _) := peelPis sDecl.type
  let nΔ := Δ.length
  let rec stripLams : Nat → Term R → Term R
    | 0, t => t
    | n + 1, .lam _ b => stripLams n b
    | _, t => t
  let rec fieldsOf : Term R → List (Name × Term R × Term R)
    | .sigma x q A rest _ => (x, q, A) :: fieldsOf rest
    | _ => []
  let fields := fieldsOf (stripLams nΔ (sDecl.value.getD .tt))
  let proj (i : Nat) (t : Term R) : Term R := .fst ((List.range i).foldl (fun t _ => .snd t) t)
  let implicitΔ := Δ.map fun (x, _, _, A) => (x, BinderInfo.implicit, (.qlit 0 : Term R), A)
  let Capp : Term R := ((List.range nΔ).map fun j => Term.var (nΔ - 1 - j)).foldl .app (.const C us)
  let w : Term R := .qlit QuantitySyntax.explicitDefault
  let mut out := []
  for (x, q, A) in fields, k in [0:fields.length] do
    if q == .qlit 0 then continue
    -- `A` lives under the earlier fields: insert `self` below them, then replace them
    let mut A' := A.lift 1 k
    for i in (List.range k).reverse do
      A' := A'.instantiateAt 0 (proj i (.var i))
    let type := implicitΔ.foldr (fun (y, bi, q, B) acc => .pi y bi q B acc none) (.pi "self" .instImplicit w Capp A' none)
    let value := Δ.foldr (fun (y, _, _, _) acc => .lam y acc) (.lam "self" (proj k (.var 0)))
    let d : Decl R := { name := C ++ "." ++ x, levelParams, type, value := some value }
    out := out ++ [d]
  pure out

/-- `notation` and `infixl`/`infixr`/`infix`: register a syntax rule and a macro rule.
Returns the new tables and the rule `(kind, pattern, template, vars)`. -/
def notationRule (tables : ParserTables) (cmd : Syntax) :
    Except String (ParserTables × (Name × Syntax × Syntax × List Name)) := do
  let antiquot (v : Name) : Syntax := .node {} "antiquot" #[.atom {} "$", .ident {} v]
  -- items: `.inl op` for an atom, `.inr (name, prec?)` for an argument
  let (prec, items, rhs) ← if cmd.isOfKind "command.infix" then do
      let kw := match cmd.getArg 0 with
        | .atom _ v => v
        | _ => "infix"
      let p := ((cmd.getArg 2).getNat?).getD 0
      let some op := (cmd.getArg 3).getStr? | throw "infix needs an operator string"
      let (lp, rp) := if kw == "infixl" then (p, p + 1) else if kw == "infixr" then (p + 1, p) else (p + 1, p + 1)
      let f := cmd.getArg 5
      let rhs : Syntax := .node {} "term.app" #[f, .node {} "null"
        #[.node {} "term.ident" #[.ident {} "a"], .node {} "term.ident" #[.ident {} "b"]]]
      pure (p, [Sum.inr ("a", some lp), Sum.inl op, Sum.inr ("b", some rp)], rhs)
    else do
      let precOpt := cmd.getArg 1
      let p ← if precOpt.isNone then pure maxPrec else precValue (precOpt.getArg 1)
      let items ← (cmd.getArg 2).args.toList.mapM fun it => do
        let x := it.getArg 0
        match x.getStr? with
        | some s => pure (Sum.inl s)
        | none =>
          let v := (x.getId?).getD "_"
          let po := it.getArg 1
          if po.isNone then pure (Sum.inr (v, none))
          else pure (Sum.inr (v, some (← precValue (po.getArg 1))))
      pure (p, items, cmd.getArg 4)
  let descr (it : String ⊕ (Name × Option Nat)) : ParserDescr := match it with
    | .inl s => .atom s.trimAscii.toString
    | .inr (_, p?) => .cat "term" (p?.getD 0)
  let pat (it : String ⊕ (Name × Option Nat)) : Syntax := match it with
    | .inl s => .atom {} s.trimAscii.toString
    | .inr (v, _) => antiquot v
  let vars := items.filterMap fun | .inr (v, _) => some v | _ => none
  match items with
  | .inr (_, lp?) :: rest =>
    let ps := rest.map descr
    let p := if h : ps.length = 1 then ps[0] else .seq ps.toArray
    let kind := mkKindName tables "term" p
    let tables := tables.addTrailing "term" { kind, prec, lhsPrec := lp?.getD prec, p }
    pure (tables, (kind, .node {} kind (items.map pat).toArray, rhs, vars))
  | _ =>
    let ps := items.map descr
    let p := if h : ps.length = 1 then ps[0] else .seq ps.toArray
    let kind := mkKindName tables "term" p
    let tables := tables.addLeading "term" { kind, prec, p }
    pure (tables, (kind, .node {} kind (items.map pat).toArray, rhs, vars))

/-- Can the elaborator see that a type is inhabited? A partial definition is an axiom
to the kernel, and this keeps such axioms from proving `False`. Conservative: Π types
with an inhabited codomain, sorts, `Unit`, nonempty enumerations, pairs, data types with
a constructor whose fields are inhabited (not indexed, no recursive fields), and types
that some declared constant inhabits (`StrMap.empty : StrMap V`). -/
partial def inhabitedTy (g : Globals R) (lvl fuel : Nat) (ty : Val R) (hyps : List Name := []) : Bool :=
  if fuel == 0 then false else
  let headOf (v : Val R) : Option Name := match whnf v with
    | .neutral (.global n _) _ => some n
    | .mu _ _ _ _ _ (some (n, _, _)) => some n
    | _ => none
  -- the variables bound so far inhabit their types (`IO A := (w : World) → A × World`)
  let inh (v : Val R) : Bool :=
    (match headOf v with
     | some n => hyps.contains n
     | none => false) || inhabitedTy g (lvl + 1) (fuel - 1) v hyps
  -- a constant whose type ends in `T …`, with inhabited argument types
  -- (the argument types are checked only shallowly: this search runs over all globals)
  let rec witness (T : Name) (n : Nat) (v : Val R) : Bool :=
    match whnf v with
    | .pi _ _ _ dom cod _ =>
      inhabitedTy g (lvl + n + 1) (min (fuel - 1) 2) dom hyps && witness T (n + 1) (Closure.inst g cod (Val.var (lvl + n)))
    | v => headOf v == some T
  -- (only constants whose type visibly ends in `T …` are evaluated: this runs often)
  let rec resultHead : Term R → Option Name
    | .pi _ _ _ _ b _ => resultHead b
    | t => match t.spine.1 with
      | .const n _ => some n
      | _ => none
  let byConstant (T : Name) : Bool := g.order.any fun c => match g.find? c with
    | some d => c != T && resultHead d.type == some T &&
        witness T 0 (eval g [] (d.type.instLevels d.levelParams (d.levelParams.map fun _ => .zero)))
    | none => false
  let rec fields (d : Val R) : Bool := match whnf d with
    | .dret _ => true
    | .darg _ S E => inh S && fields (vApp g E (Val.var lvl))
    | _ => false
  match whnf ty with
  | .pi _ _ _ dom cod _ =>
    inhabitedTy g (lvl + 1) (fuel - 1) (Closure.inst g cod (Val.var lvl)) ((headOf dom).toList ++ hyps)
  | .sort _ | .unit _ | .qty | .size | .desc .. => true
  | .enum ls => !ls.isEmpty
  | .sigma _ _ A B _ => inh A && inh (Closure.inst g B (Val.var lvl))
  | .mu _ I D _ _ hint =>
    let byCtor := match whnf I, whnf D with
      | .unit _, .darg _ S F => match whnf S with
        | .enum ls => (List.range ls.length).any fun i => fields (vApp g F (.tag ls i))
        | _ => fields D
      | .unit _, _ => fields D
      | _, _ => false
    byCtor || (match hint with
      | some (T, _, _) => byConstant T
      | none => false)
  | .neutral (.global T _) _ => byConstant T
  | _ => false

/-- Mutual inductive types (stage 13) as one family indexed by a tag type:

    mutual inductive A … inductive B … end   ↦   inductive A_B.Tag | A | B
                                                 inductive A_B : A_B.Tag → Type (all constructors)
                                                 def A : Type := A_B A_B.Tag.A   (and B)

Inside the constructors, `A` and `B` stand for their family members. Matching works on
the family's constructors (at a concrete index). No parameters or indices yet. -/
partial def mutualInductive (tables : ParserTables) (defs : Array Syntax) : Except String (List Syntax) := do
  let names := defs.map fun d => ((d.getArg 1).getId?).getD "_"
  for d in defs do
    unless (d.getArg 2).args.isEmpty && (d.getArg 3).args.isEmpty && (d.getArg 4).args.isEmpty do
      throw "mutual inductive types may not have universe parameters, parameters or indices (yet)"
  let fam := "_".intercalate names.toList
  let parse (text : String) : Except String Syntax := match parseCommand text.toList.toArray tables 0 with
    | .ok (stx, _) => pure stx
    | .error _ => throw s!"internal error: could not parse {text}"
  let tagCmd ← parse s!"inductive {fam}.Tag where{String.join (names.toList.map (s!"\n  | " ++ ·))}"
  let famFrame ← parse s!"inductive {fam} : {fam}.Tag → Type where"
  let substs ← names.mapM fun n => match parseCategory tables "term" s!"({fam} {fam}.Tag.{n})" with
    | .ok t => pure (n, t)
    | .error e => throw s!"internal error: {e}"
  let rec subst (stx : Syntax) : Syntax := match stx with
    | .node i "term.ident" #[.ident j n] => match substs.find? (·.1 == n) with
      | some (_, t) => t
      | none => .node i "term.ident" #[.ident j n]
    | .node i k as => .node i k (as.map subst)
    | s => s
  let ctors := (defs.zip substs).flatMap fun (d, (_, self)) => (d.getArg 6).args.map fun c =>
    let c := subst c
    if (c.getArg 3).args.isEmpty then c.setArg 3 (.node {} "null" #[.atom {} ":", self]) else c
  let famCmd := famFrame.setArg 6 (.node {} "null" ctors)
  let typeDefs ← names.mapM fun n => parse s!"def {n} : Type := {fam} {fam}.Tag.{n}"
  pure ([tagCmd, famCmd] ++ typeDefs.toList)

/-- Elaborate one command, updating the state and adding messages. -/
partial def elabCommand (cmd : Syntax) : StateM (CommandState R) Unit := do
  let s ← get
  let report (sev : Severity) (info : SourceInfo) (text : String) : StateM (CommandState R) Unit :=
    modify fun s => { s with messages := s.messages.push { info, severity := sev, text } }
  -- the finalizer of a foreign pointer type (for a foreign function's result)
  let finOf (t : Term R) : String := match (Term.spine t).1 with
    | .const n _ => ((s.foreignTypes.find? (·.1 == n)).map (·.2)).getD ""
    | _ => ""
  let addDeclChecked (name : Name) (levelParams : List Name) (ty : Term R) (val : Option (Term R))
      (impl : Option (Term R) := none) := do
    match addDecl s.globals { name, levelParams, type := ty, value := val, impl } with
    | .ok g => modify fun s => { s with globals := g }
    | .error e => report .error cmd.info s!"kernel rejected {name}: {e}"
  match cmd.kind with
  | "command.def" | "command.axiom" =>
    let name := ((cmd.getArg 1).getId?).getD "_"
    let levelParams := ((cmd.getArg 2).getArg 1).args.toList.filterMap Syntax.getId?
    let binders := (cmd.getArg 3).args
    let typeStx := (cmd.getArg 4).args[1]?
    let valStx := if cmd.isOfKind "command.def" then some (cmd.getArg 6) else none
    if s.globals.contains name then
      report .error (cmd.getArg 1).info s!"'{name}' has already been declared"
    else match runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals (elabDeclTerms binders typeStx valStx cmd.info) levelParams with
      | .ok ((ty, val), hv) =>
        modify fun s => { s with hovers := s.hovers ++ hv }
        addDeclChecked name levelParams ty val
      | .error e => report .error e.info e.msg
  | "command.partial" | "command.mutual" =>
    let defs := if cmd.isOfKind "command.partial" then #[cmd.getArg 1] else (cmd.getArg 1).args
    if cmd.isOfKind "command.mutual" && defs.all (·.isOfKind "command.inductive") then
      match mutualInductive s.tables defs with
      | .ok cmds => for c in cmds do elabCommand c
      | .error e => report .error cmd.info e
      return
    let typeOf (d : Syntax) : Option Syntax :=
      if d.isOfKind "command.defEqns" then some ((d.getArg 4).getArg 1) else (d.getArg 4).args[1]?
    -- the signatures first, as axioms (so the bodies can call each other)
    let mut g := s.globals
    let mut sigs : Array (Syntax × Name × List Name) := #[]
    for d in defs do
      unless d.isOfKind "command.def" || d.isOfKind "command.defEqns" do
        report .error d.info "only definitions can be partial"
        return
      let name := ((d.getArg 1).getId?).getD "_"
      let levelParams := ((d.getArg 2).getArg 1).args.toList.filterMap Syntax.getId?
      if g.contains name then
        report .error (d.getArg 1).info s!"'{name}' has already been declared"
        return
      let some tyStx := typeOf d | report .error d.info "a partial definition needs a type"; return
      match runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) g (elabDeclTerms (d.getArg 3).args (some tyStx) none d.info) levelParams with
      | .ok ((ty, _), _) =>
        unless inhabitedTy g 0 32 (eval g [] (ty.instLevels levelParams (levelParams.map fun _ => .zero))) do
          report .error (d.getArg 1).info s!"partial definition {name}: its type must be visibly inhabited (the kernel treats {name} as an axiom)"
          return
        g := g.insert { name, levelParams, type := ty, value := none }
        sigs := sigs.push (d, name, levelParams)
      | .error e => report .error e.info e.msg; return
    -- then the bodies, checked by the kernel and kept as the implementations
    for (d, name, levelParams) in sigs do
      let body : ElabM R (Term R) :=
        if d.isOfKind "command.defEqns" then do
          let (_, v, _) ← elabDefEqns name d (isPartial := true)
          pure v
        else do
          let (_, v) ← elabDeclTerms (d.getArg 3).args (typeOf d) (some (d.getArg 6)) d.info
          pure (v.getD (.const name []))
      match runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) g body levelParams with
      | .ok (v, hv) =>
        modify fun s => { s with hovers := s.hovers ++ hv }
        match addPartialImpl g name v with
        | .ok g' => g := g'
        | .error e => report .error d.info s!"kernel rejected {name}: {e}"; return
      | .error e => report .error e.info e.msg; return
    modify fun s => { s with globals := g }
  | "command.check" =>
    let r := runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals do
      let (t, ty) ← Elab.infer {} (cmd.getArg 1)
      solveSortConstraints
      let t ← zonk 0 t
      let ty ← zonk 0 (quote (← getGlobals) 0 ty)
      -- an inferred `fun` carries its type as an annotation; don't print it twice
      let t := match t with
        | .ann tm _ => tm
        | t => t
      pure s!"{t.pretty} : {ty.pretty}"
    match r with
    | .ok text => report .info cmd.info text
    | .error e => report .error e.info e.msg
  | "command.reduce" =>
    let r := runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals do
      let (t, _) ← Elab.infer {} (cmd.getArg 1)
      solveSortConstraints
      let t ← zonk 0 t
      ensureNoMVars t
      pure (nf (← getGlobals) t).pretty
    match r with
    | .ok text => report .info cmd.info text
    | .error e => report .error e.info e.msg
  | "command.defEqns" =>
    let name := ((cmd.getArg 1).getId?).getD "_"
    let levelParams := ((cmd.getArg 2).getArg 1).args.toList.filterMap Syntax.getId?
    if s.globals.contains name then
      report .error (cmd.getArg 1).info s!"'{name}' has already been declared"
    else
      let pats := (cmd.getArg 5).args.toList.filterMap fun a => (a.getArg 1).args[0]?
      let coinductiveOf? : Option (List (Name × Bool)) :=
        if pats.all (·.isOfKind "term.dotIdent") then
          s.coinductives.findSome? fun (_, obs) =>
            if pats.all (fun p => obs.any (·.1 == ((p.getArg 1).getId?).getD "_")) then some obs else none
        else none
      let r := match coinductiveOf? with
        | some obs => runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals (do let (t, v) ← elabCopatterns name cmd obs; pure (t, v, none)) levelParams
        | none => runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals (elabDefEqns name cmd) levelParams
      match r with
      | .ok ((ty, val, impl), hv) =>
        modify fun s => { s with hovers := s.hovers ++ hv }
        addDeclChecked name levelParams ty (some val) impl
      | .error e => report .error e.info e.msg
  | "command.coinductive" =>
    let name := ((cmd.getArg 1).getId?).getD "_"
    let levelParams := ((cmd.getArg 2).getArg 1).args.toList.filterMap Syntax.getId?
    if s.globals.contains name then
      report .error (cmd.getArg 1).info s!"'{name}' has already been declared"
    else
      match runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals (elabCoinductive cmd levelParams) levelParams with
      | .error e => report .error e.info e.msg
      | .ok (decls, obs) =>
        let mut g := s.globals
        for d in decls do
          match addDecl g d with
          | .ok g' => g := g'
          | .error e =>
            report .error cmd.info s!"kernel rejected {d.name}: {e}"
            return
        modify fun s => { s with globals := g, coinductives := s.coinductives ++ [(name, obs)] }
  | "command.class" =>
    let name := ((cmd.getArg 1).getId?).getD "_"
    let levelParams := ((cmd.getArg 2).getArg 1).args.toList.filterMap Syntax.getId?
    if s.globals.contains name then
      report .error (cmd.getArg 1).info s!"'{name}' has already been declared"
    else
      match runElab (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals
          (elabStructure cmd levelParams) levelParams with
      | .error e => report .error e.info e.msg
      | .ok decls =>
        let decls := decls ++ classMethods (decls[0]!) levelParams
        let mut g := s.globals
        for d in decls do
          match addDecl g d with
          | .ok g' => g := g'
          | .error e =>
            report .error cmd.info s!"kernel rejected {d.name}: {e}"
            return
        let (Δ, _) := peelPis (decls[0]!).type
        let outParams := Δ.map fun (_, _, _, A) => match (Term.spine A).1 with
          | .const n _ => n == "outParam"
          | _ => false
        let fields := (cmd.getArg 6).args.toList.filterMap fun f => (f.getArg 1).getId?
        modify fun s => { s with globals := g, classes := { name, outParams, fields } :: s.classes }
  | "command.instance" =>
    let prioOpt := cmd.getArg 1
    let priority := if prioOpt.isNone then 1000 else ((prioOpt.getArg 3).getNat?).getD 1000
    let binders := (cmd.getArg 2).args
    let typeStx := cmd.getArg 4
    -- `:= v` or `where fields` (the branch's items are inline: `cmd[5]` is the keyword)
    let isWhere := (cmd.getArg 5) matches .atom _ "where"
    let body := cmd.getArg 6
    -- `instAddNat` from the identifiers of the type
    let rec idents (stx : Syntax) : List Name := match stx with
      | .ident _ n => [n]
      | .node _ _ as => as.toList.flatMap idents
      | _ => []
    let base := "inst" ++ String.join ((idents typeStx).map fun n => (n.replace "." "").capitalize)
    let name := if !s.globals.contains base then base else
      ((List.range 1000).map (s!"{base}_{·}")).find? (!s.globals.contains ·) |>.getD base
    -- `where f := v …` builds the class's constructor applied to the fields, in order
    let rec headIdent (stx : Syntax) : Option Name :=
      match stx.kind with
      | "term.ident" => (stx.getArg 0).getId?
      | "term.app" => headIdent (stx.getArg 0)
      | "term.paren" => headIdent (stx.getArg 1)
      | _ => none
    let valStx : Except String Syntax :=
      if !isWhere then pure body else do
        let some C := headIdent typeStx | throw "an instance's type must be an application of a class"
        let some info := s.classes.find? (·.name == C) | throw s!"{C} is not a class"
        let given := body.args.toList.map fun f => (((f.getArg 0).getId?).getD "_", f.getArg 2)
        for (x, _) in given do
          unless info.fields.contains x do throw s!"{C} has no field {x}"
        let args ← info.fields.mapM fun x => match given.lookup x with
          | some v => pure (Syntax.node v.info "term.paren" #[.atom {} "(", v, .atom {} ")"])
          | none => throw s!"missing field {x}"
        let head := Syntax.node cmd.info "term.ident" #[.ident cmd.info (C ++ ".mk")]
        pure (if args.isEmpty then head else .node cmd.info "term.app" #[head, .node {} "null" args.toArray])
    match valStx with
    | .error e => report .error cmd.info e
    | .ok valStx =>
      match runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics)
          (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals
          (elabDeclTerms binders (some typeStx) (some valStx) cmd.info) [] with
      | .error e => report .error e.info e.msg
      | .ok (ty, val) =>
        let (_, concl) := peelPis ty
        match (Term.spine concl).1 with
        | .const C _ =>
          if s.classes.any (·.name == C) then
            addDeclChecked name [] ty val
            modify fun s => { s with instances := s.instances.push { name, cls := C, priority } }
          else report .error cmd.info s!"{C} is not a class"
        | _ => report .error cmd.info "an instance's type must be an application of a class"
  | "command.inductive" | "command.structure" =>
    let name := ((cmd.getArg 1).getId?).getD "_"
    let levelParams := ((cmd.getArg 2).getArg 1).args.toList.filterMap Syntax.getId?
    if s.globals.contains name then
      report .error (cmd.getArg 1).info s!"'{name}' has already been declared"
    else
      let elabCmd := if cmd.isOfKind "command.inductive" then elabInductive cmd levelParams
        else elabStructure cmd levelParams
      match runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals elabCmd levelParams with
      | .error e => report .error e.info e.msg
      | .ok decls =>
        let mut g := s.globals
        for d in decls do
          match addDecl g d with
          | .ok g' => g := g'
          | .error e =>
            report .error cmd.info s!"kernel rejected {d.name}: {e}"
            return
        -- the recursors need the declarations above
        if cmd.isOfKind "command.inductive" then
          let ctors := (cmd.getArg 6).args.toList.filterMap fun c => (c.getArg 1).getId?
          for (withIH, sized) in [(false, false), (true, false), (false, true)] do
            match mkRecursor g name ctors withIH sized with
            | .error e => report .error cmd.info s!"could not generate the recursor: {e}"; return
            | .ok d =>
              match addDecl g d with
              | .ok g' => g := g'
              | .error e =>
                report .error cmd.info s!"kernel rejected {d.name}: {e}\n  {d.type.pretty}"
                return
        modify fun s => { s with globals := g }
  | "command.builtin" =>
    let key := ((cmd.getArg 1).getId?).getD "_"
    let n := ((cmd.getArg 3).getId?).getD "_"
    let known := ["nat", "nat.zero", "nat.succ", "nat.pred", "nat.add", "nat.sub", "nat.mul", "nat.beq", "nat.blt", "string", "memo"]
    if !known.contains key then report .error cmd.info s!"unknown builtin {key}; known: {known}"
    else if !s.globals.contains n then report .error cmd.info s!"unknown declaration {n}"
    else modify fun s => { s with builtins := (key, n) :: s.builtins,
                                  globals := { s.globals with builtins := (key, n) :: s.globals.builtins } }
  | "command.foreignType" =>
    -- an opaque C pointer type; values are released with the finalizer
    let name := ((cmd.getArg 1).getId?).getD "_"
    let fin := if (cmd.getArg 2).isNone then "" else (((cmd.getArg 2).getArg 3).getStr?).getD ""
    match addDecl s.globals { name, type := .sort 1, value := none } with
    | .ok g => modify fun s => { s with globals := g, foreignTypes := (name, fin) :: s.foreignTypes }
    | .error e => report .error cmd.info s!"kernel rejected {name}: {e}"
  | "command.importC" =>
    -- bind every function of a C header whose types we can marshal
    let header := ((cmd.getArg 1).getStr?).getD "_"
    let isPure := !(cmd.getArg 2).isNone
    match s.cHeaders header with
    | none => report .error cmd.info s!"{header} was not preprocessed (run through `wiz check` or `wiz run`)"
    | some src =>
      let rec kindOf (t : FFI.CType) (isResult : Bool) : Option Char := match t with
        | .const t => kindOf t isResult
        | .int "_Bool" => some 'b'
        | .int _ => some 'n'
        | .float _ => some 'f'
        | .void => if isResult then some 'v' else none
        | .ptr t => match t with
          | .int "char" | .const (.int "char") => some 's'
          | _ => none
        | .other _ => none
      let tyOf (k : Char) : Term R := match k with
        | 'n' => .const "Nat" []
        | 'f' => .const "Float64" []
        | 's' => .const "String" []
        | 'b' => .const "Bool" []
        | _ => .unit 1
      let w : Term R := .qlit QuantitySyntax.explicitDefault
      let funcs := FFI.parseHeader src
      -- glue code may call these, and needs the header
      let usable := funcs.toList.filterMap fun f => do
        if f.variadic then none
        let ps ← f.params.mapM FFI.GTy.ofC
        pure (f.name, ps, ← FFI.GTy.ofC f.ret)
      modify fun s => { s with cFuncs := usable ++ s.cFuncs, cCode := s.cCode.push s!"#include <{header}>" }
      for f in funcs do
        let name : Name := "C." ++ f.name
        if f.variadic || (← get).globals.contains name then continue
        let (some ks, some rk) := (f.params.mapM (kindOf · false), kindOf f.ret true) | continue
        let res := if isPure then tyOf rk else .app (.const "IO" []) (tyOf rk)
        let ty := ks.foldr (fun k acc => .pi "_" .default w (tyOf k) acc none) res
        let key : Name := s!"extern:{f.name}:{String.mk ks}:{rk}:{if isPure then "pure" else "io"}:{header}:"
        match addDecl (← get).globals { name, type := ty, value := none } with
        | .ok g => modify fun s => { s with builtins := (key, name) :: s.builtins,
                                            globals := { g with builtins := (key, name) :: g.builtins } }
        | .error e => report .error cmd.info s!"kernel rejected {name}: {e}"
  | "command.glue" =>
    -- a foreign function defined by checked C code
    let name := ((cmd.getArg 1).getId?).getD "_"
    let binders := (cmd.getArg 2).args
    let body := ((cmd.getArg 6).getStr?).getD ""
    if s.globals.contains name then report .error (cmd.getArg 1).info s!"'{name}' has already been declared"
    else
      let elabTy := runElab (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals
        (elabDeclTerms binders (some (cmd.getArg 4)) none cmd.info) []
      match elabTy with
      | .error e => report .error e.info e.msg
      | .ok (ty, _) =>
        let names := (binders.flatMap Elab.binderViews).toList.map (·.name)
        let kind (t : Term R) : Option Char := match t with
          | .unit _ => some 'v'
          | t => match (Term.spine t).1 with
            | .const "Nat" _ => some 'n' | .const "UInt64" _ => some 'u' | .const "Float64" _ => some 'f'
            | .const "String" _ => some 's' | .const "Bool" _ => some 'b'
            | .const n _ => if s.foreignTypes.any (·.1 == n) then some 'p' else none
            | _ => none
        let rec gparams : Term R → List (Term R) × Term R
          | .pi _ _ _ A B _ => let (ps, r) := gparams B; (A :: ps, r)
          | t => ([], t)
        let (ps, res) := gparams ty
        let (io, res) := match Term.spine res with
          | (.const "IO" _, [A]) => (true, A)
          | _ => (false, res)
        match ps.mapM kind, kind res with
        | some ks, some rk =>
          if names.length != ks.length then report .error cmd.info "glue: every parameter needs a name" else
          let gty (k : Char) : FFI.GTy := match k with
            | 'f' => .dbl | 's' => .str | 'v' => .void | 'p' => .ptr | _ => .int
          let cty (k : Char) : String := match k with
            | 'f' => "double" | 's' => "const char *" | 'v' => "void" | 'b' => "int" | 'p' => "void *" | _ => "uint64_t"
          let pairs := (names.zip ks).filter (·.2 != 'v')
          match FFI.checkGlue body (pairs.map fun (x, k) => (x, gty k)) s.cFuncs (gty rk) with
          | .error e => report .error (cmd.getArg 6).info s!"glue: {e}"
          | .ok () =>
            let cname := "wiz_glue_" ++ ((C.mangle name).drop 2).toString
            let cparams := ", ".intercalate (pairs.map fun (x, k) => s!"{cty k} {x}")
            let code := s!"static {cty rk} {cname}({if cparams.isEmpty then "void" else cparams}) \{
{body}
}"
            let key : Name := s!"extern:{cname}:{String.mk ks}:{rk}:{if io then "io" else "pure"}::{finOf res}"
            match addDecl s.globals { name, type := ty, value := none } with
            | .ok g =>
              modify fun s => { s with builtins := (key, name) :: s.builtins,
                                       globals := { g with builtins := (key, name) :: g.builtins },
                                       cCode := s.cCode.push code,
                                       cFuncs := (cname, pairs.map (gty ·.2), gty rk) :: s.cFuncs }
            | .error e => report .error cmd.info s!"kernel rejected {name}: {e}"
        | _, _ =>
          let msg := "a glue function's arguments and result must be Nat, UInt64, Float64, String, Bool or Unit (the result may be in IO)"
          report .error cmd.info msg
  | "command.extern" =>
    -- an axiom, bound to a C function: the marshalling follows the Wiz type
    let cname := ((cmd.getArg 1).getStr?).getD "_"
    let header := if (cmd.getArg 2).isNone then "" else (((cmd.getArg 2).getArg 3).getStr?).getD ""
    let name := ((cmd.getArg 3).getId?).getD "_"
    if s.globals.contains name then report .error (cmd.getArg 3).info s!"'{name}' has already been declared"
    else
      let elabTy := runElab (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals
        (elabDeclTerms #[] (some (cmd.getArg 5)) none cmd.info) []
      match elabTy with
      | .error e => report .error e.info e.msg
      | .ok (ty, _) =>
        let kind (t : Term R) : Option Char := match t with
          | .unit _ => some 'v'
          -- a type variable: any Wiz value, passed as it is
          | .var _ => some 'w'
          | t => match (Term.spine t).1 with
            | .const "Nat" _ => some 'n'
            | .const "UInt64" _ => some 'u'
            | .const "Float64" _ => some 'f'
            | .const "String" _ => some 's'
            | .const "Bool" _ => some 'b'
            | .const "Bytes" _ | .const "Array" _ | .const "Str" _ | .const "StrMap" _ => some 'w'
            | .var _ => some 'w'
            | .const n _ => if s.foreignTypes.any (·.1 == n) then some 'p' else none
            | _ => none
        let rec params : Term R → List (Term R × Term R) × Term R
          | .pi _ _ q A B _ => let (ps, r) := params B; ((q, A) :: ps, r)
          | t => ([], t)
        let (ps, res) := params ty
        let (io, res) := match Term.spine res with
          | (.const "IO" _, [A]) => (true, A)
          | _ => (false, res)
        -- erased parameters (`{A : Type}`) are passed as ◾ and ignored
        let pkind (qa : Term R × Term R) : Option Char := if qa.1 == .qlit 0 then some 'e' else kind qa.2
        match ps.mapM pkind, kind res with
        | some ks, some rk =>
          let key : Name := s!"extern:{cname}:{String.mk ks}:{rk}:{if io then "io" else "pure"}:{header}:{finOf res}"
          match addDecl s.globals { name, type := ty, value := none } with
          | .ok g => modify fun s => { s with builtins := (key, name) :: s.builtins,
                                              globals := { g with builtins := (key, name) :: g.builtins } }
          | .error e => report .error cmd.info s!"kernel rejected {name}: {e}"
        | _, _ =>
          let msg := "a foreign function's arguments and result must be Nat, UInt64, Float64, String, Bool or Unit (the result may be in IO)"
          report .error cmd.info msg
  | "command.attrMacro" =>
    let k := ((cmd.getArg 3).getId?).getD "_"
    let f := ((cmd.getArg 5).getId?).getD "_"
    let ok := runElab s.globals do
      let (_, ty) ← Elab.infer {} (.node cmd.info "term.ident" #[cmd.getArg 5])
      let macroTy ← evalIn {} (.const "Macro" [])
      unifyAt {} cmd macroTy ty
    match ok with
    | .error e => report .error e.info s!"{f} is not a macro: {e.msg}"
    | .ok () =>
      modify fun s => { s with procMacros := (k, f) :: s.procMacros }
      modify fun s => { s with metaCode := mkMetaCode s.globals s.builtins s.procMacros s.tactics }
  | "command.attrTactic" =>
    let k := ((cmd.getArg 3).getId?).getD "_"
    let f := ((cmd.getArg 5).getId?).getD "_"
    let ok := runElab s.globals do
      let (_, ty) ← Elab.infer {} (.node cmd.info "term.ident" #[cmd.getArg 5])
      let tacticTy ← evalIn {} (.const "Tactic" [])
      unifyAt {} cmd tacticTy ty
    match ok with
    | .error e => report .error e.info s!"{f} is not a tactic: {e.msg}"
    | .ok () =>
      modify fun s => { s with tactics := (k, f) :: s.tactics }
      modify fun s => { s with metaCode := mkMetaCode s.globals s.builtins s.procMacros s.tactics }
  | "command.erase" =>
    let n := ((cmd.getArg 1).getId?).getD "_"
    match s.globals.find? n with
    | none => report .error cmd.info s!"unknown declaration {n}"
    | some d => match eraseDecl s.globals d with
      | .ok e => report .info cmd.info s!"{n} := {e}"
      | .error err => report .error cmd.info s!"cannot erase {n}: {err}"
  | "command.eval" =>
    -- elaborate, erase, run, and read the result back using its type
    let r := runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals do
      let (t, _) ← Elab.infer {} (cmd.getArg 1)
      solveSortConstraints
      let t ← zonk 0 t
      ensureNoMVars t cmd.info
      pure t
    match r with
    | .error e => report .error e.info e.msg
    | .ok t =>
      let ctx : Ctx R := { globals := s.globals }
      let result := do
        let (ty, _) ← Wiz.infer ctx t
        let e ← eraseTop ctx t ty
        let code ← compileReachable s.globals s.builtins (e.globals.toList)
        pure (ty, e, code)
      match result with
      | .ok (ty, e, code) =>
        let v := run code [] e
        report .info cmd.info (readback s.globals s.builtins ty v).pretty
      | .error err => report .error cmd.info s!"cannot run this: {err}"
  | "command.run" =>
    -- like `#eval`, but through the IR, with reference counting, on a checked heap
    let r := runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals do
      let (t, _) ← Elab.infer {} (cmd.getArg 1)
      solveSortConstraints
      let t ← zonk 0 t
      ensureNoMVars t cmd.info
      pure t
    match r with
    | .error e => report .error e.info e.msg
    | .ok t =>
      let ctx : Ctx R := { globals := s.globals }
      let result : Except String (VTy R × RVal) := do
        let (ty, _) ← (Wiz.infer ctx t).mapError toString
        let e ← (eraseTop ctx t ty).mapError toString
        let code ← (compileReachable s.globals s.builtins e.globals.toList).mapError toString
        let decls ← IR.lowerProgram code e
        let (v, _) ← IR.runProgram (decls.map (·.optimize))
        pure (ty, v)
      match result with
      | .ok (ty, v) => report .info cmd.info (readback s.globals s.builtins ty v).pretty
      | .error err => report .error cmd.info s!"#run: {err}"
  | "command.ir" =>
    let n := ((cmd.getArg 1).getId?).getD "_"
    let result : Except String (Array IR.Decl) := do
      let code ← (compileReachable s.globals s.builtins [n]).mapError toString
      IR.lowerProgram code (.global n)
    match result with
    | .ok decls =>
      let mine := decls.filter fun d => d.name == n || d.name.startsWith (n ++ ".")
      report .info cmd.info ("\n".intercalate (mine.toList.map (·.optimize.toString)))
    | .error err => report .error cmd.info s!"#ir: {err}"
  | "command.syntax" | "command.declareSyntaxCat" =>
    match updateTables s.tables cmd with
    | .ok tables => modify fun s => { s with tables }
    | .error msg => report .error cmd.info msg
  | "command.macroRules" =>
    for alt in (cmd.getArg 1).args do
      let lhs := (alt.getArg 1).args[0]?.getD .missing
      let rhs := alt.getArg 3
      unless lhs.kind.startsWith "quote." && rhs.kind.startsWith "quote." do
        report .error alt.info "a macro rule is `| `(cat| pattern) => `(cat| template)`"
        return
      let pattern := lhs.getArg 3
      modify fun s => { s with macros := (pattern.kind, pattern, rhs.getArg 3, []) :: s.macros }
  | "command.notation" | "command.infix" =>
    match notationRule s.tables cmd with
    | .ok (tables, rule) => modify fun s => { s with tables, macros := rule :: s.macros }
    | .error e => report .error cmd.info e
  | k =>
    -- user-defined command syntax: expand a macro, if one applies
    let rules := s.macros.map fun (kind, pattern, template, vars) => ({ kind, pattern, template, vars } : Elab.MacroRule)
    match Elab.expandMacro? rules cmd s.nextScope with
    | some cmd' =>
      modify fun s => { s with nextScope := s.nextScope + 1 }
      elabCommand cmd'
    | none => report .error cmd.info s!"no elaborator for command kind {k}"

end Wiz
