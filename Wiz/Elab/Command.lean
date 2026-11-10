import Wiz.Elab.Recursor
import Wiz.Compiler.Run
import Wiz.Compiler.IRRun
import Wiz.Compiler.Lower
import Wiz.FFI.CParse
import Wiz.FFI.CGlue
import Wiz.Compiler.C
import Wiz.Elab.ProcMacro
import Wiz.Elab.Reflect
import Wiz.Frontend.Parse
import Wiz.Elab.Witness
import Wiz.Elab.Info

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
  | warning
  deriving BEq, Repr, Inhabited

structure Msg where
  info : SourceInfo
  severity : Severity
  text : String
  /-- a stable name for the kind of error (`unknown-identifier`, …), or `""` -/
  code : String := ""
  deriving Repr, Inhabited

def Msg.render (input : String) (m : Msg) : String :=
  let (l, c) := lineCol input m.info.start
  let sev := match m.severity with | .error => "error" | .warning => "warning" | .info => "info"
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
  /-- (HD8) `attribute [macro k] f` for `f : CommandMacro`, and `attribute [deriver C] f`,
  latest first -/
  cmdMacros : List (Name × Name) := []
  derivers : List (Name × Name) := []
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
  /-- (9i) the structs of imported headers, for glue code: fields by spelling -/
  cStructs : List (String × List (String × FFI.GTy)) := []
  /-- C code to emit: header includes and the glue functions -/
  cCode : Array String := #[]
  /-- foreign pointer types and their finalizers -/
  foreignTypes : List (Name × String) := []
  /-- for the language server (stage 11): the info tree of this file (identifiers, expected
  types, tactic states, …), and where each global was declared (its command's range, and
  module; `""` is the main file) -/
  infos : Array (Info R) := #[]
  /-- record the expected type of every checked term (the language server turns it on) -/
  termInfo : Bool := false
  declSites : Std.HashMap Name (SourceInfo × String) := {}
  /-- the module being elaborated (`""` for the main file) -/
  module : String := ""
  /-- the modules whose `builtin` registrations are trusted: the toolchain's library
  (`lib/`). The main file never is, nor a module from a `-I` directory. -/
  trustedModule : String → Bool := fun _ => false
  /-- macro rules, latest first -/
  macros : List (Name × Syntax × Syntax × List Name) := []
  nextScope : Nat := 1000000
  /-- (`runFrontend`) the modules already checked in isolation, with their errors
  (`none` while one is being checked: an import cycle) -/
  checked : Std.HashMap Name (Option (Array Msg)) := {}
  /-- no command has been elaborated into this state yet (it is the initial state, up to
  messages and the info tree) -/
  pristine : Bool := true

/-- `addDecl` with the sorts of the elaborator's `Π`/`Σ` filled in first (`Sorts`). -/
def addDeclSorted (g : Globals R) (d : Decl R) : TCM (Globals R) :=
  addDecl g (d.withSorts g)

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
    (info : SourceInfo) (declName? : Option (Name × SourceInfo × Nat) := none) :
    ElabM R (Term R × Option (Term R)) := do
  let (ctx, tele) ← elabTelescope { info } (binders.flatMap binderViews).toList
  let ty ← match typeStx with
    | some s => pure (← Elab.checkType ctx s).1
    | none => freshMeta ctx "the type of this definition"
  -- (for the language server) the type after the binders, and where ` : T` would go
  if let some (n, ni, at_) := declName? then pushInfo (.decl ni n ctx ty typeStx.isSome at_)
  -- the type's instance problems that are already determined, solved before the body is
  -- checked: an equation stuck on such a hole then computes when it meets the body's type
  -- (`unifyAt`). (The type isn't zonked here: an equation that stays as written lets
  -- `rfl` be `refl` of its sides.)
  while ← synthPending do pure ()
  let val ← valStx.mapM fun s => do Elab.check ctx s (← evalIn ctx ty)
  let ty := tele.foldr (fun (x, bi, q, a) b => Term.pi x bi q a b none) ty
  let val := val.map fun v => tele.foldr (fun (x, _, _, _) b => Term.lam x b) v
  solveSortConstraints
  let ty ← zonk 0 ty
  ensureNoMVars ty info
  let val ← val.mapM (zonk 0)
  if let some v := val then ensureNoMVars v info
  pure (ty, val)

/-- Where a type ascription goes in `def f binders := v`: after the last of the name, the
universe parameters and the binders. -/
def declInsertAt (cmd : Syntax) : Nat :=
  [1, 2, 3].foldl (fun acc i => max acc (cmd.getArg i).info.stop) 0

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
  -- (an index type that is only a phantom tail, `phantomTail`, has one value too)
  unless (← force I) matches .unit _ | .pi .. do
    throwAt info "sized recursion is only supported on non-indexed types (for now)"
  let c1 := ctx.bind x0 vA0
  let q (c : LocalCtx R) (v : Val R) : Term R := quote g c.lvl v
  -- P := fun _ x' => B[x0 := x']   (B is under the x0 binder)
  -- (in `c1`: `B` lives under `x0`, which becomes the inner binder; the rest shift by 2)
  let P : Term R := .lam "_" (.lam x0 (B.lift 2 1))
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
  -- (the hint sits in `y`'s domain, under `j` only)
  let hintT := hint.map fun (n, us, as) => (n, us, as.map (quote g (L + 1)))
  let fTyTm : Term R := .pi "j" .implicit (.qlit 0) (.sizeLt sT)
    (.pi "y" .default (.qlit w) (.mu l (q ctxX I |>.lift 1) (q ctxX D |>.lift 1) (q ctxX idx |>.lift 1) (.var 0) hintT)
      ((Term.app (Term.app ((P.lift (L - c1.lvl)).lift 2) ((q ctxX idx).lift 2)) (.var 0))) none) none
  -- β-reduce `P () y` (the kernel can't infer the type of an applied lambda)
  let fTyTm := quote g L (← evalIn ctxX fTyTm)
  let fValTm : Term R := .lam "j" (.lam "y" (.app (.app (.app (recT.lift 2) (.var 1)) ((q ctxX idx).lift 2)) (.var 0)))
  let ctxL := ctxX.define name (← evalIn ctxX fTyTm) (← evalIn ctxX fValTm)
  -- introduce the remaining arguments
  let mut ctx' := ctxL
  let mut goal := goalP
  let mut vars : List Lvl := [xLvl]
  let mut names : List Name := []
  let n := (clauses.head?.map (·.pats.length)).getD 1
  for k in [1:n] do
    let .pi x _ xq A Bc _ ← force goal | throwAt info s!"{name} takes fewer than {n} arguments"
    let x := if x == "_" then s!"a{k}" else x
    vars := vars ++ [ctx'.lvl]
    names := names ++ [x]
    goal ← instM Bc (Val.var ctx'.lvl)
    if ((Val.toPoly? xq).bind (·.isConst?)) == some 0 then
      ctx' := { ctx' with erasedLvls := ctx'.lvl :: ctx'.erasedLvls }
    ctx' := ctx'.bind x A
  let tree ← compileMatch ctx' vars clauses goal none true
  let body := Term.letE name (.qlit w) fTyTm fValTm (names.foldr .lam tree)
  let F : Term R := .lam "s" (.lam "rec" (.lam "i" (.lam x0 body)))
  let sizeVarT : Term R := .var (c1.lvl - si - 1)
  let sfixT : Term R := .sfix l (q c1 I) (q c1 D) vlev P F sizeVarT (q c1 idx) (.var 0)
  solveSortConstraints
  let val := tele.foldr (fun (x, _, _, _) b => Term.lam x b) (.lam x0 sfixT)
  let fullTy := tele.foldr (fun (x, bi, qq, a) b => Term.pi x bi qq a b none) (Term.pi x0 bi0 q0 A0 B s0)
  let val ← zonk 0 val
  ensureNoMVars val info
  let fullTy ← zonk 0 fullTy  -- (the telescope's holes, solved by now)
  ensureNoMVars fullTy info
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
    let .pi x _ xq A B _ ← force tyv | throwAt tyStx.info s!"{name} takes fewer than {n} arguments"
    let x := if x == "_" then s!"a{i}" else x
    vars := vars ++ [ctx'.lvl]
    names := names ++ [x]
    tyv ← instM B (Val.var ctx'.lvl)
    if ((Val.toPoly? xq).bind (·.isConst?)) == some 0 then
      ctx' := { ctx' with erasedLvls := ctx'.lvl :: ctx'.erasedLvls }
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
  let allParams := (tele.map fun (x, bi, _, _) => (x, bi == .default)).toList
  let rc : Option RecCtx := if recursive then some { fn := name, params, pos, cols := n, allParams } else none
  if let some x := vars.head? then recordMatch cmd.info alts clauses ctx'.types[ctx'.lvl - x - 1]!
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
  let fullTy ← zonk 0 fullTy  -- (the telescope's holes, solved by now)
  ensureNoMVars fullTy info
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

/-- Does the identifier `n` occur anywhere in `stx`? -/
partial def mentionsIdent (n : Name) (stx : Syntax) : Bool :=
  (stx.isOfKind "term.ident" && (stx.getArg 0).getId? == some n) || stx.args.any (mentionsIdent n)

/-- How the fields of the coinductive type `T` sit in its payload (Q4: a small field is
lifted, `descFieldLifts`), read off `T.desc`. -/
def coinductiveLifts (g : Globals R) (T : Name) : List FieldLift :=
  match g.find? (T ++ ".desc") with
  | some { value := some v, type, .. } =>
    let rec strip : Nat → Term R → Term R
      | n + 1, .lam _ b => strip n b
      | _, t => t
    descFieldLifts (strip (peelPis type).1.length v)
  | _ => []

/-- The copattern alternative for observation `o`, if any. -/
def copatternAlt? (alts : List Syntax) (o : Name) : Option Syntax :=
  alts.find? fun a =>
    match (a.getArg 1).args[0]? with
    | some p => p.isOfKind "term.dotIdent" && (p.getArg 1).getId? == some o
    | none => false

/-- Is `rhs` a corecursive call `f e…` (or a bare `f`)? -/
def isCorecCall (name : Name) (rhs : Syntax) : Bool :=
  let h := if rhs.isOfKind "term.app" then rhs.getArg 0 else rhs
  h.isOfKind "term.ident" && (h.getArg 0).getId? == some name

/-- The corecursive case of `elabCopatterns`: `coit`. -/
def elabCopatternsCoit (name : Name) (cmd : Syntax) (obs : List (Name × Bool)) : ElabM R (Term R × Term R) := do
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
  let lifts := coinductiveLifts g T
  let mut comps : List (Term R) := []
  for (o, isRec) in obs, k in [0:obs.length] do
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
      comps := comps ++ [(lifts[k]?.getD .none).wrap (← Elab.check sctx rhs F)]
  -- the index equation: `()` at `Unit`; for a phantom tail (`phantomTail`), `refl`
  let e : Term R ← match ← force I with
    | .unit _ => pure .tt
    | _ => pure (.refl (q sctx.lvl I) (q sctx.lvl i))
  let payload : Term R := comps.foldr .pair (.pair e .tt)
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
  let fullTy ← zonk 0 fullTy  -- (the telescope's holes, solved by now)
  ensureNoMVars fullTy info
  pure (fullTy, val)

/-- **Exercise 4.24.** The non-corecursive case of `elabCopatterns`: `cocon` of the
observations, so `register a s | .head => a | .tail => s` is one cell in front of `s`.

The result type is `ν^sz D i`; its payload is `⟦D⟧ (ν^{s'}) i` for `sz = ↑s'` (or `∞`).
Walk that Σ type: check each observation's right-hand side against the component (a
recursive observation against the nominal type one size down, so its hint survives),
and instantiate the rest with the value. Reject a right-hand side that mentions the
definition itself (guardedness). The payload ends in `((), ())`. -/
def elabCopatternsCocon (name : Name) (cmd : Syntax) (obs : List (Name × Bool)) : ElabM R (Term R × Term R) := do
  let info := cmd.info
  let g ← getGlobals
  let (ctx, tele) ← elabTelescope { info } (((cmd.getArg 3).args.flatMap binderViews)).toList
  let tyStx := (cmd.getArg 4).getArg 1
  let (ty, _) ← Elab.checkType ctx tyStx
  let ty ← zonk ctx.lvl ty
  ensureNoMVars ty info
  let .nu l I D i sz hint ← force (← evalIn ctx ty)
    | throwAt tyStx.info "copatterns need a coinductive result type"
  let some s' := sizePred? sz
    | throwAt tyStx.info s!"a copattern definition builds a value of size ↑s or ∞, not {← showVal ctx sz}"
  --<sol
  let alts := (cmd.getArg 5).args.toList
  -- walk the payload's Σ type, one component per observation
  let mut pty : VTy R := vInterp g l I D (nuFamilyAt l I D s') i
  let mut comps : List (Term R) := []
  for (o, isRec) in obs do
    let some alt := copatternAlt? alts o | throwAt info s!"missing copattern .{o}"
    let rhs := alt.getArg 3
    if mentionsIdent name rhs then
      throwAt rhs.info s!"the observation .{o} must be a corecursive call of {name} (guardedness)"
    let .sigma _ _ A B _ ← force pty | throwAt info "internal error: observation type"
    -- a recursive observation: the same nominal type, one size down
    let A := if isRec then .nu l I D i s' hint else A
    -- (Q4) a lifted field (`ULift A'`, made by the elaborator): check against the
    -- field's own type, and box it
    let (A, lifted) ← match isRec, ← force A with
      | false, .ulift _ A' => pure (A', true)
      | _, _ => pure (A, false)
    let c ← Elab.check ctx rhs A
    let c := if lifted then .up c else c
    comps := comps ++ [c]
    pty ← instM B (← evalIn ctx c)
  -- the index equation: `()` at `Unit`; for a phantom tail (`phantomTail`), `refl`
  let e : Term R ← match ← force I with
    | .unit _ => pure .tt
    | _ => pure (.refl (quote g ctx.lvl I) (quote g ctx.lvl i))
  let payload : Term R := comps.foldr .pair (.pair e .tt)
  let val := tele.foldr (fun (x, _, _, _) b => Term.lam x b) (Term.cocon payload)
  let fullTy := tele.foldr (fun (x, bi, qq, a) b => Term.pi x bi qq a b none) ty
  let val ← zonk 0 val
  ensureNoMVars val info
  let fullTy ← zonk 0 fullTy  -- (the telescope's holes, solved by now)
  ensureNoMVars fullTy info
  pure (fullTy, val)
  --|ex
  --| sorry
  --sol>

/-- Copatterns: `def f binders : T args | .obs => rhs …` for a coinductive `T`
compiles to `coit`. The state is the tuple of the explicit binders; a recursive
observation must be a corecursive call `f e…` (that is the guardedness condition),
whose arguments become the next state.

When no observation is corecursive (`register a s | .head => a | .tail => s`), the
definition is not recursive at all: it compiles to `cocon` of the observations, one
cell in front of the given streams, and `f` may not occur on any right-hand side. -/
def elabCopatterns (name : Name) (cmd : Syntax) (obs : List (Name × Bool)) : ElabM R (Term R × Term R) := do
  let alts := (cmd.getArg 5).args.toList
  for (o, _) in obs do
    if (copatternAlt? alts o).isNone then throwAt cmd.info s!"missing copattern .{o}"
  let corecursive := obs.any fun (o, isRec) =>
    isRec && ((copatternAlt? alts o).map fun a => isCorecCall name (a.getArg 3)).getD false
  if corecursive then elabCopatternsCoit name cmd obs else elabCopatternsCocon name cmd obs

/-- Run the elaborator; also returns the info tree it recorded (even after an error). -/
def runElabH (g : Globals R) (x : ElabM R α) (levelParams : List Name := [])
    (macros : List (Name × Syntax × Syntax × List Name) := []) (builtins : List (Name × Name) := [])
    (procMacros : List (Name × Name) := []) (tactics : List (Name × Name) := [])
    (metaCode : Thunk (Except String Code) := Thunk.pure (.ok {}))
    (classes : List ClassInfo := []) (instances : Array InstanceInfo := #[]) (termInfo : Bool := false) :
    Except (ElabError R) α × Array (Info R) :=
  -- macros and tactics run against the globals as they are when this command starts
  let compileCode (roots : List Name) := match metaCode.get with
    | .ok c => if roots.all c.contains then .ok c
      else (compileReachable g builtins roots (externImpls := false)).mapError (s!"cannot compile the environment: {·}")
    | .error e => .error e
  let runProcMacro f stx scope := do Elab.runProcMacro (← compileCode [f, "Macro.run"]) f stx scope (macroEnv g)
  let kernelInfer (ctx : Ctx R) (t : Term R) := (Wiz.infer ctx t).map (·.1) |>.mapError toString
  -- (13b) structures with a constructor private to another module don't unfold here
  match x.run { globals := g.elabView, levelParams, macros, builtins, procMacros, runProcMacro, tactics, compileCode,
                kernelInfer, classes, instances, termInfo } with
  | .ok (a, st) => (.ok a, finishInfos st)
  | .error e => (.error e, (e.state?.map finishInfos).getD #[])

def runElab (g : Globals R) (x : ElabM R α) (levelParams : List Name := [])
    (macros : List (Name × Syntax × Syntax × List Name) := []) (builtins : List (Name × Name) := [])
    (procMacros : List (Name × Name) := []) (tactics : List (Name × Name) := [])
    (metaCode : Thunk (Except String Code) := Thunk.pure (.ok {}))
    (classes : List ClassInfo := []) (instances : Array InstanceInfo := #[]) : Except (ElabError R) α :=
  (runElabH g x levelParams macros builtins procMacros tactics metaCode classes instances).1

/-- The erased code of the registered macros and tactics (and what they reach), on demand. -/
def mkMetaCode (g : Globals R) (builtins procMacros tactics : List (Name × Name)) (more : List Name := []) :
    Thunk (Except String Code) :=
  Thunk.mk fun _ =>
    let roots := "TacticM.run" :: "Macro.run" :: (procMacros ++ tactics).map (·.2) ++ more
    (compileReachable g builtins roots (externImpls := false)).mapError (s!"cannot compile the macros and tactics: {·}")

/-- The method functions of a class `C` (from its structure declaration):
`C.f : {Δ} → [self : C Δ] → F`, the field `f` of `self`, where earlier fields in `F`
become projections of `self`. With `selfBi := .default`, the projection functions of a
structure `S`: `S.f : {Δ} → (self : S Δ) → F` (`Signal.map BitVec.toNat s`). Erased
fields get none. -/
def classMethods (sDecl : Decl R) (levelParams : List Name)
    (selfBi : BinderInfo := .instImplicit) : List (Decl R) := Id.run do
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
    let type := implicitΔ.foldr (fun (y, bi, q, B) acc => .pi y bi q B acc none) (.pi "self" selfBi w Capp A' none)
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

/-- Is a `builtin key := d` registration well formed? Numerals and the native operations
need the shapes they assume: `nat` a type, `nat.zero : N`, `nat.succ : N → N`, the
operations `N → N → N` (or `N → N → B` for the comparisons), each a definition (when an
argument isn't a literal, the definition computes). Otherwise the kernel's numerals
would be ill-typed or stuck (`builtin nat := E` for an empty `E` crashed the checker). -/
def builtinShapeError (g : Globals R) (key : Name) (d : Decl R) : Option String :=
  let rec doms : Term R → List (Term R) × Term R
    | .pi _ _ _ a b _ => let (as, r) := doms b; (a :: as, r)
    | t => ([], t)
  let isN (N : Name) : Term R → Bool
    | .const c [] => c == N
    | _ => false
  if key == "nat" || key == "string" then
    match d.type, d.value.map (eval g []) with
    | .sort _, some (.mu _ _ _ _ _ (some (T, _, _))) => if T == d.name then none else some "it must be an inductive type"
    | _, _ => some "it must be an inductive type"
  else if key == "memo" then none
  else match g.builtins.lookup "nat" with
    | none => some "register `builtin nat := …` first"
    | some N =>
      let (as, r) := doms d.type
      let arity := natOpArity key
      -- numerals unfold through `nat.zero` and `nat.succ`: they must be `N`'s own
      -- constructors, not definitions that only have their types
      let rec isCtor : Term R → Bool
        | .lam _ b => isCtor b
        | .con _ => true
        | _ => false
      if d.value.isNone then some "it must be a definition"
      else if as.length != arity || !as.all (isN N) then
        some s!"it must take {arity} argument{if arity == 1 then "" else "s"} of type {N}"
      else if (key == "nat.zero" || key == "nat.succ") && !(d.inline && (d.value.map isCtor).getD false) then
        some s!"it must be a constructor of {N}"
      else if !(key == "nat.beq" || key == "nat.blt") && !isN N r then some s!"its result must have type {N}"
      else none

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
    if (c.getArg 4).args.isEmpty then c.setArg 4 (.node {} "null" #[.atom {} ":", self]) else c
  let famCmd := famFrame.setArg 6 (.node {} "null" ctors)
  let typeDefs ← names.mapM fun n => parse s!"def {n} : Type := {fam} {fam}.Tag.{n}"
  pure ([tagCmd, famCmd] ++ typeDefs.toList)

/-- (13b) Does a `structure` command say `private mk ::` after `where`? -/
def structurePrivateMk (cmd : Syntax) : Bool :=
  let spec := (cmd.getArg 5).getArg 1
  !spec.args.isEmpty && !(spec.getArg 0).args.isEmpty

/-- (13b) The fields (observations) of a `structure` or `coinductive` command marked
`private`. -/
def privateFields (cmd : Syntax) : List Name :=
  (cmd.getArg 6).args.toList.filterMap fun f =>
    if (f.getArg 0).args.isEmpty then none else (f.getArg 2).getId?

/-- Elaborate one command, updating the state and adding messages. -/
partial def elabCommand (cmd : Syntax) : StateM (CommandState R) Unit := do
  -- (13b) privacy is per module: the globals know which one is being elaborated
  modify fun s => if s.globals.module == s.module then s else { s with globals := { s.globals with module := s.module } }
  let s ← get
  let report (sev : Severity) (info : SourceInfo) (text : String) : StateM (CommandState R) Unit :=
    modify fun s => { s with messages := s.messages.push { info, severity := sev, text } }
  let reportErr (e : ElabError R) : StateM (CommandState R) Unit :=
    modify fun s => { s with messages := s.messages.push { info := e.info, severity := .error, text := e.msg, code := e.code } }
  let addInfos (is : Array (Info R)) : StateM (CommandState R) Unit :=
    unless is.isEmpty do modify fun s => { s with infos := s.infos ++ is }
  -- the finalizer of a foreign pointer type (for a foreign function's result)
  let finOf (t : Term R) : String := match (Term.spine t).1 with
    | .const n _ => ((s.foreignTypes.find? (·.1 == n)).map (·.2)).getD ""
    | _ => ""
  -- how a foreign function's parameter or result is marshalled (stage 9a, `ExternSig`)
  let ffiKind (t : Term R) : Option Char := match t with
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
      | .const n _ =>
        if s.foreignTypes.any (·.1 == n) then some 'p'
        -- a Wiz data type (`UIntN w`): the value as it is, for runtime natives
        else if (s.globals.find? n).any (·.value.isSome) then some 'w' else none
      | _ => none
  -- the parameters and result of a function type, and whether the result is in `IO`
  let rec ffiParams : Term R → List (Term R × Term R) × Term R
    | .pi _ _ q A B _ => let (ps, r) := ffiParams B; ((q, A) :: ps, r)
    | t => ([], t)
  let ffiIO (res : Term R) : Bool × Term R := match Term.spine res with
    | (.const "IO" _, [A]) => (true, A)
    | _ => (false, res)
  -- (9g) a function that C calls: Wiz values come in (`n u f s b p w`) and go out
  -- (`n u f s b v w`); none erased, none a callback
  let ffiCallSig (ty : Term R) : Option RVal.CallbackSig := do
    let (ps, res) := ffiParams ty
    let (io, res) := ffiIO res
    let ks ← ps.mapM fun (q, A) => if q == .qlit 0 then none else
      match ffiKind A with
      | some 'v' => none
      | k => k
    let rk ← match ffiKind res with
      | some 'p' => none
      | k => k
    pure { params := ks, result := rk, io }
  -- (9i) the C struct a Wiz structure stands for (`c_struct`), as a marshalling kind
  let structKind? (n : Name) : Option RVal.FKind :=
    (s.builtins.find? fun (k, x) => x == n && k.startsWith "cstruct:").bind fun (k, _) =>
      (RVal.FKind.parseOne (k.drop 8).toString.toList).map (·.1)
  -- (HD8) the code of the registered macros, tactics and derivers
  let remakeMetaCode : StateM (CommandState R) Unit := modify fun s =>
    let more := if s.cmdMacros.isEmpty && s.derivers.isEmpty then []
      else "CommandMacro.run" :: (s.cmdMacros ++ s.derivers).map (·.2)
    { s with metaCode := mkMetaCode s.globals s.builtins s.procMacros s.tactics more }
  let metaCodeFor (f : Name) (runner : Name := "CommandMacro.run") : Except String Code := match s.metaCode.get with
    | .ok c => if c.contains f && c.contains runner then .ok c
      else (compileReachable s.globals s.builtins [f, runner] (externImpls := false)).mapError (s!"cannot compile {f}: {·}")
    | .error e => .error e
  -- elaborate the commands a command macro or deriver produced
  let elabExpansion (what : String) (r : Except String (Array Syntax × Nat)) (info : SourceInfo) :
      StateM (CommandState R) Unit := do
    match r with
    | .error e => report .error info s!"{what}: {e}"
    | .ok (cmds, next) =>
      modify fun s => { s with nextScope := next }
      for c in cmds do elabCommand c
  -- `deriving C` for the type `T`: run `C`'s deriver
  let derive (C T : Name) (info : SourceInfo) : StateM (CommandState R) Unit := do
    let s ← get
    match s.derivers.lookup C with
    | none => report .error info s!"no deriver for {C} (register one with `attribute [deriver {C}] f`)"
    | some f =>
      let r := do Elab.runDeriver (← metaCodeFor f) f T info s.nextScope (macroEnv s.globals)
      elabExpansion s!"deriving {C} for {T}" r info
  let derivingClause (stx : Syntax) (T : Name) : StateM (CommandState R) Unit := do
    unless stx.isNone do
      for c in (stx.getArg 1).args do
        if let some C := c.getId? then derive C T c.info
  let addDeclChecked (name : Name) (levelParams : List Name) (ty : Term R) (val : Option (Term R))
      (impl : Option (Term R) := none) := do
    match addDeclSorted s.globals { name, levelParams, type := ty, value := val, impl } with
    | .ok g => modify fun s => { s with globals := g }
    | .error e => report .error cmd.info s!"kernel rejected {name}: {e}"
  match cmd.kind with
  | "command.private" =>
    -- (13b) every name the command declares is private to this module
    let before := s.globals.order.size
    elabCommand (cmd.getArg 1)
    modify fun s =>
      let added := s.globals.order.extract before s.globals.order.size
      { s with globals := { s.globals with
          privates := added.foldl (fun m n => m.insert n s.module) s.globals.privates } }
  | "command.def" | "command.axiom" =>
    let name := ((cmd.getArg 1).getId?).getD "_"
    let levelParams := ((cmd.getArg 2).getArg 1).args.toList.filterMap Syntax.getId?
    let binders := (cmd.getArg 3).args
    let typeStx := (cmd.getArg 4).args[1]?
    let valStx := if cmd.isOfKind "command.def" then some (cmd.getArg 6) else none
    if s.globals.contains name then
      report .error (cmd.getArg 1).info s!"'{name}' has already been declared"
    else match runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) (termInfo := s.termInfo) s.globals (elabDeclTerms binders typeStx valStx cmd.info (declName? := some (name, (cmd.getArg 1).info, declInsertAt cmd))) levelParams with
      | (.ok (ty, val), hv) =>
        addInfos hv
        addDeclChecked name levelParams ty val
      | (.error e, hv) => addInfos hv; reportErr e
  | "command.partial" | "command.mutual" =>
    -- each definition, with the witness written for it (`partial (default := w) def …`)
    let unwrap (d : Syntax) : Syntax × Option Syntax :=
      if d.isOfKind "command.partial" then
        (d.getArg 2, if (d.getArg 1).isNone then none else some ((d.getArg 1).getArg 3))
      else (d, none)
    let members := if cmd.isOfKind "command.partial" then #[unwrap cmd] else (cmd.getArg 1).args.map unwrap
    let defs := members.map (·.1)
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
    for (d, wStx) in members do
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
      | (.ok (ty, _), _) =>
        -- the kernel takes `name : ty` only with a witness of `ty`: the one written, or
        -- one the elaborator finds
        let findW : ElabM R (Option (Term R)) := match wStx with
          | some w => do
            let t ← Elab.check {} w (← evalIn {} ty)
            solveSortConstraints
            let t ← zonk 0 t
            ensureNoMVars t w.info
            pure (some t)
          | none => findWitness ty
        let w ← match runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) g findW levelParams with
          | .ok (some w) => pure w
          | .ok none =>
            report .error (d.getArg 1).info s!"partial definition {name}: no witness found for its type {ty.pretty}; give one with `partial (default := w) def {name} …` (the kernel takes {name} only if its type is inhabited)"
            return
          | .error e => report .error e.info e.msg; return
        match addPartialDecl g (Decl.withSorts g { name, levelParams, type := ty, value := none, witness := some w }) with
        | .ok g' => g := g'
        | .error e => report .error (d.getArg 1).info s!"kernel rejected {name}: {e}"; return
        sigs := sigs.push (d, name, levelParams)
      | (.error e, _) => reportErr e; return
    -- then the bodies, checked by the kernel and kept as the implementations
    for (d, name, levelParams) in sigs do
      let body : ElabM R (Term R) :=
        if d.isOfKind "command.defEqns" then do
          let (_, v, _) ← elabDefEqns name d (isPartial := true)
          pure v
        else do
          let (_, v) ← elabDeclTerms (d.getArg 3).args (typeOf d) (some (d.getArg 6)) d.info
          pure (v.getD (.const name []))
      match runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) (termInfo := s.termInfo) g body levelParams with
      | (.ok v, hv) =>
        addInfos hv
        let v := match g.find? name with
          | some d => Sorts.value g #[] [] v (eval g [] d.type)
          | none => v
        match addPartialImpl g name v with
        | .ok g' => g := g'
        | .error e => report .error d.info s!"kernel rejected {name}: {e}"; return
      | (.error e, hv) => addInfos hv; reportErr e; return
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
      let coinductiveOf? : Option (Name × List (Name × Bool)) :=
        if pats.all (·.isOfKind "term.dotIdent") then
          s.coinductives.findSome? fun (T, obs) =>
            if pats.all (fun p => obs.any (·.1 == ((p.getArg 1).getId?).getD "_")) then some (T, obs) else none
        else none
      -- (13b) copatterns define every observation: not outside the module of a private one
      if let some (T, obs) := coinductiveOf? then
        if let some (o, m) := obs.findSome? fun (o, _) => (s.globals.privateTo? (T ++ "." ++ o)).map (o, ·) then
          report .error cmd.info (s!"'{T}.{o}' is private to module {m}: a {T} can't be defined by " ++
            "copatterns outside it")
          return
      let r := match coinductiveOf?.map (·.2) with
        | some obs => runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) (termInfo := s.termInfo) s.globals (do let (t, v) ← elabCopatterns name cmd obs; pure (t, v, none)) levelParams
        | none => runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) (termInfo := s.termInfo) s.globals (elabDefEqns name cmd) levelParams
      match r with
      | (.ok (ty, val, impl), hv) =>
        addInfos hv
        addDeclChecked name levelParams ty (some val) impl
      | (.error e, hv) => addInfos hv; reportErr e
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
          match addDeclSorted g d with
          | .ok g' => g := g'
          | .error e =>
            report .error cmd.info s!"kernel rejected {d.name}: {e}"
            return
        -- (13b) private observations: private to this module with the coconstructor
        -- `T.mk`, and elsewhere `T` is opaque (`Globals.elabView`), so a value of it is
        -- neither observed nor built except through the module's own definitions
        let privObs := privateFields cmd
        unless privObs.isEmpty do
          let names := privObs.map (name ++ "." ++ ·) ++ [name ++ ".mk"]
          g := { g with privates := names.foldl (fun m n => m.insert n s.module) g.privates,
                        opaques := g.opaques.insert name s.module }
        modify fun s => { s with globals := g, coinductives := s.coinductives ++ [(name, obs)] }
  | "command.class" =>
    let name := ((cmd.getArg 1).getId?).getD "_"
    let levelParams := ((cmd.getArg 2).getArg 1).args.toList.filterMap Syntax.getId?
    if s.globals.contains name then
      report .error (cmd.getArg 1).info s!"'{name}' has already been declared"
    else if let some f := (cmd.getArg 6).args.find? fun f => !(f.getArg 0).args.isEmpty then
      report .error f.info "a class's methods can't be private (make the class private instead)"
    else
      match runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals
          (elabStructure cmd levelParams) levelParams with
      | .error e => report .error e.info e.msg
      | .ok decls =>
        let decls := decls ++ classMethods (decls[0]!) levelParams
        let mut g := s.globals
        for d in decls do
          match addDeclSorted g d with
          | .ok g' => g := g'
          | .error e =>
            report .error cmd.info s!"kernel rejected {d.name}: {e}"
            return
        let (Δ, _) := peelPis (decls[0]!).type
        let outParams := Δ.map fun (_, _, _, A) => match (Term.spine A).1 with
          | .const n _ => n == "outParam"
          | _ => false
        let fields := (cmd.getArg 6).args.toList.filterMap fun f => (f.getArg 2).getId?
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
    -- (HD8) named after the conclusion of a Π-type (as derivers write them), without macro scopes
    let rec concl (stx : Syntax) : Syntax :=
      if stx.isOfKind "term.depArrow" then concl (stx.getArg 2) else stx
    let base := "inst" ++ String.join ((idents (concl typeStx)).map fun n => ((stripScope n).replace "." "").capitalize)
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
    -- the universe names in the binders and the type are the instance's universe
    -- parameters (an instance has no `.{u}` of its own; derivers write `Type u`)
    let rec levelNames (stx : Syntax) : List Name := match stx with
      | .node _ k as =>
        if k == "level.param" then ((stx.getArg 0).getId?).toList
        else as.toList.flatMap levelNames
      | _ => []
    let levelParams := (binders.toList.flatMap levelNames ++ levelNames typeStx).eraseDups
    match valStx with
    | .error e => report .error cmd.info e
    | .ok valStx =>
      match runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics)
          (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals
          (elabDeclTerms binders (some typeStx) (some valStx) cmd.info) levelParams with
      | .error e => report .error e.info e.msg
      | .ok (ty, val) =>
        let (_, concl) := peelPis ty
        match (Term.spine concl).1 with
        | .const C _ =>
          if s.classes.any (·.name == C) then
            addDeclChecked name levelParams ty val
            modify fun s => { s with instances := s.instances.push { name, cls := C, priority } }
          else report .error cmd.info s!"{C} is not a class"
        | _ => report .error cmd.info "an instance's type must be an application of a class"
  | "command.inductive" | "command.structure" =>
    let name := ((cmd.getArg 1).getId?).getD "_"
    let levelParams := ((cmd.getArg 2).getArg 1).args.toList.filterMap Syntax.getId?
    let ctorSpec := ((cmd.getArg 5).getArg 1)
    if s.globals.contains name then
      report .error (cmd.getArg 1).info s!"'{name}' has already been declared"
    else if cmd.isOfKind "command.structure" && !ctorSpec.args.isEmpty &&
        (ctorSpec.getArg 1).getId? != some "mk" then
      report .error (ctorSpec.getArg 1).info s!"a structure's constructor is `mk` (only `private mk ::` can be written)"
    else
      let elabCmd := if cmd.isOfKind "command.inductive" then elabInductive cmd levelParams
        else elabStructure cmd levelParams
      match runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals elabCmd levelParams with
      | .error e => report .error e.info e.msg
      | .ok decls =>
        -- a structure's projection functions `S.f` (unless the name is taken, as `S.mk`)
        let decls := if cmd.isOfKind "command.structure" then
            decls ++ (classMethods (decls[0]!) levelParams .default).filter fun d =>
              !s.globals.contains d.name && !decls.any (·.name == d.name)
          else decls
        let mut g := s.globals
        for d in decls do
          match addDeclSorted g d with
          | .ok g' => g := g'
          | .error e =>
            report .error cmd.info s!"kernel rejected {d.name}: {e}"
            return
        -- the recursors need the declarations above
        if cmd.isOfKind "command.inductive" then
          let ctors := (cmd.getArg 6).args.toList.filterMap fun c => (c.getArg 2).getId?
          -- (indexed families also get `recN`/`casesOnN`, for motives that don't depend
          -- on the scrutinee)
          let indexed := isIndexed g name
          let mut recNames : List Name := []
          for (withIH, sized, nondep) in [(false, false, false), (true, false, false), (false, true, false)] ++
              (if indexed then [(false, false, true), (true, false, true)] else []) do
            match mkRecursor g name ctors withIH sized nondep with
            | .error e => report .error cmd.info s!"could not generate the recursor: {e}"; return
            | .ok d =>
              recNames := recNames ++ [d.name]
              match addDeclSorted g d with
              | .ok g' => g := g'
              | .error e =>
                report .error cmd.info s!"kernel rejected {d.name}: {e}\n  {d.type.pretty}"
                return
          -- (13b) `| private c`: the constructor is private to this module, and so are the
          -- recursors (their cases would hand out a private constructor's fields, and
          -- they are what a `match` compiles to); elsewhere `T` is opaque
          -- (`Globals.elabView`): it isn't matched there, and nothing else converts to it
          let privCtors := (cmd.getArg 6).args.toList.filterMap fun c =>
            if (c.getArg 1).args.isEmpty then none else (c.getArg 2).getId?
          unless privCtors.isEmpty do
            let names := privCtors.map (name ++ "." ++ ·) ++ recNames
            g := { g with privates := names.foldl (fun m n => m.insert n s.module) g.privates,
                          opaques := g.opaques.insert name s.module }
        -- (13b) `private mk ::`: the constructor is private to this module, and elsewhere
        -- the type is opaque (`Globals.elabView`): only its projections read it
        if cmd.isOfKind "command.structure" && structurePrivateMk cmd then
          g := { g with privates := g.privates.insert (name ++ ".mk") s.module,
                        opaques := g.opaques.insert name s.module }
        -- (13b) `private f : A`: the projection `S.f` is private, and elsewhere `S` is
        -- opaque, so the field isn't read through the Σ (`p.1`) either
        let privFields := if cmd.isOfKind "command.structure" then privateFields cmd else []
        unless privFields.isEmpty do
          g := { g with privates := privFields.foldl (fun m f => m.insert (name ++ "." ++ f) s.module) g.privates,
                        opaques := g.opaques.insert name s.module }
        modify fun s => { s with globals := g }
        derivingClause (cmd.getArg 7) name
  | "command.builtin" =>
    let key := ((cmd.getArg 1).getId?).getD "_"
    let n := ((cmd.getArg 3).getId?).getD "_"
    let known := ["nat", "nat.zero", "nat.succ", "nat.pred", "nat.add", "nat.sub", "nat.mul", "nat.beq", "nat.blt", "string", "memo",
      "nat.div", "nat.mod", "nat.pow", "nat.land", "nat.lor", "nat.xor", "nat.shiftLeft", "nat.shiftRight", "nat.log2"]
    if !known.contains key then report .error cmd.info s!"unknown builtin {key}; known: {known}"
    -- one registration per key, and one key per constant: a second `builtin nat.add := K`
    -- would redirect how the first one's constant unfolds (the kernel finds the definition
    -- by key), an assumption that no declaration using it would show
    else if let some m := s.globals.builtins.lookup key then
      report .error cmd.info s!"builtin {key} is already registered (as {m}); a builtin can be registered only once"
    else if let some (k, _) := s.globals.builtins.find? fun (k, m) => m == n && known.contains k then
      report .error cmd.info s!"{n} is already registered as builtin {k}"
    else match s.globals.find? n with
    | none => report .error cmd.info s!"unknown declaration {n}"
    | some d =>
      match builtinShapeError s.globals key d with
      | some e => report .error cmd.info s!"builtin {key} := {n}: {e}"
      | none =>
        -- the toolchain's library is trusted (its registrations are reviewed: README,
        -- "Trusted base"); anywhere else, nothing checks that `n` computes like the native
        -- operation, so the registration is an axiom of whatever depends on `n`
        let trusted := s.trustedModule s.module
        modify fun s => { s with builtins := (key, n) :: s.builtins,
                                 globals := { s.globals with builtins := (key, n) :: s.globals.builtins,
                                                             assumed := if trusted then s.globals.assumed
                                                                        else (key, n) :: s.globals.assumed } }
        unless trusted do
          report .warning cmd.info s!"builtin {key} := {n} is not checked: it is an axiom of every declaration that depends on {n} (see `#print axioms`)"
  | "command.printAxioms" =>
    let n := ((cmd.getArg 2).getId?).getD "_"
    if !s.globals.contains n then report .error (cmd.getArg 2).info s!"unknown declaration {n}"
    else match s.globals.axiomsOf n with
      | [] => report .info cmd.info s!"'{n}' does not depend on any axioms"
      | as =>
        -- (a native implementation is trusted to agree with its definition; proofs
        -- never run it, compiled code does)
        let note := if as.any (·.startsWith "native ") then
          "\n(native: an implementation that compiled code runs, trusted to agree with its definition)" else ""
        report .info cmd.info s!"'{n}' depends on axioms: [{", ".intercalate as}]{note}"
  | "command.foreignType" =>
    -- an opaque C pointer type; values are released with the finalizer
    let name := ((cmd.getArg 1).getId?).getD "_"
    let fin := if (cmd.getArg 2).isNone then "" else (((cmd.getArg 2).getArg 3).getStr?).getD ""
    -- (9i) `(c := "T")`: `T *` in an imported header is this type
    let cty := if (cmd.getArg 3).isNone then [] else [(s!"ctype:{(((cmd.getArg 3).getArg 3).getStr?).getD ""}", name)]
    match addDeclSorted s.globals { name, type := .sort 1, value := none } with
    | .ok g => modify fun s => { s with globals := { g with builtins := cty ++ g.builtins }, builtins := cty ++ s.builtins,
                                        foreignTypes := (name, fin) :: s.foreignTypes }
    | .error e => report .error cmd.info s!"kernel rejected {name}: {e}"
  | "command.importC" =>
    -- bind every function of a C header whose types we can marshal
    let header := ((cmd.getArg 1).getStr?).getD "_"
    let isPure := !(cmd.getArg 2).isNone
    -- (9i) opt-outs: `(no_auto)`, `(skip := "names")`
    let opts := (cmd.getArg 3).args
    let noAuto := opts.any (·.args.size == 3)
    let skips := opts.toList.flatMap fun o => match (o.getArg 3).getStr? with
      | some str => (str.splitOn " ").filter (· ≠ "")
      | none => []
    match s.cHeaders header with
    | none => report .error cmd.info s!"{header} was not preprocessed (run through `wiz check` or `wiz run`)"
    | some src =>
      let tyOf (k : RVal.FKind) (st : CommandState R) : Term R := match k with
        | .k 'n' => .const "Nat" []
        | .k 'f' => .const "Float64" []
        | .k 's' => .const "String" []
        | .k 'b' => .const "Bool" []
        | .k 'y' => .const "Bytes" []
        | .k 'p' => .const "_" []
        | .struct c h fs =>
          let key := s!"cstruct:{(RVal.FKind.struct c h fs).toKey}"
          .const (((st.builtins.find? (·.1 == key)).map (·.2)).getD "_") []
        | _ => .unit 1
      let w : Term R := .qlit QuantitySyntax.explicitDefault
      let (funcs, structs) := FFI.parseHeaderFull src
      -- glue code may call these, and needs the header
      let usable := funcs.toList.filterMap fun f => do
        if f.variadic then none
        let ps ← f.params.mapM FFI.GTy.ofC
        pure (f.name, ps, ← FFI.GTy.ofC f.ret)
      -- (a field glue can't use is `void`: it can't be read, and a local of the struct must be initialised)
      let hstructs := structs.toList.filterMap fun st => st.fields.map fun fs =>
        (st.spelling, fs.map fun (f, t) => (f, (FFI.GTy.ofC t).getD .void))
      let hstructs := hstructs.flatMap fun (sp, fs) => (sp, fs) :: (((structs.find? (·.spelling == sp)).map (·.aliases)).getD []).map (·, fs)
      modify fun s => { s with cFuncs := usable ++ s.cFuncs, cCode := s.cCode.push s!"#include <{header}>",
                               cStructs := hstructs ++ s.cStructs }
      let structOf (sp : String) : Option FFI.CStruct := structs.find? (·.spelling == sp)
      let spellings (sp : String) : List String := sp :: ((structOf sp).map (·.aliases)).getD []
      let skipped (sp : String) : Bool := (spellings sp).any skips.contains
      -- the Wiz name of a C struct: its typedef name if it has one
      let wizName (sp : String) : Name :=
        "C." ++ (match ((structOf sp).map (·.aliases)).getD [] with
          | a :: _ => a
          | [] => sp.replace "struct " "struct_")
      -- (9i) a C struct by value, as a Wiz structure: a `c_struct` declared for it, or one
      -- made here (`C.div_t`, `C.struct_timespec`) when every field can be marshalled
      let rec structFor (sp : String) (fuel : Nat) : StateM (CommandState R) (Option RVal.FKind) := do
        if fuel == 0 || noAuto || skipped (sp) then return none
        let st ← get
        let mine := st.builtins.find? fun (k, _) => k.startsWith "cstruct:" &&
          match RVal.FKind.parseOne (k.drop 8).toString.toList with
          | some (.struct c _ _, _) => (spellings sp).contains c
          | _ => false
        if let some (k, _) := mine then return (RVal.FKind.parseOne (k.drop 8).toString.toList).map (·.1)
        let some { fields := some fs, .. } := structOf sp | return none
        let mut lines : Array String := #[]
        for (f, t) in fs do
          let t := match t with | .const t => t | t => t
          let fty ← match t with
            | .int "_Bool" => pure (some "Bool")
            | .int _ => pure (some "Nat")
            | .float _ => pure (some "Float64")
            | .ptr (.int "char") | .ptr (.const (.int "char")) => pure (some "String")
            | .array (.int c) (some _) | .array (.const (.int c)) (some _) =>
              pure (if c == "char" || c == "unsigned char" || c == "signed char" then some "Bytes" else none)
            | .struct sp' => do
              match ← structFor sp' (fuel - 1) with
              | some k => pure ((← get).builtins.find? (·.1 == s!"cstruct:{k.toKey}") |>.map (·.2))
              | none => pure none
            | _ => pure none
          let some fty := fty | return none
          lines := lines.push s!"  {f} : {fty}"
        let text := s!"c_struct \"{sp}\" (header := \"{header}\") {wizName sp} where\n{"\n".intercalate lines.toList}\n"
        let st ← get
        let some (stx, _) := (parseCommand text.toList.toArray st.tables 0).toOption | return none
        let n0 := st.messages.size
        elabCommand stx
        let st' ← get
        if (st'.messages.extract n0 st'.messages.size).any (·.severity == .error) then
          -- (a field name Wiz can't take, say): leave the struct out
          set { st' with messages := st'.messages.extract 0 n0 }
          return none
        let k := st'.builtins.find? fun (k, x) => x == wizName sp && k.startsWith "cstruct:"
        return k.bind fun (k, _) => (RVal.FKind.parseOne (k.drop 8).toString.toList).map (·.1)
      -- (9i) a pointer to a struct (or to an opaque typedef): a foreign type, the user's
      -- (`foreign_type T (c := "FILE")`) or one made here (no finalizer)
      let ptrFor (sp : String) : StateM (CommandState R) (Option Name) := do
        if noAuto || skipped sp then return none
        let st ← get
        if let some (_, n) := st.builtins.find? fun (k, _) => k.startsWith "ctype:" && (spellings sp).contains (k.drop 6).toString then
          return some n
        let n := wizName sp
        if st.foreignTypes.any (·.1 == n) then return some n
        if st.globals.contains n then return none
        match addDeclSorted st.globals { name := n, type := .sort 1, value := none } with
        | .ok g =>
          let key := s!"ctype:{sp}"
          modify fun s => { s with globals := { g with builtins := (key, n) :: g.builtins }, builtins := (key, n) :: s.builtins,
                                   foreignTypes := (n, "") :: s.foreignTypes }
          return some n
        | .error _ => return none
      let rec kindOf (t : FFI.CType) (isResult : Bool) : StateM (CommandState R) (Option (RVal.FKind × Option Name)) := match t with
        | .const t => kindOf t isResult
        | .int "_Bool" => pure (some (.k 'b', none))
        | .int _ => pure (some (.k 'n', none))
        | .float _ => pure (some (.k 'f', none))
        | .void => pure (if isResult then some (.k 'v', none) else none)
        | .struct sp => do pure ((← structFor sp 8).map (·, none))
        | .ptr t => match t with
          | .int "char" | .const (.int "char") => pure (some (.k 's', none))
          | .struct sp | .const (.struct sp) => do pure ((← ptrFor sp).map fun n => (RVal.FKind.k 'p', some n))
          | _ => pure none
        | _ => pure none
      -- (9i) a read-only buffer and its length (`const void *buf, size_t n`): `Bytes`
      let lenNames := ["n", "__n", "len", "__len", "nbytes", "__nbytes", "length", "__length"]
      let isBuf (t : FFI.CType) : Bool := match t with
        | .ptr (.const .void) | .ptr (.const (.int "unsigned char")) => true
        | _ => false
      for f in funcs do
        let name : Name := "C." ++ f.name
        if f.variadic || (← get).globals.contains name || skips.contains f.name then continue
        -- the parameters, with buffers and their lengths as one
        let names := f.paramNames ++ List.replicate (f.params.length - f.paramNames.length) ""
        let arr := (f.params.zip names).toArray
        let mut ps : Array (Option FFI.CType) := #[]
        let mut i := 0
        while i < arr.size do
          let t := arr[i]!.1
          let isLen := match arr[i + 1]? with
            | some (l, ln) => (match l with | .int _ | .const (.int _) => true | _ => false) && lenNames.contains ln
            | none => false
          if !noAuto && isBuf t && isLen then
            ps := ps.push none; i := i + 2
          else
            ps := ps.push (some t); i := i + 1
        let mut ks : Array (RVal.FKind × Option Name) := #[]
        let mut ok := true
        for p in ps do
          match p with
          | none => ks := ks.push (.k 'y', none)
          | some t => match ← kindOf t false with
            | some k => ks := ks.push k
            | none => ok := false; break
        if !ok then continue
        let some (rk, rn) ← kindOf f.ret true | continue
        let st ← get
        let ty1 (k : RVal.FKind × Option Name) : Term R := match k.2 with
          | some n => .const n []
          | none => tyOf k.1 st
        let res := if isPure then ty1 (rk, rn) else .app (.const "IO" []) (ty1 (rk, rn))
        -- (9i) a foreign pointer result gets its type's finalizer (`foreign_type … (c := …)`)
        let fin := match rn with
          | some n => (List.lookup n (st.foreignTypes : List (Name × String))).getD ""
          | none => ""
        let ty := ks.toList.foldr (fun k acc => .pi "_" .default w (ty1 k) acc none) res
        let key : Name := s!"extern:{f.name}:{String.join (ks.toList.map (·.1.toKey))}:{rk.toKey}:{if isPure then "pure" else "io"}:{header}:{fin}"
        match addDeclSorted st.globals { name, type := ty, value := none } with
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
      let elabTy := runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals
        (elabDeclTerms binders (some (cmd.getArg 4)) none cmd.info) []
      match elabTy with
      | .error e => report .error e.info e.msg
      | .ok (ty, _) =>
        let names := (binders.flatMap Elab.binderViews).toList.map (·.name)
        let kind (t : Term R) : Option RVal.FKind := match t with
          | .unit _ => some (.k 'v')
          | t => match (Term.spine t).1 with
            | .const "Nat" _ => some (.k 'n') | .const "UInt64" _ => some (.k 'u') | .const "Float64" _ => some (.k 'f')
            | .const "String" _ => some (.k 's') | .const "Bool" _ => some (.k 'b')
            | .const n _ => if s.foreignTypes.any (·.1 == n) then some (.k 'p') else structKind? n
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
          let gty (k : RVal.FKind) : FFI.GTy := match k with
            | .k 'f' => .dbl | .k 's' => .str | .k 'v' => .void | .k 'p' => .ptr | .struct c _ _ => .struct c | _ => .int
          let cty (k : RVal.FKind) : String := match k with
            | .k 'f' => "double" | .k 's' => "const char *" | .k 'v' => "void" | .k 'b' => "int" | .k 'p' => "void *"
            | .struct c _ _ => c | _ => "uint64_t"
          let pairs := (names.zip ks).filter (·.2 != .k 'v')
          -- (9i) the structs in scope: the `c_struct`s (their declared fields), and the headers'
          let declared := s.builtins.filterMap fun (key, _) =>
            if !key.startsWith "cstruct:" then none else
            match RVal.FKind.parseOne (key.drop 8).toString.toList with
            | some (.struct c _ fs, _) => some (c, fs.filterMap fun (f, k) => match k with
                | .k 'e' | .k 'y' => none
                | k => some (f, gty k))
            | _ => none
          match FFI.checkGlue body (pairs.map fun (x, k) => (x, gty k)) s.cFuncs (gty rk) (s.cStructs ++ declared) with
          | .error e => report .error (cmd.getArg 6).info s!"glue: {e}"
          | .ok () =>
            let cname := "wiz_glue_" ++ ((C.mangle name).drop 2).toString
            let cparams := ", ".intercalate (pairs.map fun (x, k) => s!"{cty k} {x}")
            let code := s!"static {cty rk} {cname}({if cparams.isEmpty then "void" else cparams}) \{
{body}
}"
            let key : Name := s!"extern:{cname}:{String.join (ks.map (·.toKey))}:{rk.toKey}:{if io then "io" else "pure"}::{finOf res}"
            match addDeclSorted s.globals { name, type := ty, value := none } with
            | .ok g =>
              modify fun s => { s with builtins := (key, name) :: s.builtins,
                                       globals := { g with builtins := (key, name) :: g.builtins },
                                       cCode := s.cCode.push code,
                                       cFuncs := (cname, pairs.map (gty ·.2), gty rk) :: s.cFuncs }
            | .error e => report .error cmd.info s!"kernel rejected {name}: {e}"
        | _, _ =>
          let msg := "a glue function's arguments and result must be Nat, UInt64, Float64, String, Bool, Unit, a foreign type or a c_struct (the result may be in IO)"
          report .error cmd.info msg
  | "command.cStruct" =>
    -- (9i) a Wiz structure standing for a C struct, passed to and from C by value
    let name := ((cmd.getArg 3).getId?).getD "_"
    let header := if (cmd.getArg 2).isNone then "" else (((cmd.getArg 2).getArg 3).getStr?).getD ""
    let ctype := if (cmd.getArg 1).isNone then "wiz_s" ++ ((C.mangle name).drop 1).toString
      else (((cmd.getArg 1).getArg 0).getStr?).getD "_"
    let fields := (cmd.getArg 5).args
    if s.globals.contains name then report .error (cmd.getArg 3).info s!"'{name}' has already been declared"
    else if fields.isEmpty then report .error cmd.info "a c_struct needs at least one field"
    else if ctype.contains ':' || ctype.contains '|' || ctype.contains '<' || header.contains ':' || header.contains '|' then
      report .error cmd.info "c_struct: unexpected characters in the C type or header"
    else
      -- each field's type, on its own (fields may not depend on each other)
      let fieldKind (f : Syntax) : Except (SourceInfo × String) (String × RVal.FKind) := do
        let fname := ((f.getArg 2).getId?).getD "_"
        let q0 := !(f.getArg 1).isNone && ((f.getArg 1).getArg 0 |>.getArg 0).getNat? == some 0
        if q0 then return (fname, .k 'e')
        match runElab (macros := s.macros) (builtins := s.builtins) (classes := s.classes) (instances := s.instances) s.globals
            (elabDeclTerms #[] (some (f.getArg 4)) none f.info) [] with
        | .error e => throw (e.info, s!"c_struct field {fname}: {e.msg} (fields may not depend on other fields)")
        | .ok (ty, _) =>
          let k : Option RVal.FKind := match (Term.spine ty).1 with
            | .const "Nat" _ => some (.k 'n')
            | .const "UInt64" _ => some (.k 'u')
            | .const "Float64" _ => some (.k 'f')
            | .const "String" _ => some (.k 's')
            | .const "Bool" _ => some (.k 'b')
            -- a byte array `char f[N]`: its size comes from the header
            | .const "Bytes" _ => if header != "" then some (.k 'y') else none
            | .const n _ => if s.foreignTypes.any (·.1 == n) then some (.k 'p') else structKind? n
            | _ => none
          match k with
          | some k => pure (fname, k)
          | none => throw (f.info, s!"c_struct field {fname}: a field must be Nat, UInt64, Float64, String, Bool, a foreign type, another c_struct or (with a header) Bytes")
      match fields.toList.mapM fieldKind with
      | .error (info, e) => report .error info e
      | .ok kinds =>
        let parse (text : String) : Option Syntax := match parseCommand text.toList.toArray s.tables 0 with
          | .ok (stx, _) => some stx
          | .error _ => none
        match parse s!"structure {name} where" with
        | none => report .error cmd.info "internal error: c_struct"
        | some frame =>
          let n0 := (← get).messages.size
          elabCommand ((frame.setArg 6 (Syntax.mkNull fields)).setArg 7 (cmd.getArg 6))
          if (← get).messages.extract n0 (← get).messages.size |>.any (·.severity == .error) then return
          let k : RVal.FKind := .struct ctype header kinds
          let code := if header == "" then C.structDefinition ctype kinds else s!"#include <{header}>"
          modify fun s => { s with builtins := (s!"cstruct:{k.toKey}", name) :: s.builtins,
                                   globals := { s.globals with builtins := (s!"cstruct:{k.toKey}", name) :: s.globals.builtins },
                                   cCode := if s.cCode.contains code then s.cCode else s.cCode.push code }
  | "command.extern" =>
    -- an axiom, bound to a C function: the marshalling follows the Wiz type
    let cname := ((cmd.getArg 1).getStr?).getD "_"
    let header := if (cmd.getArg 2).isNone then "" else (((cmd.getArg 2).getArg 3).getStr?).getD ""
    let name := ((cmd.getArg 3).getId?).getD "_"
    if s.globals.contains name then report .error (cmd.getArg 3).info s!"'{name}' has already been declared"
    else
      let elabTy := runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals
        (elabDeclTerms #[] (some (cmd.getArg 5)) none cmd.info) []
      match elabTy with
      | .error e => report .error e.info e.msg
      | .ok (ty, _) =>
        let kind (t : Term R) : Option RVal.FKind := match t with
          | .unit _ => some (.k 'v')
          -- a type variable: any Wiz value, passed as it is
          | .var _ => some (.k 'w')
          | t => match (Term.spine t).1 with
            | .const "Nat" _ => some (.k 'n')
            | .const "UInt64" _ => some (.k 'u')
            | .const "Float64" _ => some (.k 'f')
            | .const "String" _ => some (.k 's')
            | .const "Bool" _ => some (.k 'b')
            | .const "Bytes" _ | .const "Array" _ | .const "Str" _ | .const "StrMap" _ => some (.k 'w')
            | .var _ => some (.k 'w')
            | .const n _ =>
              if s.foreignTypes.any (·.1 == n) then some (.k 'p')
              -- (9i) a structure declared with `c_struct`: the C struct, by value
              else if let some k := structKind? n then some k
              -- a Wiz data type (`UIntN w`): the value as it is, for runtime natives
              else if (s.globals.find? n).any (·.value.isSome) then some (.k 'w') else none
            | _ => none
        let rec params : Term R → List (Term R × Term R) × Term R
          | .pi _ _ q A B _ => let (ps, r) := params B; ((q, A) :: ps, r)
          | t => ([], t)
        let (ps, res) := params ty
        let (io, res) := match Term.spine res with
          | (.const "IO" _, [A]) => (true, A)
          | _ => (false, res)
        -- erased parameters (`{A : Type}`) are passed as ◾ and ignored
        -- a runtime native (`wiz_…`, runtime/wiz.c) takes and returns any other Wiz value
        -- as it is: an opaque type's (`Chan p`, `MVar A`), a closure, a Σ pair (25a)
        let kind (t : Term R) : Option RVal.FKind :=
          match kind t with
          | some k => some k
          | none => if cname.startsWith "wiz_" then some (.k 'w') else none
        -- (9g) a function is passed as a callback: borrowed for the call, or, as a
        -- `Callback T`, owned by the C side (runtime natives take closures as they are)
        let native := cname.startsWith "wiz_"
        let callback? (A : Term R) : Option (Option RVal.FKind) :=
          if native then none else
          match A with
          | .pi .. => some ((ffiCallSig A).map (.callback false ·))
          | A => match Term.spine A with
            | (.const "Callback" _, [T]) => some ((ffiCallSig T).map (.callback true ·))
            | _ => none
        let pkind (qa : Term R × Term R) : Option RVal.FKind :=
          if qa.1 == .qlit 0 then some (.k 'e') else
          match callback? qa.2 with
          | some k => k
          | none => kind qa.2
        match ps.mapM pkind, kind res with
        | some ks, some rk =>
          if !io && ks.any (fun k => match k with | .callback _ c => c.io | _ => false) then
            report .error cmd.info "a foreign function that takes a callback in IO must be in IO itself"
          else
          let key : Name := s!"extern:{cname}:{String.join (ks.map (·.toKey))}:{rk.toKey}:{if io then "io" else "pure"}:{header}:{finOf res}"
          match addDeclSorted s.globals { name, type := ty, value := none } with
          | .ok g => modify fun s => { s with builtins := (key, name) :: s.builtins,
                                              globals := { g with builtins := (key, name) :: g.builtins } }
          | .error e => report .error cmd.info s!"kernel rejected {name}: {e}"
        | _, _ =>
          let msg := "a foreign function's arguments and result must be Nat, UInt64, Float64, String, Bool, Unit, a c_struct, a Wiz data type or a function of those (a callback; the result may be in IO)"
          report .error cmd.info msg
  | "command.export" =>
    -- (9g) a C symbol for a Wiz function: the inverse of `extern`
    let cname := ((cmd.getArg 1).getStr?).getD "_"
    let fStx := cmd.getArg 2
    let f := (fStx.getId?).getD "_"
    match s.globals.find? f with
    | none => report .error fStx.info s!"unknown declaration {f}"
    | some d =>
      -- an optional type, which must be the definition's
      let ty? : Except (ElabError R) (Term R) :=
        if (cmd.getArg 3).isNone then pure d.type else do
          let (ty, _) ← runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals
            (elabDeclTerms #[] (some ((cmd.getArg 3).getArg 1)) none cmd.info) []
          pure ty
      match ty? with
      | .error e => report .error e.info e.msg
      | .ok ty =>
        if !d.levelParams.isEmpty then report .error fStx.info s!"{f} has universe parameters: only closed functions can be exported"
        else if !convTy s.globals #[] (eval s.globals [] d.type) (eval s.globals [] ty) then
          report .error (cmd.getArg 3).info s!"{f} has type {d.type.pretty}, not {ty.pretty}"
        else if !C.isCIdent cname then report .error (cmd.getArg 1).info s!"{cname} is not a C identifier"
        else if s.builtins.any (fun (k, _) => (RVal.ExternSig.ofExportKey? k).any (·.cname == cname)) then
          report .error (cmd.getArg 1).info s!"{cname} is exported already"
        else match ffiCallSig ty with
          | none =>
            report .error cmd.info "an exported function's arguments must be Nat, UInt64, Float64, String, Bool, a foreign pointer or a Wiz data type, and its result one of those (not a foreign pointer) or Unit, maybe in IO"
          | some c =>
            let key : Name := s!"export:{cname}:{String.ofList c.params}:{c.result}:{if c.io then "io" else "pure"}"
            modify fun s => { s with builtins := (key, f) :: s.builtins }
  | "command.attrMacro" =>
    let k := ((cmd.getArg 3).getId?).getD "_"
    let f := ((cmd.getArg 5).getId?).getD "_"
    let hasType (T : Name) := runElab s.globals do
      let (_, ty) ← Elab.infer {} (.node cmd.info "term.ident" #[cmd.getArg 5])
      let macroTy ← evalIn {} (.const T [])
      unifyAt {} cmd macroTy ty
    -- (HD8) a command macro expands one command into several
    let isCommandMacro := k.startsWith "command." && s.globals.contains "CommandMacro" &&
      (hasType "CommandMacro" matches .ok ())
    if isCommandMacro then
      modify fun s => { s with cmdMacros := (k, f) :: s.cmdMacros }
      remakeMetaCode
    else match hasType "Macro" with
    | .error e => report .error e.info s!"{f} is not a macro: {e.msg}"
    | .ok () =>
      modify fun s => { s with procMacros := (k, f) :: s.procMacros }
      remakeMetaCode
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
      remakeMetaCode
  | "command.attrImplementedBy" =>
    -- `attribute [implemented_by g] f`: compiled code runs `g` wherever it would run `f`
    -- (erasure takes `g`'s code for `f`); the kernel and proofs keep `f`'s definition. So
    -- `g` must have `f`'s type (up to conversion), at the same universe levels.
    let impl := ((cmd.getArg 3).getId?).getD "_"
    let getStx? := (cmd.getArg 4).args[0]?
    let fStx := cmd.getArg 6
    let f := (fStx.getId?).getD "_"
    -- the constructor's erased code `λ…. ⟨t f₀ … fₙ₋₁⟩`, with one runtime field `var j`
    let ctorShape? (d : Decl R) : Option (Nat × Nat × Nat × Nat × Nat) := do
      let .ok e := eraseDecl s.globals d | none
      let rec peel : ETerm → Nat × ETerm
        | .lam _ b => let (n, b) := peel b; (n + 1, b)
        | t => (0, t)
      let (n, .obj t fs) := peel e | none
      let live := (List.range fs.size).filter fun k => !(fs[k]! matches .erased)
      let [r] := live | none
      let .var j := fs[r]! | none
      pure (t, fs.size, r, n, n - 1 - j)
    -- the name of the `μ` type at the end of a Π type, and the number of its binders
    let rec target (g : Globals R) (lvl : Nat) : Val R → Nat → Option Name × Nat
      | ty, fuel + 1 => match whnf ty with
        | .pi _ _ _ _ cod _ => let (T, n) := target g (lvl + 1) (Closure.inst g cod (.var lvl)) fuel; (T, n + 1)
        | .mu _ _ _ _ _ (some (T, _, _)) => (some T, 0)
        | _ => (none, 0)
      | _, 0 => (none, 0)
    let rec lastDom (g : Globals R) (lvl : Nat) : Val R → Nat → Option Name
      | ty, fuel + 1 => match whnf ty with
        | .pi _ _ _ dom cod _ => match whnf (Closure.inst g cod (.var lvl)) with
          | .pi .. => lastDom g (lvl + 1) (Closure.inst g cod (.var lvl)) fuel
          | _ => match whnf dom with
            | .mu _ _ _ _ _ (some (T, _, _)) => some T
            | _ => none
        | _ => none
      | _, 0 => none
    match s.globals.find? f, s.globals.find? impl with
    | none, _ => report .error fStx.info s!"unknown declaration {f}"
    | _, none => report .error (cmd.getArg 3).info s!"unknown declaration {impl}"
    | some df, some di =>
      if let some getStx := getStx? then
        -- `attribute [implemented_by mk get] T.mk` (stage 22d): values of `T` are native.
        -- `mk` builds one from the constructor's arguments (it has the constructor's
        -- type), `get` reads its one runtime field back; the kernel keeps the model.
        let get := (getStx.getId?).getD "_"
        let g := s.globals
        let (T?, _) := target g 0 (eval g [] df.type) 1000
        match s.globals.find? get, ctorShape? df, T? with
        | none, _, _ => report .error getStx.info s!"unknown declaration {get}"
        | _, none, _ | _, _, none =>
          report .error fStx.info s!"{f} is not a constructor with exactly one runtime field"
        | some dg, some (tag, nfields, r, mkArity, p), some T =>
          let us := df.levelParams.map Level.param
          if di.levelParams.length != df.levelParams.length || dg.levelParams.length != df.levelParams.length then
            report .error (cmd.getArg 3).info s!"{impl} and {get} must have {f}'s universe parameters"
          else if !convTy g #[] (eval g [] df.type) (eval g [] (di.type.instLevels di.levelParams us)) then
            report .error (cmd.getArg 3).info
              s!"{impl} can't implement {f}: its type {di.type.pretty} is not {f}'s type {df.type.pretty}"
          else if lastDom g 0 (eval g [] dg.type) 1000 != some T then
            report .error getStx.info s!"{get} must take a value of {T} as its last argument"
          else if (reprOf? s.builtins T).isSome then
            report .error fStx.info s!"{T} already has a native representation"
          else
            let (_, getArity) := target g 0 (eval g [] dg.type) 1000
            let key := ReprInfo.key T { mkImpl := impl, getImpl := get, tag, nfields, r, mkArity, p, getArity }
            modify fun s => { s with builtins := (key, f) :: s.builtins,
                                     globals := { s.globals with builtins := (key, f) :: s.globals.builtins } }
      else if s.builtins.any (fun (k, x) => x == f && k != inlineKey && !k.startsWith RVal.exportPrefix) then
        report .error fStx.info s!"{f} is a builtin or foreign function: it already has an implementation"
      else if f == impl then report .error (cmd.getArg 3).info s!"{f} can't be implemented by itself"
      else if df.levelParams.length != di.levelParams.length then
        report .error (cmd.getArg 3).info
          s!"{impl} has {di.levelParams.length} universe parameters, {f} has {df.levelParams.length}"
      else
        let us := df.levelParams.map Level.param
        let tyI := di.type.instLevels di.levelParams us
        let g := s.globals
        if !convTy g #[] (eval g [] df.type) (eval g [] tyI) then
          report .error (cmd.getArg 3).info
            s!"{impl} can't implement {f}: its type {tyI.pretty} is not {f}'s type {df.type.pretty}"
        else
          modify fun s => { s with globals := s.globals.insert { df with impl := some (.const impl us) } }
  | "command.attrInline" =>
    -- `attribute [inline] f` (22i): compiled code substitutes `f`'s body where `f` is
    -- applied to all its arguments, so a lambda argument is applied directly (no
    -- closure). Registered as the builtin key `inline`; the kernel doesn't see it.
    let fStx := cmd.getArg 4
    let f := (fStx.getId?).getD "_"
    match s.globals.find? f with
    | none => report .error fStx.info s!"unknown declaration {f}"
    | some d =>
      if d.value.isNone then report .error fStx.info s!"{f} has no definition to inline"
      else if s.builtins.any (fun (k, x) => x == f && !k.startsWith RVal.exportPrefix) then
        report .error fStx.info s!"{f} is a builtin, foreign or inline function already"
      else
        modify fun s => { s with builtins := s.builtins ++ [(inlineKey, f)],
                                 globals := { s.globals with builtins := s.globals.builtins ++ [(inlineKey, f)] } }
  | "command.attrDeriver" =>
    let C := ((cmd.getArg 3).getId?).getD "_"
    let f := ((cmd.getArg 5).getId?).getD "_"
    let ok := runElab s.globals do
      let (_, ty) ← Elab.infer {} (.node cmd.info "term.ident" #[cmd.getArg 5])
      let deriverTy ← evalIn {} (.const "Deriver" [])
      unifyAt {} cmd deriverTy ty
    match ok with
    | .error e => report .error e.info s!"{f} is not a deriver: {e.msg}"
    | .ok () =>
      modify fun s => { s with derivers := (C, f) :: s.derivers }
      remakeMetaCode
  | "command.deriving" =>
    -- `deriving instance C₁, C₂ for T₁, T₂`
    let ids (stx : Syntax) := stx.args.toList.filter (·.getId?.isSome)
    for T in ids (cmd.getArg 4) do
      for C in ids (cmd.getArg 2) do
        derive (C.getId?.getD "_") (T.getId?.getD "_") C.info
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
        let (code, failed) ← compileReachableE s.globals s.builtins (e.globals.toList) (externImpls := false)
        pure (ty, e, code, failed)
      match result with
      | .ok (_, _, _, (n, err) :: _) =>
        -- the interpreter can't fail: running a stub would print a wrong value
        report .error cmd.info s!"cannot run this: cannot erase {n}: {err}"
      | .ok (ty, e, code, []) =>
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
        let code ← (compileReachable s.globals s.builtins e.globals.toList (externImpls := false)).mapError toString
        let decls ← IR.lowerProgram code e
        let (v, _) ← IR.runProgram (IR.optimizeProgram decls)
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
      -- (not the owned wrappers for closures, stage 8e)
      let mine := (IR.optimizeProgram decls).filter fun d =>
        d.name == n || (d.name.startsWith (n ++ ".") && !d.name.endsWith "._owned")
      report .info cmd.info ("\n".intercalate (mine.toList.map (·.toString)))
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
    | none =>
      -- (HD8) a command macro, written in Wiz
      match s.cmdMacros.lookup k with
      | some f =>
        let r := do Elab.runCommandMacro (← metaCodeFor f) f cmd s.nextScope (macroEnv s.globals)
        elabExpansion s!"macro {f}" r cmd.info
      | none => match s.procMacros.lookup k with
        | some f =>
          -- a `Macro` for a command kind: one command
          let r := do
            let (out, next) ← Elab.runProcMacro (← metaCodeFor f "Macro.run") f cmd s.nextScope (macroEnv s.globals)
            pure (#[out], next)
          elabExpansion s!"macro {f}" r cmd.info
        | none => report .error cmd.info s!"no elaborator for command kind {k}"

end Wiz
