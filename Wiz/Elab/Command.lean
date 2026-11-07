import Wiz.Elab.Recursor
import Wiz.Compiler.Run
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

/-- Metas are untyped, so `?A : Sort ?u` never learns `?u` from `?A := A`. For each
recorded constraint whose hole is now solved, ask the kernel for the solution's type
and unify its level. -/
def solveSortConstraints : ElabM R Unit := do
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
  let ty := tele.foldr (fun (x, bi, q, a) b => Term.pi x bi q a b) ty
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
  let .pi x0 bi0 q0 A0 B := ty | throwAt info "internal error: sized definition"
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
  let .pi _ _ _ _ c_s ← force fty | throwAt info "internal error"
  let ctxS := c1.bind "s" .size
  let sv := Val.var c1.lvl
  let afterS ← instM c_s sv
  let .pi _ _ _ recTy c_rec ← force afterS | throwAt info "internal error"
  let ctxR := ctxS.bind "rec" recTy
  let recV := Val.var ctxS.lvl
  let afterRec ← instM c_rec recV
  let .pi _ _ _ iTy c_i ← force afterRec | throwAt info "internal error"
  let ctxI := ctxR.bind "i" iTy
  let iV := Val.var ctxR.lvl
  let afterI ← instM c_i iV
  let .pi _ _ _ xTy c_x ← force afterI | throwAt info "internal error"
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
      ((Term.app (Term.app ((P.lift (L - c1.lvl)).lift 2) .tt) (.var 0))))
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
    let .pi x _ _ A Bc ← force goal | throwAt info s!"{name} takes fewer than {n} arguments"
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
  let fullTy := tele.foldr (fun (x, bi, qq, a) b => Term.pi x bi qq a b) (Term.pi x0 bi0 q0 A0 B)
  let val ← zonk 0 val
  ensureNoMVars val info
  pure (fullTy, val)

/-- `def f binders : T | p… => rhs …`: the alternatives match the leading explicit
arguments of `T`; a right-hand side that calls `f` makes it structurally recursive. -/
def elabDefEqns (name : Name) (cmd : Syntax) : ElabM R (Term R × Term R) := do
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
    let .pi x _ _ A B ← force tyv | throwAt tyStx.info s!"{name} takes fewer than {n} arguments"
    let x := if x == "_" then s!"a{i}" else x
    vars := vars ++ [ctx'.lvl]
    names := names ++ [x]
    tyv ← instM B (Val.var ctx'.lvl)
    ctx' := ctx'.bind x A
  let mentions (stx : Syntax) : Bool := syntaxMentions name stx
  let rc : Option RecCtx := if clauses.any (fun c => mentions c.rhs) then some { fn := name } else none
  -- a recursive definition whose first argument has a size-variable size: compile to `sfix`
  if rc.isSome then
    if let some x0 := vars.head? then
      if let .mu _ _ _ _ (.neutral (.local si) #[]) _ ← force ctx'.types[ctx'.lvl - x0 - 1]! then
        if si < ctx.lvl then
          return ← elabSizedDef name cmd ctx tele ty si clauses
  let body ← compileMatch ctx' vars clauses tyv rc true
  solveSortConstraints
  let val := tele.foldr (fun (x, _, _, _) b => Term.lam x b) (names.foldr .lam body)
  let fullTy := tele.foldr (fun (x, bi, q, a) b => Term.pi x bi q a b) ty
  let val ← zonk 0 val
  ensureNoMVars val info
  pure (fullTy, val)

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
    .sigma x w ((q ctx.lvl ctx.types[ctx.lvl - k - 1]!).lift j) acc) (.unit (.succ l))
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
        let .pi _ _ _ _ cod ← force oty | throwAt info "internal error: observation type"
        oty ← instM cod a
      let .pi _ _ _ _ cod ← force oty | throwAt info "internal error: observation type"
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
  let fullTy := tele.foldr (fun (x, bi, qq, a) b => Term.pi x bi qq a b) ty
  let val ← zonk 0 val
  ensureNoMVars val info
  pure (fullTy, val)

def runElab (g : Globals R) (x : ElabM R α) (levelParams : List Name := []) :
    Except ElabError α :=
  (x.run { globals := g, levelParams }).map (·.1)

/-- Elaborate one command, updating the state and adding messages. -/
def elabCommand (cmd : Syntax) : StateM (CommandState R) Unit := do
  let s ← get
  let report (sev : Severity) (info : SourceInfo) (text : String) : StateM (CommandState R) Unit :=
    modify fun s => { s with messages := s.messages.push { info, severity := sev, text } }
  let addDeclChecked (name : Name) (levelParams : List Name) (ty : Term R) (val : Option (Term R)) := do
    match addDecl s.globals { name, levelParams, type := ty, value := val } with
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
    else match runElab s.globals (elabDeclTerms binders typeStx valStx cmd.info) levelParams with
      | .ok (ty, val) => addDeclChecked name levelParams ty val
      | .error e => report .error e.info e.msg
  | "command.check" =>
    let r := runElab s.globals do
      let (t, ty) ← Elab.infer {} (cmd.getArg 1)
      solveSortConstraints
      let t ← zonk 0 t
      let ty ← zonk 0 (quote (← getGlobals) 0 ty)
      pure s!"{t.pretty} : {ty.pretty}"
    match r with
    | .ok text => report .info cmd.info text
    | .error e => report .error e.info e.msg
  | "command.reduce" =>
    let r := runElab s.globals do
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
        | some obs => runElab s.globals (elabCopatterns name cmd obs) levelParams
        | none => runElab s.globals (elabDefEqns name cmd) levelParams
      match r with
      | .ok (ty, val) => addDeclChecked name levelParams ty (some val)
      | .error e => report .error e.info e.msg
  | "command.coinductive" =>
    let name := ((cmd.getArg 1).getId?).getD "_"
    let levelParams := ((cmd.getArg 2).getArg 1).args.toList.filterMap Syntax.getId?
    if s.globals.contains name then
      report .error (cmd.getArg 1).info s!"'{name}' has already been declared"
    else
      match runElab s.globals (elabCoinductive cmd levelParams) levelParams with
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
  | "command.inductive" | "command.structure" =>
    let name := ((cmd.getArg 1).getId?).getD "_"
    let levelParams := ((cmd.getArg 2).getArg 1).args.toList.filterMap Syntax.getId?
    if s.globals.contains name then
      report .error (cmd.getArg 1).info s!"'{name}' has already been declared"
    else
      let elabCmd := if cmd.isOfKind "command.inductive" then elabInductive cmd levelParams
        else elabStructure cmd levelParams
      match runElab s.globals elabCmd levelParams with
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
  | "command.erase" =>
    let n := ((cmd.getArg 1).getId?).getD "_"
    match s.globals.find? n with
    | none => report .error cmd.info s!"unknown declaration {n}"
    | some d => match eraseDecl s.globals d with
      | .ok e => report .info cmd.info s!"{n} := {e}"
      | .error err => report .error cmd.info s!"cannot erase {n}: {err}"
  | "command.eval" =>
    -- elaborate, erase, run, and read the result back using its type
    let r := runElab s.globals do
      let (t, _) ← Elab.infer {} (cmd.getArg 1)
      solveSortConstraints
      let t ← zonk 0 t
      ensureNoMVars t cmd.info
      pure t
    match r with
    | .error e => report .error e.info e.msg
    | .ok t =>
      let ctx : Ctx R := { globals := s.globals }
      match Wiz.infer ctx t, compileAll s.globals with
      | .ok (ty, _), .ok code =>
        match eraseCheck ctx t ty with
        | .ok e =>
          let v := run code [] e
          report .info cmd.info (readback s.globals ty v).pretty
        | .error err => report .error cmd.info s!"cannot run this: {err}"
      | .error err, _ | _, .error err => report .error cmd.info s!"cannot run this: {err}"
  | "command.syntax" | "command.declareSyntaxCat" =>
    match updateTables s.tables cmd with
    | .ok tables => modify fun s => { s with tables }
    | .error msg => report .error cmd.info msg
  | k => report .error cmd.info s!"no elaborator for command kind {k}"

end Wiz
