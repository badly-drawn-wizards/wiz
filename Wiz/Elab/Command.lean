import Wiz.Elab.Recursor
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

/-- Metas are untyped, so `?A : Sort ?u` never learns `?u` from `?A := A`. For each
recorded constraint whose hole is now solved, ask the kernel for the solution's type
and unify its level. -/
def solveSortConstraints : ElabM R Unit := do
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
          for withIH in [false, true] do
            match mkRecursor g name ctors withIH with
            | .error e => report .error cmd.info s!"could not generate the recursor: {e}"; return
            | .ok d =>
              match addDecl g d with
              | .ok g' => g := g'
              | .error e =>
                report .error cmd.info s!"kernel rejected {d.name}: {e}\n  {d.type.pretty}"
                return
        modify fun s => { s with globals := g }
  | "command.syntax" | "command.declareSyntaxCat" =>
    match updateTables s.tables cmd with
    | .ok tables => modify fun s => { s with tables }
    | .error msg => report .error cmd.info msg
  | k => report .error cmd.info s!"no elaborator for command kind {k}"

end Wiz
