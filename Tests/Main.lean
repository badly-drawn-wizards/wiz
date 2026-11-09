import Tests.Rig
import Tests.Eval
import Tests.Check
import Tests.Parser
import Tests.Elab
import Tests.LSP

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

open Tests

def groups : List Group :=
  [Rig.group, Eval.evalGroup, Eval.convGroup, Eval.structGroup, Check.mlttGroup, Check.qttGroup, Check.structGroup,
   Parser.lexGroup, Parser.termGroup, Parser.cmdGroup, Elab.group, Elab.levelGroup, Elab.structGroup, Elab.ottGroup, Elab.qtyGroup, Elab.dataGroup, Elab.inductiveGroup, Elab.matchGroup, Elab.coinductiveGroup, Elab.sizedGroup, Elab.runGroup, Elab.macroGroup, Elab.builtinGroup, Elab.tacticGroup, Elab.classGroup, Elab.backendGroup, Elab.cGroup, Elab.llvmGroup, Elab.ffiGroup, Elab.effectsGroup, Elab.toolingGroup, Elab.stdGroup, Elab.wordGroup, Elab.selfHostGroup, Elab.languageGroup, Elab.opticGroup, Elab.derivingGroup, Elab.reuseGroup, Elab.vecGroup, LSP.group, LSP.serverGroup]

/-- Whether a command-line selector picks a group: `=NAME` exactly, anything else as a
prefix of the group's name. -/
def selects (g : Group) (arg : String) : Bool :=
  if arg.startsWith "=" then "=" ++ g.name == arg else g.name.startsWith arg

/-- `lake test` runs everything; `lake test -- conv rig` runs only groups whose name
starts with one of the arguments, and `lake test -- =c` only the group named `c`.
`lake test -- --list` prints the group names, one per line (CI checks its shards
against them). -/
def main : List String → IO UInt32
  | ["--run", group, ix] =>
    match groups.find? (·.name == group) >>= (·.cases[ix.toNat!]?) with
    | some c => c.runHere
    | none => do IO.eprintln s!"no such case: {group} #{ix}"; pure 2
  -- (D1) check a file with the given regularity mode, in a child process that the test
  -- can time out: `Elab.checkDiverges`
  | ["--check", mode, file] => do
    let input ← IO.FS.readFile file
    let s := Wiz.runFrontend (R := Wiz.ZeroOneMany) input { globals := { regularity := Elab.regularityMode mode } }
    let errs := s.messages.filter (·.severity == .error)
    for m in errs do IO.eprintln (m.render input)
    pure (if errs.isEmpty then 0 else 1)
  | ["--list"] => do
    for g in groups do IO.println g.name
    pure 0
  | args => do
    let selected := if args.isEmpty then groups
      else groups.filter fun g => args.any (selects g)
    let mut passed := 0
    let mut failed := 0
    for g in selected do
      let start ← IO.monoMsNow
      let (p, f) ← g.run
      IO.println s!"  ({g.name}: {((← IO.monoMsNow) - start) / 1000} s)"
      passed := passed + p
      failed := failed + f
    IO.println s!"\n{passed} passed, {failed} failed"
    pure (if failed == 0 then 0 else 1)
