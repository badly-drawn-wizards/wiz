import Tests.Rig
import Tests.Eval
import Tests.Check
import Tests.Parser
import Tests.Elab
import Tests.ElabFix
import Tests.Grail
import Tests.LSP
import Tests.Allocs
import Tests.Scaling

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

open Tests

def groups : List Group :=
  [Rig.group, Eval.evalGroup, Eval.convGroup, Eval.structGroup, Check.mlttGroup, Check.qttGroup, Check.structGroup,
   Parser.lexGroup, Parser.termGroup, Parser.cmdGroup, Elab.group, Elab.levelGroup, Elab.structGroup, Elab.ottGroup, Elab.qtyGroup, Elab.dataGroup, Elab.inductiveGroup, Elab.matchGroup, Elab.coinductiveGroup, Elab.sizedGroup, Elab.runGroup, Elab.macroGroup, Elab.builtinGroup, Elab.tacticGroup, Elab.classGroup, Elab.backendGroup, Elab.cGroup, Elab.llvmGroup, Elab.ffiGroup, Elab.effectsGroup, Elab.toolingGroup, Elab.stdGroup, Elab.wordGroup, Elab.selfHostGroup, Elab.languageGroup, Elab.opticGroup, Elab.derivingGroup, Elab.reuseGroup, Elab.borrowGroup, Elab.phantomGroup, Elab.liftGroup, Elab.regionsGroup, Elab.vecGroup, LSP.group, LSP.serverGroup, Grail.modulesGroup, Grail.toolchainGroup, Grail.grailGroup, Grail.grailJobsGroup, Grail.grailDepsGroup, Grail.testRunnerGroup, Grail.grailSelfhostGroup, ElabFix.group, Elab.infoviewGroup, Scaling.group]

/-- Whether a command-line selector picks a group: `=NAME` exactly, anything else as a
prefix of the group's name. `=NAME#I,J,…` picks only the cases with those indices
(counting from 0) of the group `NAME`; CI splits a long group this way
(`scripts/ci.py`). -/
def selects (g : Group) (arg : String) : Bool :=
  if arg.startsWith "=" then "=" ++ g.name == (arg.splitOn "#")[0]! else g.name.startsWith arg

/-- The cases of `g` that the selectors pick: `none` for all of them. -/
def selectedCases (g : Group) (args : List String) : Option (List Nat) := Id.run do
  let mut ixs : List Nat := []
  if !args.any (selects g) then return none
  for arg in args.filter (selects g) do
    match arg.splitOn "#" with
    | [_, list] => ixs := ixs ++ (list.splitOn ",").filterMap String.toNat?
    | _ => return none
  return some ixs

/-- A JSON string literal. -/
def jsonStr (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    out := match c with
      | '"' => out ++ "\\\""
      | '\\' => out ++ "\\\\"
      | '\n' => out ++ "\\n"
      | c => if c.toNat < 0x20 then
          let h := String.ofList (Nat.toDigits 16 c.toNat)
          out ++ "\\u00" ++ (if h.length < 2 then "0" ++ h else h)
        else out.push c
  return out.push '"'

/-- The `--timings` record of a case: one line of JSON. -/
def timingLine (shard group : String) (r : CaseResult) : String :=
  let notes := ", ".intercalate (r.notes.map jsonStr)
  s!"\{\"shard\": {jsonStr shard}, \"group\": {jsonStr group}, \"index\": {r.index}, \"case\": {jsonStr r.name}, " ++
  s!"\"seconds\": {showMs r.ms}, \"ok\": {r.ok}, \"notes\": [{notes}]}"

/-- Remove `--FLAG VALUE` from the arguments; the value, if it was there. -/
def takeFlag (flag : String) : List String → Option String × List String
  | f :: v :: rest => if f == flag then (some v, rest) else
    let (x, r) := takeFlag flag (v :: rest); (x, f :: r)
  | args => (none, args)

/-- This machine's toolchain settings, from the uncommitted `grail.local.wiz` that the nix
dev shell writes (`flake.nix`), as grail reads them. -/
def localToolchain : IO Wiz.Toolchain := do
  let file : System.FilePath := "grail.local.wiz"
  unless ← file.pathExists do
    IO.eprintln "note: no grail.local.wiz (`nix develop` writes it): tests that compile C use `cc` without GMP's paths"
    return {}
  let settings ← match ← Grail.evalBuildFile {} 0 ["lib", "."] file "Settings.render settings" with
    | .error e => throw (IO.userError e)
    | .ok x => match Grail.decodeSettings x with
      | .error e => throw (IO.userError s!"{file}: {e}")
      | .ok ss => pure ss
  settings.foldlM (init := {}) fun tc (k, v) => match tc.set k v with
    | some tc => pure tc
    | none => throw (IO.userError s!"{file}: unknown setting {k}")

/-- The suite's toolchain: `grail.local.wiz`, then the toolchain flags given to
`lake test -- …`, which win. The top-level run reads the file and passes the result to
each case's process as flags (`readLocal := false` there). -/
def suiteToolchain (args : List String) (readLocal : Bool) : IO (Wiz.Toolchain × List String) := do
  let base ← if readLocal then localToolchain else pure {}
  pure (base.parseFlags args)

/-- `lake test` runs everything; `lake test -- conv rig` runs only groups whose name
starts with one of the arguments, `lake test -- =c` only the group named `c`, and
`lake test -- =selfhost#0,3` only cases 0 and 3 of the group `selfhost`.
`lake test -- --list` prints the group names, one per line (CI checks its shards
against them), and `lake test -- --list-cases SELECTOR…` the selected cases, as
`GROUP<tab>INDEX<tab>NAME` lines. `--timings FILE` appends one line of JSON per case to
FILE (its group, index, name, wall time in seconds, whether it passed, and its notes:
`Tests.note`), labelled with `--shard NAME`. -/
def main (args : List String) : IO UInt32 := do
  -- the processes the suite starts get the toolchain as flags
  let child := match args with
    | "--run" :: _ | "--check" :: _ | "--grail-job" :: _ | ["--list"] | "--list-cases" :: _ | "--allocs" :: _ => true
    | _ => false
  let (tc, args') ← suiteToolchain args (readLocal := !child)
  toolchainRef.set tc
  flagsRef.set tc.toFlags
  match args' with
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
  -- a job of a grail build that a test runs (`Grail/Graph.lean`)
  | ["--grail-job", job] => Grail.jobMain tc job
  -- allocation counts and IR of definitions of a file (`Tests/Allocs.lean`)
  | "--allocs" :: rest => Allocs.allocsMain rest
  | ["--list"] => do
    for g in groups do IO.println g.name
    pure 0
  | "--list-cases" :: sels => do
    for g in groups do
      let only := selectedCases g sels
      if sels.isEmpty || sels.any (selects g) then
        for c in g.cases, i in [0:g.cases.length] do
          if only.all (·.contains i) then IO.println s!"{g.name}\t{i}\t{c.name}"
    pure 0
  | args => do
    let (timings, args) := takeFlag "--timings" args
    let (shard, args) := takeFlag "--shard" args
    let shard := shard.getD ""
    let selected := if args.isEmpty then groups
      else groups.filter fun g => args.any (selects g)
    let mut passed := 0
    let mut failed := 0
    for g in selected do
      let start ← IO.monoMsNow
      let results ← g.run (selectedCases g args) fun r => do
        if let some file := timings then
          let h ← IO.FS.Handle.mk file .append
          h.putStrLn (timingLine shard g.name r)
      let cases := results.foldl (· + ·.ms) 0
      IO.println s!"  ({g.name}: {showMs ((← IO.monoMsNow) - start)} s; cases {showMs cases} s)"
      let p := (results.filter (·.ok)).length
      passed := passed + p
      failed := failed + (results.length - p)
    IO.println s!"\n{passed} passed, {failed} failed"
    pure (if failed == 0 then 0 else 1)
