import Grail.Build

/-!
# The test runner (stage 23f)

A `tests` target names a directory; every `.wiz` file under it is a test, and
`F.expected` beside `F.wiz` is its expected output. The first line says what kind of
test it is (default `check`):

* `-- test: check`: the messages of elaborating the file, as `wiz check` prints them
  (`path:line:col: severity: text`, the path relative to the package);
* `-- test: run`: what `main` prints, compiled through C (an `IO` program's output, or
  `main`'s value read back with its type, as `wiz run` prints it).

A test is a job like any other: its key covers the file's key (its text and its
imports'), the kind, the toolchain for `run`, and the expected output, and a passing test
is recorded under `.grail/build/<key>/`, so `grail test` again runs nothing. A failing
test isn't recorded. `grail test --update` writes the actual output to `.expected`.
-/

namespace Grail
open Wiz

inductive TestKind where
  | check
  | run
  deriving BEq, Repr

def TestKind.ofSource (src : String) : Except String TestKind :=
  let first := (src.splitOn "\n").headD ""
  if !first.startsWith "-- test:" then .ok .check else
  match ((first.drop 8).trimAscii.toString) with
  | "check" => .ok .check
  | "run" => .ok .run
  | k => .error s!"unknown test kind {k} (check, run)"

def TestKind.name : TestKind → String
  | .check => "check" | .run => "run"

structure TestResult where
  file : String
  ok : Bool
  /-- came from a recorded pass -/
  cached : Bool := false
  message : String := ""

/-- The first line where two texts differ, for the report. -/
def firstDifference (expected actual : String) : String := Id.run do
  let es := expected.splitOn "\n"
  let as := actual.splitOn "\n"
  for i in [0:max es.length as.length] do
    let e := es[i]?.getD "<end>"
    let a := as[i]?.getD "<end>"
    if e != a then return s!"line {i + 1}:\n      expected: {e}\n      actual:   {a}"
  pure "(the same)"

/-- What the test prints. -/
def Runner.testOutput (r : Runner) (file : String) (kind : TestKind) : IO (Except String String) := do
  match kind with
  | .check =>
    let l ← r.load file
    let s ← r.elab file
    pure (.ok (render file l s))
  | .run =>
    let s ← r.elab file
    let exe ← match ← r.link s!"test-{hash file}" file with
      | .ok exe => pure exe
      | .error e => return .error e
    let out ← IO.Process.output { cmd := "timeout", args := #["60", exe.toString] }
    if out.exitCode == 124 then return .error "timed out (60 s)"
    if out.exitCode != 0 then return .error s!"exited with {out.exitCode}: {out.stderr}"
    match Build.irProgram s "main" with
    | .error e => pure (.error e)
    | .ok (_, ty) =>
      if Build.isIO ty then return .ok out.stdout
      match Build.parseValue out.stdout with
      | none => pure (.error s!"could not read the result: {out.stdout}")
      | some v => pure (.ok ((readback s.globals s.builtins (eval s.globals [] ty) v).pretty ++ "\n"))

/-- Run one test (a path relative to the package). -/
def Runner.test (r : Runner) (file : String) (update : Bool) : IO TestResult := do
  let src ← IO.FS.readFile (r.ctx.dir / file)
  let kind ← match TestKind.ofSource src with
    | .ok k => pure k
    | .error e => return { file, ok := false, message := e }
  let expFile := r.ctx.dir / ((System.FilePath.mk file).withExtension "expected")
  let expected ← if ← expFile.pathExists then some <$> IO.FS.readFile expFile else pure none
  let l ← r.load file
  let key := mixHash (hash "test") (hash (toString [toString r.ctx.binId, toString l.key, kind.name,
    if kind == .run then toString r.ctx.tc.id else "", expected.getD "\x00none"]))
  let out := r.ctx.grailDir / "build" / hex key
  if !update && expected.isSome && (← out.pathExists) then
    r.stats.modify fun s => { s with upToDate := s.upToDate + 1 }
    return { file, ok := true, cached := true }
  let actual ← match ← r.testOutput file kind with
    | .ok a => pure a
    | .error e => pure s!"error: {e}\n"
  if update then
    if expected != some actual then IO.FS.writeFile expFile actual
    return { file, ok := true, message := if expected == some actual then "" else "updated" }
  match expected with
  | none => return { file, ok := false, message := s!"no {expFile} (grail test --update writes it)" }
  | some e =>
    if e != actual then
      r.stats.modify fun s => { s with failed := s.failed + 1 }
      return { file, ok := false, message := firstDifference e actual }
    -- record the pass
    let _ ← r.job s!"test {file}" key fun dir => do
      IO.FS.writeFile (dir / "actual") actual
      pure (.ok ())
    pure { file, ok := true }

/-- The test files of a `tests` target, relative to the package, sorted. -/
def testFiles (dir : System.FilePath) (root : String) : IO (Array String) := do
  let files ← Module.listRoot (dir / root)
  pure (files.map fun (m, _) => (System.FilePath.mk root / Module.relPath m).toString)

/-- Run the tests of these targets whose path contains one of `filters` (all, if none). -/
def Runner.tests (r : Runner) (targets : List Target) (filters : List String) (update : Bool) :
    IO (Array TestResult) := do
  let mut results := #[]
  for t in targets do
    if let .tests _ root := t then
      for f in ← testFiles r.ctx.dir root do
        if filters.isEmpty || filters.any (fun p => (f.splitOn p).length > 1) then
          let res ← r.test f update
          r.log (if res.ok then s!"  ✓ {f}{if res.message.isEmpty then "" else s!" ({res.message})"}"
                 else s!"  ✗ {f}\n      {res.message}")
          results := results.push res
  pure results

end Grail
