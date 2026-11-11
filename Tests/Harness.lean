import Wiz.Toolchain

/-!
# A tiny test harness

Each group is tagged with the exercise it exercises. `lake test -- <group>...` runs only
the named groups. Unimplemented `sorry`s fail at runtime with "executed 'sorry'".
-/

namespace Tests

/-- The toolchain the suite builds with (C compiler, GMP and collector flags), set once by
`Tests/Main.lean` and passed to everything that compiles. -/
initialize toolchainRef : IO.Ref Wiz.Toolchain ← IO.mkRef {}
/-- The toolchain flags, given again to each case's process. -/
initialize flagsRef : IO.Ref (List String) ← IO.mkRef []

def toolchain : IO Wiz.Toolchain := toolchainRef.get

/-- The tests' loaders serve the toolchain's `lib/` (and test modules standing in for
it): their `builtin` registrations are trusted, as `wiz` trusts `lib/`. The main file
never is. -/
def libModule (m : String) : Bool := m != ""

structure Case where
  name : String
  run  : Unit → IO Unit  -- a thunk: test bodies must not run at start-up

structure Group where
  name     : String
  exercise : String
  cases    : List Case
  /-- The CI shard that runs the group (`.github/test-shards.json`), when no shard's
  selectors pick it; empty: the default shard. `tests --list-shards` prints it. -/
  shard    : String := ""

/-- The groups of the modules under `Tests/Groups/`, in their import order: each module
registers its own (`builtin_initialize registerGroup myGroup`), and `Tests/Groups.lean`, which
Lake generates from the directory's files (`lakefile.lean`), imports them all. So a new
group is a new file and touches no shared one. -/
initialize groupRegistry : IO.Ref (Array Group) ← IO.mkRef #[]

/-- Add a group to the suite: `builtin_initialize registerGroup myGroup` in its module.
`builtin_`: it runs when the test driver starts, never while Lean elaborates a module
that imports the group (a plain `initialize` would, and in the exercise tree, where the
code under test has `sorry`s, that is an error). -/
def registerGroup (g : Group) : IO Unit := groupRegistry.modify (·.push g)

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

def checkEq {α : Type} [BEq α] [ToString α] (expected actual : α) : IO Unit :=
  unless expected == actual do
    throw (IO.userError s!"expected {expected}\n      got {actual}")

/-- Run one case in-process; used by the child process. -/
def Case.runHere (c : Case) : IO UInt32 := do
  try
    c.run ()
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

/-- What a case's process tells the driver besides passing or failing, one line each on
its standard output after this marker: `uses R` (it needs the shared program `R`, such as
the self-hosted checker) and `built R SECONDS` (it built `R`, which took that long). The
driver strips these lines and records them with the case's time (`--timings`), so that CI
can balance the cases of a split shard (`scripts/ci.py`). -/
def noteMarker : String := "@@wiz-test-note "

def note (line : String) : IO Unit := do
  IO.println (noteMarker ++ line)
  (← IO.getStdout).flush

/-- Mark the running case as skipped (it could not run here, e.g. without a C toolchain),
with the reason; the case then returns normally. The driver shows it as skipped, not
passed (`Group.run`), and records the note `skipped REASON` (`--timings`). A skipped case
is not evidence that the case passes. -/
def skip (reason : String) : IO Unit := note s!"skipped {reason}"

/-- The reason a passing case's process gave for skipping: its `skipped` note, or a line
in the old style (`(skipped: REASON)`, `(no X: skipped)`) that a case printed itself. -/
def skipReason (notes : List String) (stdout : String) : Option String :=
  match notes.find? (·.startsWith "skipped ") with
  | some n => some (n.drop "skipped ".length).toString
  | none => (stdout.splitOn "\n").findSome? fun l =>
    let l := l.trimAscii.toString
    if l.startsWith "(skipped: " && l.endsWith ")" then some ((l.drop "(skipped: ".length).dropEnd 1).toString
    else if l.startsWith "(" && l.endsWith ": skipped)" then some ((l.drop 1).dropEnd ": skipped)".length).toString
    else none

/-- Milliseconds as seconds with three decimals, e.g. `12.345`. -/
def showMs (ms : Nat) : String :=
  let frac := toString (ms % 1000)
  s!"{ms / 1000}.{"".pushn '0' (3 - frac.length)}{frac}"

/-- One case's result: its index in the group, its name, whether it passed (a skipped
case did not fail: `ok`, with the reason in `skipped`), its wall time in milliseconds and
the notes it printed (`note`). -/
structure CaseResult where
  index : Nat
  name : String
  ok : Bool
  ms : Nat
  notes : List String
  skipped : Option String := none

/-- Run each case in a child process (`<self> --run-case <group> <index>`), because an
executed `sorry` aborts the whole process; `only` restricts the run to the cases with
these indices. Prints each case with its wall time (`✓` passed, `✗` failed, with its
output, `⊘` skipped, with the reason) and gives its result to `onResult` as soon as it
finishes. -/
def Group.run (g : Group) (only : Option (List Nat) := none)
    (onResult : CaseResult → IO Unit := fun _ => pure ()) : IO (List CaseResult) := do
  IO.println s!"── {g.name} ({g.exercise})"
  let stdout ← IO.getStdout
  stdout.flush
  let self ← IO.appPath
  let mut results := #[]
  for c in g.cases, i in [0:g.cases.length] do
    if let some ixs := only then
      unless ixs.contains i do continue
    let start ← IO.monoMsNow
    let out ← IO.Process.output
      { cmd := self.toString, args := #["--run-case", g.name, toString i] ++ (← flagsRef.get).toArray }
    let ms := (← IO.monoMsNow) - start
    let lines := out.stdout.splitOn "\n"
    let notes := lines.filterMap fun l => if l.startsWith noteMarker then some (l.drop noteMarker.length).toString else none
    let stdoutText := "\n".intercalate (lines.filter (!·.startsWith noteMarker))
    let skipped := if out.exitCode == 0 then skipReason notes stdoutText else none
    if let some why := skipped then
      IO.println s!"  ⊘ {c.name} ({showMs ms} s)\n      skipped ({why})"
    else if out.exitCode == 0 then
      IO.println s!"  ✓ {c.name} ({showMs ms} s)"
    else
      let msg := if (out.stderr ++ stdoutText).contains "executed 'sorry'" then
          "not implemented yet (hit a `sorry`)"
        else (out.stderr ++ stdoutText).trimAscii.toString.replace "\n" "\n      "
      IO.println s!"  ✗ {c.name} ({showMs ms} s)\n      {msg}"
    stdout.flush
    let r : CaseResult := { index := i, name := c.name, ok := out.exitCode == 0, ms, notes, skipped }
    onResult r
    results := results.push r
  pure results.toList

/-- Cases with known outcomes for the test driver's own tests (`Tests/Grail.lean`,
`testrunner`): `--run` finds this group, but no selector picks it, so it is never part
of a suite run. -/
def driverFixtures : Group where
  name := "driver-fixtures"
  exercise := "the test driver"
  cases := [
    { name := "fixture: passes", run := fun _ => pure () },
    { name := "fixture: fails", run := fun _ => do
        IO.println "fixture output before the failure"
        throw (IO.userError "fixture failure") },
    { name := "fixture: skips", run := fun _ => skip "fixture reason" },
    { name := "fixture: skips (old style)", run := fun _ => IO.println "    (skipped: old fixture reason)" }
  ]

end Tests
