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

structure Case where
  name : String
  run  : Unit → IO Unit  -- a thunk: test bodies must not run at start-up

structure Group where
  name     : String
  exercise : String
  cases    : List Case

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

/-- Milliseconds as seconds with three decimals, e.g. `12.345`. -/
def showMs (ms : Nat) : String :=
  let frac := toString (ms % 1000)
  s!"{ms / 1000}.{"".pushn '0' (3 - frac.length)}{frac}"

/-- One case's result: its index in the group, its name, whether it passed, its wall
time in milliseconds and the notes it printed (`note`). -/
structure CaseResult where
  index : Nat
  name : String
  ok : Bool
  ms : Nat
  notes : List String

/-- Run each case in a child process (`<self> --run <group> <index>`), because an
executed `sorry` aborts the whole process; `only` restricts the run to the cases with
these indices. Prints each case with its wall time and gives its result to `onResult`
as soon as it finishes. -/
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
      { cmd := self.toString, args := #["--run", g.name, toString i] ++ (← flagsRef.get).toArray }
    let ms := (← IO.monoMsNow) - start
    let lines := out.stdout.splitOn "\n"
    let notes := lines.filterMap fun l => if l.startsWith noteMarker then some (l.drop noteMarker.length).toString else none
    let stdoutText := "\n".intercalate (lines.filter (!·.startsWith noteMarker))
    if out.exitCode == 0 then
      IO.println s!"  ✓ {c.name} ({showMs ms} s)"
    else
      let msg := if (out.stderr ++ stdoutText).contains "executed 'sorry'" then
          "not implemented yet (hit a `sorry`)"
        else (out.stderr ++ stdoutText).trimAscii.toString.replace "\n" "\n      "
      IO.println s!"  ✗ {c.name} ({showMs ms} s)\n      {msg}"
    stdout.flush
    let r : CaseResult := { index := i, name := c.name, ok := out.exitCode == 0, ms, notes }
    onResult r
    results := results.push r
  pure results.toList

end Tests
