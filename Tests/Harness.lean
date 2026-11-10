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

/-- Run each case in a child process (`<self> --run <group> <index>`), because an
executed `sorry` aborts the whole process. Returns (passed, failed). -/
def Group.run (g : Group) : IO (Nat × Nat) := do
  IO.println s!"── {g.name} ({g.exercise})"
  let self ← IO.appPath
  let mut passed := 0
  let mut failed := 0
  for c in g.cases, i in [0:g.cases.length] do
    let out ← IO.Process.output
      { cmd := self.toString, args := #["--run", g.name, toString i] ++ (← flagsRef.get).toArray }
    if out.exitCode == 0 then
      IO.println s!"  ✓ {c.name}"
      passed := passed + 1
    else
      let msg := if (out.stderr ++ out.stdout).contains "executed 'sorry'" then
          "not implemented yet (hit a `sorry`)"
        else (out.stderr ++ out.stdout).trimAscii.toString.replace "\n" "\n      "
      IO.println s!"  ✗ {c.name}\n      {msg}"
      failed := failed + 1
  pure (passed, failed)

end Tests
