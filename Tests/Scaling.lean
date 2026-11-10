import Tests.Harness
import Wiz

/-!
# Scaling (agent/mem-hunt)

Regression tests for super-linear time or memory: each case scales one dimension of
its input (fields of a structure, …) well past where the old blow-up made it
unusable, and bounds the case's time. The bounds are loose, two orders of magnitude
above what the case takes now: they catch exponential behaviour, not noise.
-/

open Wiz

set_option compiler.extract_closed false

namespace Tests.Scaling


/-- Checking `input` (with the Lean kernel, no library, in a child process:
`tests --check`) succeeds within `secs` seconds. A child process, so that a regression
times out instead of hanging the suite (address space capped at 8 GB, like
`checkDiverges`: the runtime reserves a large thread stack, so a tight cap fails). -/
def checksWithin (secs : Nat) (input : String) : IO Unit := do
  let dir ← IO.FS.createTempDir
  IO.FS.writeFile (dir / "input.wiz") input
  let self ← IO.appPath
  let out ← IO.Process.output { cmd := "sh", cwd := dir, args := #["-c",
    s!"ulimit -v 8000000; exec timeout {secs} \"$0\" --check off input.wiz", self.toString] }
  if out.exitCode == 124 then throw (IO.userError s!"took longer than {secs} s")
  unless out.exitCode == 0 do
    throw (IO.userError s!"exit code {out.exitCode}: {(out.stdout ++ out.stderr).take 1500}")

/-- Unary numbers, so that the inputs need no library. -/
def natDecl : String := "inductive N where\n  | z\n  | s (n : N)\n"

/-- A structure with `n` fields, its constructor applied, and its last field. -/
def wideStructure (n : Nat) : String :=
  natDecl ++ "structure S where\n" ++ String.join ((List.range n).map (s!"  f{·} : N\n")) ++
  s!"def x : S := S.mk {" ".intercalate ((List.range n).map fun _ => "N.z")}\n" ++
  s!"def y : N := x.f{n - 1}\n"

/-- A class with `n` methods shaped like the HDL's `Hw` (an implicit index, two
arguments), and an instance given by `where`. -/
def wideClass (n : Nat) : String :=
  natDecl ++ "class C (r : N → Type) where\n" ++
  String.join ((List.range n).map (s!"  op{·} : \{n : N} → r n → r n → r n\n")) ++
  "def K (n : N) : Type := N\ninstance : C K where\n" ++
  String.join ((List.range n).map (s!"  op{·} := fun a b => a\n"))

def group : Group where
  name := "scaling"
  exercise := "super-linear time and memory"
  cases := [
    -- `Level.normalize (imax a b)` normalised `b` twice: 2^n on the chain of `imax`es
    -- that is a telescope's sort (`S.mk`'s type, the class's methods)
    { name := "a structure with 64 fields (Level.normalize was exponential: 24 took 49 s)", run := fun _ =>
        checksWithin 60 (wideStructure 64) },
    { name := "a class with 48 Hw-like methods and an instance (was exponential: 16 took 4 s)", run := fun _ =>
        checksWithin 60 (wideClass 48) }]

end Tests.Scaling
