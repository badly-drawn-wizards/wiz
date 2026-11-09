import Grail.Build

/-!
# The self-hosted toolchain as targets (stage 23e)

`selfhost NAME ROLE` targets build the self-hosted programs from `selfhost/*.wiz`:

* `checker`: the self-hosted frontend (reads `input.wiz`, prints what it makes of it);
* `compiler`: the frontend and backend (reads `input.wiz`, prints C);
* `bootstrap`: the fixpoint check of `scripts/fixpoint.sh`. Stage 1 (the compiler, built
  by the Lean `wiz`) compiles the toolchain to C (`self1.c`); that C, compiled with
  `selfhost/rt.c` and the collector, is stage 2, which compiles the toolchain again
  (`self2.c`). The two must be equal.

Each step is a job: the generated source (keyed by the `selfhost/*.wiz` texts and this
binary, which holds the parser tables), then the executable as for any `exe`, then
`self1.c` (keyed by the stage-1 binary and its input), stage 2 (by `self1.c`, `rt.c`,
the compiler and the collector's flags) and `self2.c`. Run again, the check runs nothing
unless something it depends on changed.
-/

namespace Grail
open Wiz

/-- Write the program for `role` (`checker` or `compiler`) and the toolchain as an input
(`self.wiz`); returns the program's path relative to the package. -/
def Runner.selfhostSource (r : Runner) (role : String) : IO (Except String String) := do
  let files := if role == "checker" then Selfhost.checkerFiles else Selfhost.compilerFiles
  let srcs ← files.mapM fun (f : String) => IO.FS.readFile (r.ctx.dir / f)
  let prog := if role == "checker" then Selfhost.checkerSource srcs else Selfhost.compilerSource srcs
  let key := mixHash (hash "selfhost-source") (hash (toString [role, toString r.ctx.binId, prog]))
  match ← r.job s!"generate {role}.wiz" key (fun out => do
      IO.FS.writeFile (out / s!"{role}.wiz") prog
      IO.FS.writeFile (out / "self.wiz") (Selfhost.selfSource srcs)
      pure (.ok ())) with
  | .error e => pure (.error e)
  | .ok _ => pure (.ok s!".grail/build/{hex key}/{role}.wiz")

/-- Run `exe` in a fresh directory with `input` as `input.wiz`; its output goes to `file`. -/
def runOn (exe : System.FilePath) (input : String) (out : System.FilePath) (file : String) :
    IO (Except String Unit) := do
  let exe ← IO.FS.realPath exe  -- it runs in another directory
  let work := out / "work"
  IO.FS.createDirAll work
  IO.FS.writeFile (work / "input.wiz") input
  let o ← IO.Process.output { cmd := exe.toString, cwd := work }
  IO.FS.removeDirAll work
  if o.exitCode != 0 then return .error s!"{exe} failed ({o.exitCode}): {o.stderr.take 2000}"
  IO.FS.writeFile (out / file) o.stdout
  pure (.ok ())

/-- The bootstrap fixpoint check. -/
def Runner.bootstrap (r : Runner) : IO (Except String Unit) := do
  let tc := r.ctx.tc
  let src ← match ← r.selfhostSource "compiler" with | .ok f => pure f | .error e => return .error e
  let stage1 ← match ← r.link "selfhost-stage1" src with | .ok e => pure e | .error e => return .error e
  let self ← IO.FS.readFile (r.ctx.dir / ((System.FilePath.mk src).withFileName "self.wiz"))
  let k1 := mixHash (hash "self1") (hash (toString [toString (hash (← IO.FS.readBinFile stage1)), self]))
  let d1 ← match ← r.job "stage 1 compiles the toolchain (self1.c)" k1 (fun out => runOn stage1 self out "self1.c") with
    | .ok d => pure d | .error e => return .error e
  let self1 ← IO.FS.readFile (d1 / "self1.c")
  let rt ← IO.FS.readFile (r.ctx.dir / "selfhost" / "rt.c")
  let k2 := mixHash (hash "stage2") (hash (toString [self1, rt, tc.cc, " ".intercalate tc.gcCflags, " ".intercalate tc.gcLdflags]))
  let d2 ← match ← r.job "stage 2: cc self1.c with selfhost/rt.c" k2 (fun out => do
      let rtDir ← IO.FS.realPath (r.ctx.dir / "selfhost")
      run tc.cc (#["-O1", "-w", s!"-I{rtDir}"] ++ tc.gcCflags.toArray ++
        #[(d1 / "self1.c").toString, "-o", (out / "stage2").toString] ++ tc.gcLdflags.toArray)) with
    | .ok d => pure d | .error e => return .error e
  let k3 := mixHash (hash "self2") (hash (toString [toString k2, self]))
  let d3 ← match ← r.job "stage 2 compiles the toolchain (self2.c)" k3 (fun out => runOn (d2 / "stage2") self out "self2.c") with
    | .ok d => pure d | .error e => return .error e
  let self2 ← IO.FS.readFile (d3 / "self2.c")
  if self1 == self2 then
    r.log s!"fixpoint: stage-1 C = stage-2 C ({self1.utf8ByteSize} bytes)"
    pure (.ok ())
  else
    pure (.error s!"no fixpoint: {firstDiff self1 self2}")
where
  firstDiff (a b : String) : String := Id.run do
    let as := a.splitOn "\n"
    let bs := b.splitOn "\n"
    for i in [0:max as.length bs.length] do
      if as[i]? != bs[i]? then
        return s!"line {i + 1}: stage 1 {(as[i]?.getD "<end>").take 200} / stage 2 {(bs[i]?.getD "<end>").take 200}"
    pure "(equal)"

/-- Build a `selfhost` target. -/
def Runner.selfhost (r : Runner) (name role : String) : IO (Except String Unit) := do
  match role with
  | "checker" | "compiler" =>
    let src ← match ← r.selfhostSource role with | .ok f => pure f | .error e => return .error e
    match ← r.link name src with
    | .error e => pure (.error e)
    | .ok exe => install exe (r.ctx.grailDir / "bin" / name); pure (.ok ())
  | "bootstrap" => r.bootstrap
  | _ => pure (.error s!"unknown self-hosted target {role} (checker, compiler, bootstrap)")

/-- Build any target. -/
def Runner.buildTarget (r : Runner) : Target → IO Bool
  | .selfhost name role => do
    match ← r.selfhost name role with
    | .ok () => pure true
    | .error e => IO.eprintln e; pure false
  | t => r.target t

end Grail
