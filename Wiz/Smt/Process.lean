import Std.Data.HashMap

/-!
# Calling solvers from the (pure) elaborator (stage 28)

The elaborator is a pure function (`ElabM` is a state monad over `Except`), but the
`smt` and `sat_decide` tactics ask an external solver. `runSolver` runs one as a process,
through `unsafeBaseIO` behind an `opaque`, as the module cache does (`isoGet`,
Frontend.lean). It stays a function of its arguments in the sense that matters:

* the answer is kept in a cache file under a key that is the hash of the solver's
  identity (its path and `--version` output), its arguments and the whole input, so a
  second run with the same query replays the same answer (and needs no solver);
* without a cache directory (`--no-cache`), the solver runs every time.

What a solver says is trusted only by the `smt` tactic behind `--trust-smt` (its answer
`unsat` becomes an axiom); `sat_decide` checks the solver's LRAT proof in the kernel, so
there a wrong or nondeterministic answer can only make the tactic fail.
-/

namespace Wiz.Smt

/-- How the elaborator reaches solvers (from the toolchain: `--trust-smt`, `--smt-solver`,
`--sat-solver`, `--smt-timeout`, and the cache directory). -/
structure Config where
  /-- `--trust-smt`: the `smt` tactic may close goals on a solver's word -/
  trust : Bool := false
  /-- the SMT solver (Z3's command line) -/
  solver : String := "z3"
  /-- the SAT solver (CaDiCaL's command line: `cadical IN OUT --lrat --no-binary`) -/
  satSolver : String := "cadical"
  /-- milliseconds per query -/
  timeoutMs : Nat := 10000
  /-- where answers are kept (`<cache>/smt`); none: not kept -/
  cacheDir : Option String := none
  deriving Repr, Inhabited, BEq, Hashable

/-- What a process run gave: its exit code, its standard output, and the contents of the
file it was asked to write (if any). -/
structure Answer where
  exitCode : UInt32
  stdout : String
  outFile : String
  deriving Repr, Inhabited

private def sep : String := "\n\x00wiz-smt\x00\n"

private def hex (k : UInt64) : String :=
  let s := (Nat.toDigits 16 k.toNat).asString
  "".pushn '0' (16 - s.length) ++ s

/-- Per process: the identity of each solver (`path --version`), computed once. -/
initialize solverIds : IO.Ref (Std.HashMap String String) ← IO.mkRef {}

private def solverId (cmd : String) : IO String := do
  if let some v := (← solverIds.get).get? cmd then return v
  let v ← try
      let out ← IO.Process.output { cmd, args := #["--version"] }
      pure s!"{cmd} {out.stdout.trim}"
    catch _ => pure s!"{cmd} (not found)"
  solverIds.modify (·.insert cmd v)
  pure v

private def runIO (cfg : Config) (cmd : String) (args : List String) (input : String) (inExt : String)
    (wantOut : Bool) : IO (Except String (String × Answer)) := do
  let id ← solverId cmd
  if id.endsWith "(not found)" then
    return .error s!"the solver `{cmd}` is not installed (not on PATH)"
  let key := hash (id, args, input)
  let dir : System.FilePath ← match cfg.cacheDir with
    | some d => pure (System.FilePath.mk d / "smt")
    | none => do pure ((← IO.FS.createTempDir) / "q")
  IO.FS.createDirAll dir
  let base := dir / hex key
  let ansFile := base.addExtension "ans"
  if cfg.cacheDir.isSome && (← ansFile.pathExists) then
    let txt ← IO.FS.readFile ansFile
    match txt.splitOn sep with
    | [code, out, file] => return .ok (id, { exitCode := code.toNat!.toUInt32, stdout := out, outFile := file })
    | _ => pure ()
  let inFile := base.addExtension inExt
  let outPath := base.addExtension "out"
  IO.FS.writeFile inFile input
  let args := args.map fun a => if a == "{in}" then inFile.toString else if a == "{out}" then outPath.toString else a
  let r ← try
      let out ← IO.Process.output { cmd, args := args.toArray }
      let file ← if wantOut && (← outPath.pathExists) then IO.FS.readFile outPath else pure ""
      pure (.ok { exitCode := out.exitCode, stdout := out.stdout, outFile := file : Answer })
    catch e => pure (.error s!"running `{cmd}` failed: {e}")
  try IO.FS.removeFile inFile catch _ => pure ()
  try IO.FS.removeFile outPath catch _ => pure ()
  match r with
  | .ok a =>
    if cfg.cacheDir.isSome then
      IO.FS.writeFile ansFile s!"{a.exitCode}{sep}{a.stdout}{sep}{a.outFile}"
    pure (.ok (id, a))
  | .error e => pure (.error e)

private unsafe def runSolverImpl (cfg : Config) (cmd : String) (args : List String) (input : String)
    (inExt : String) (wantOut : Bool) : Except String (String × Answer) :=
  match unsafeBaseIO (runIO cfg cmd args input inExt wantOut).toBaseIO with
  | .ok r => r
  | .error e => .error s!"running `{cmd}` failed: {e}"

/-- Run solver `cmd` with `args` (`{in}`: a file holding `input`, with extension `inExt`;
`{out}`: a file it writes, read back if `wantOut`). The solver's identity and the answer,
or why there is none. Cached (see above). -/
@[implemented_by runSolverImpl]
opaque runSolver (cfg : Config) (cmd : String) (args : List String) (input : String)
    (inExt : String) (wantOut : Bool) : Except String (String × Answer)

/-- A solver's identity in a few words, for an axiom's name: the command's base name and
the first version-looking word of its `--version` (`z3 4.13.0`). -/
def shortId (id : String) : String :=
  let ws := (id.splitOn " ").filter (· ≠ "")
  let cmd := ((ws.headD "solver").splitOn "/").getLast!
  match ws.drop 1 |>.find? (fun w => w.any Char.isDigit && w.contains '.') with
  | some v => s!"{cmd} {v}"
  | none => cmd

end Wiz.Smt
