import Grail.Graph
import Grail.Deps

/-!
# grail, a build tool for Wiz

`grail build [TARGET…]` builds the targets of the package in the current directory
(all of them by default), as described by its `grail.wiz`. See docs/stages/23-grail.md.
-/

namespace Grail
open Wiz

def usage : String := "usage:
  grail build [TARGET…]   build the package's targets (by default all but the
                          bootstrap check, which takes minutes)
  grail test [FILTER…] [--update]
                          run the tests (of `tests` targets) whose path contains a
                          filter; --update writes the actual output to .expected
  grail update            resolve the git dependencies again and write grail.lock
                          (builds use the lock only)
  grail run TARGET [-- ARGS…]
                          build an exe or command target's needs and run it with
                          ARGS, its input and output grail's own; exits with its code
  grail targets           list the targets
  grail config            print the toolchain grail would use
  grail clean             remove .grail/build, .grail/bin, .grail/tmp, .grail/log and
                          the command outputs grail installed (unless changed since)
options: -C DIR (the package directory), --std DIR (the standard library),
  -j N (jobs at once; default: the number of cores, at most 4),
  --timeout SECS (a job's time limit, default 1800), --test-timeout SECS (default 300),
  --cc X --cflags \"…\" --ldflags \"…\" --libs \"…\" --llc X --gc-cflags \"…\" --gc-ldflags \"…\" -I DIR,
  --cache DIR (the elaboration cache, default ~/.cache/wiz), --no-cache
Machine settings (where GMP lives) go in an uncommitted grail.local.wiz:
  import Grail
  def settings : Settings := Settings.empty |> Settings.set \"cflags\" \"-I…\""

/-- What identifies this binary (so a new elaborator or backend rebuilds everything):
`Cache.binaryId`, remembered under the cache directory. -/
def binaryId (cacheDir : Option System.FilePath) : IO UInt64 := Cache.binaryId cacheDir

structure Opts where
  dir : Option String := none
  std : Option String := none
  jobs : Option Nat := none
  timeout : Option Nat := none
  testTimeout : Option Nat := none

/-- `-C DIR`, `--std DIR`, `-j N`, `--timeout SECS`, `--test-timeout SECS`, taken out of the arguments. -/
partial def grailOpts (o : Opts) : List String → Opts × List String
  | "-C" :: d :: rest => grailOpts { o with dir := some d } rest
  | "--std" :: d :: rest => grailOpts { o with std := some d } rest
  | "-j" :: n :: rest => grailOpts { o with jobs := n.toNat? } rest
  | "--timeout" :: n :: rest => grailOpts { o with timeout := n.toNat? } rest
  | "--test-timeout" :: n :: rest => grailOpts { o with testTimeout := n.toNat? } rest
  | a :: rest =>
    if a.startsWith "-j" && (a.drop 2).toString.toNat?.isSome then grailOpts { o with jobs := (a.drop 2).toString.toNat? } rest
    else let (o, r) := grailOpts o rest; (o, a :: r)
  | [] => (o, [])

/-- The standard library: `--std`, else `lib/` of the checkout this binary was built in
(`.lake/build/bin/grail`), else `./lib`. -/
def findStd (opt : Option String) : IO System.FilePath := do
  if let some d := opt then return d
  let exe ← IO.appPath
  let guess := ((((exe.parent.bind (·.parent)).bind (·.parent)).bind (·.parent)).getD ".") / "lib"
  if ← (guess / "Prelude.wiz").pathExists then return guess
  pure "lib"

def cliMain (args : List String) : IO UInt32 := do
  -- (23k) the supervisor of a job process
  if let "--grail-exec" :: rest := args then return ← execMain rest
  let home := (← IO.getEnv "HOME").getD "."
  let defaults : Toolchain := { cacheDir := some (System.FilePath.mk home / ".cache" / "wiz") }
  -- a job of a build, in its own process (`Grail/Graph.lean`)
  if let "--grail-job" :: job :: flags := args then
    return ← jobMain (defaults.parseFlags flags).1 job
  -- `grail run TARGET -- ARGS…`: what follows `--` is the program's
  let (args, runArgs) := match args.idxOf? "--" with
    | some i => (args.take i, (args.drop (i + 1)).toArray)
    | none => (args, #[])
  let (opts, args) := grailOpts {} args
  let dir : System.FilePath := opts.dir.getD "."
  let std ← findStd opts.std
  let jobs := opts.jobs.getD (max 1 (min 4 (System.Platform.Internal.getHardwareConcurrency ()).toNat))
  let mkRunner (ctx : Ctx) : IO Runner := do
    pure { ctx, stats := ← IO.mkRef {}, memo := ← IO.mkRef {}, jobs, self := ← IO.appPath,
           timeoutMs := 1000 * opts.timeout.getD 1800, testTimeoutMs := 1000 * opts.testTimeout.getD 300 }
  -- the flags win over the build files; read them now, apply them last
  let raw := args
  let (flagged, args) := defaults.parseFlags args
  let binId ← binaryId flagged.cacheDir
  match args with
  | ["clean"] =>
    -- (23i) the outputs grail installed in the package, unless they were changed since
    IO.print (← cleanInstalled { dir, std, tc := defaults, binId })
    for d in ["build", "bin", "tmp", "log"] do
      if ← (dir / ".grail" / d).pathExists then IO.FS.removeDirAll (dir / ".grail" / d)
    pure 0
  | "build" :: _ | "test" :: _ | ["targets"] | ["config"] | ["update"] | ["run", _] =>
    let (pkg, localSettings) ← match ← readConfig flagged binId std dir with
      | .ok r => pure r
      | .error e => do IO.eprintln e; return 1
    let mut tc := defaults
    for (k, v) in pkg.settings ++ localSettings do
      match tc.set k v with
      | some t => tc := t
      | none => IO.eprintln s!"unknown setting {k}"; return 1
    -- the flags again, over the build files
    tc := (tc.parseFlags raw).1
    -- a dependency's build file
    let readPkg (d : System.FilePath) : IO (Except String Package) := do
      pure ((← readConfig tc binId std d).map (·.1))
    let depRoots : IO (Option (List System.FilePath)) := do
      match ← lockedRoots readPkg dir pkg IO.eprint with
      | .ok rs => pure (some rs)
      | .error e => IO.eprintln e; pure none
    match args with
    | ["config"] => IO.print tc.render; pure 0
    | ["update"] =>
      match ← update readPkg dir pkg with
      | .error e => IO.eprintln e; pure 1
      | .ok ls =>
        for l in ls do IO.println s!"{l.name}\t{l.url} {l.rev}\t{l.commit}"
        pure 0
    | ["targets"] =>
      for t in pkg.targets do
        match t with
        | .command c =>
          let tool := match c.tool with | .path n => n | .exe n => s!"exe {n}"
          let kind := if c.phony then "phony command" else if c.manual then "command (manual)" else "command"
          IO.println s!"{t.name}\t{kind}: {tool}, {c.inputs.length} inputs, outputs {c.outputPaths}"
        | _ => IO.println s!"{t.name}\t{repr t}"
      pure 0
    | "test" :: rest =>
      let update := rest.contains "--update"
      let filters := rest.filter (· != "--update")
      let some roots ← depRoots | return 1
      let r ← mkRunner { dir, std, tc, binId, libRoots := libRootsOf dir pkg.targets ++ roots }
      let results ← r.tests pkg.targets filters update
      let passed := results.filter (·.ok) |>.size
      let cached := results.filter (·.cached) |>.size
      IO.println s!"{passed} passed, {results.size - passed} failed ({cached} recorded passes)"
      pure (if passed == results.size then 0 else 1)
    | ["run", name] =>
      let some t := pkg.targets.find? (·.name == name) | IO.eprintln s!"no target {name}"; return 1
      let some roots ← depRoots | return 1
      -- the build's report goes to stderr: stdout is the program's
      let r ← mkRunner { dir, std, tc, binId, libRoots := libRootsOf dir pkg.targets ++ roots }
      let r := { r with out := IO.eprint }
      r.runTarget pkg.targets t runArgs
    | _ =>
      let wanted := args.drop 1
      let targets := if wanted.isEmpty then pkg.targets.filter (·.isDefault)
        else pkg.targets.filter (wanted.contains ·.name)
      for w in wanted do
        unless pkg.targets.any (·.name == w) do IO.eprintln s!"no target {w}"; return 1
      let some roots ← depRoots | return 1
      let r ← mkRunner { dir, std, tc, binId, libRoots := libRootsOf dir pkg.targets ++ roots }
      let ok ← r.build pkg.targets targets
      let st ← r.stats.get
      IO.println s!"{st.ran} jobs run, {st.upToDate} up to date{if st.failed > 0 then s!", {st.failed} failed" else ""}{if st.skipped > 0 then s!", {st.skipped} skipped" else ""}"
      pure (if ok then 0 else 1)
  | _ => IO.println usage; pure 0

end Grail
