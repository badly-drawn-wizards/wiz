import Grail.Config

/-!
# The build graph (stage 23d: sequential)

A **job** has a key, computed from its inputs before it runs, and an output directory
`.grail/build/<key>/`. A job whose directory exists is up to date and doesn't run; a job
that runs writes into a temporary directory that is renamed into place when it
succeeds, so an interrupted build leaves nothing half-written. Keys:

* `check F`: the file's key (`Cache.moduleKey`: its text, headers, and its imports'
  keys, transitively), mixed with `binId` (this grail binary: elaborator and backends);
* `ir F` from `check F`; `c F` from `ir F`;
* `obj F` from the text of `main.c` and the compiler and `cflags`;
* `link E` from `obj F` and the compiler and `ldflags`.

So editing a module reruns the checks of the files that import it, and an edit that
doesn't change the generated C stops at `obj`.
-/

namespace Grail
open Wiz

structure Ctx where
  /-- the package directory -/
  dir : System.FilePath
  /-- the standard library (`lib/`) -/
  std : System.FilePath
  tc : Toolchain
  /-- identifies this grail binary -/
  binId : UInt64
  /-- the roots of the package's `lib` targets: their modules can be imported -/
  libRoots : List System.FilePath := []

def Ctx.roots (c : Ctx) : List System.FilePath := [c.std, c.dir] ++ c.libRoots ++ c.tc.searchPath

def libRootsOf (dir : System.FilePath) (ts : List Target) : List System.FilePath :=
  ts.filterMap fun | .lib _ r => some (dir / r) | _ => none
def Ctx.grailDir (c : Ctx) : System.FilePath := c.dir / ".grail"

structure Stats where
  ran : Nat := 0
  upToDate : Nat := 0
  failed : Nat := 0

def hex (k : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 k.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- A file's elaborated state and its loaded form, made at most once per run. -/
structure Memo where
  loaded : Std.HashMap String Loaded := {}
  states : Std.HashMap String (CommandState ZeroOneMany) := {}

structure Runner where
  ctx : Ctx
  stats : IO.Ref Stats
  memo : IO.Ref Memo
  /-- print each job as it runs -/
  log : String → IO Unit := IO.println

/-- Run a job unless its output directory exists. `act` writes into a fresh directory. -/
def Runner.job (r : Runner) (label : String) (key : UInt64) (act : System.FilePath → IO (Except String Unit)) :
    IO (Except String System.FilePath) := do
  let out := r.ctx.grailDir / "build" / hex key
  if ← out.pathExists then
    r.stats.modify fun s => { s with upToDate := s.upToDate + 1 }
    return .ok out
  r.log s!"[{label}]"
  let tmp : System.FilePath := r.ctx.grailDir / "tmp" / s!"{hex key}-{← IO.Process.getPID}-{← IO.monoNanosNow}"
  IO.FS.createDirAll tmp
  let res ← try act tmp catch e => pure (.error (toString e))
  match res with
  | .error e =>
    IO.FS.removeDirAll tmp
    r.stats.modify fun s => { s with failed := s.failed + 1 }
    pure (.error e)
  | .ok () =>
    IO.FS.createDirAll (r.ctx.grailDir / "build")
    try IO.FS.rename tmp out
    catch _ => IO.FS.removeDirAll tmp   -- someone else made it first
    r.stats.modify fun s => { s with ran := s.ran + 1 }
    pure (.ok out)

def Runner.load (r : Runner) (file : String) : IO Loaded := do
  if let some l := (← r.memo.get).loaded[file]? then return l
  let l ← Grail.load r.ctx.tc r.ctx.roots r.ctx.binId (← IO.FS.readFile (r.ctx.dir / file))
  r.memo.modify fun m => { m with loaded := m.loaded.insert file l }
  pure l

def Runner.elab (r : Runner) (file : String) : IO (CommandState ZeroOneMany) := do
  if let some s := (← r.memo.get).states[file]? then return s
  let s ← elaborate r.ctx.tc r.ctx.binId (← r.load file)
  r.memo.modify fun m => { m with states := m.states.insert file s }
  pure s

/-- Check a file (relative to the package directory). -/
def Runner.check (r : Runner) (file : String) : IO (Except String UInt64) := do
  let l ← r.load file
  let key := mixHash (hash "check") (mixHash r.ctx.binId l.key)
  let res ← r.job s!"check {file}" key fun out => do
    let s ← r.elab file
    let msgs := render file l s
    if hasErrors s then return .error msgs
    IO.print msgs
    IO.FS.writeFile (out / "messages.txt") msgs
    pure (.ok ())
  pure (res.map fun _ => key)

def run (cmd : String) (args : Array String) : IO (Except String Unit) := do
  try
    let o ← IO.Process.output { cmd, args }
    pure (if o.exitCode == 0 then .ok () else .error s!"{cmd} failed:\n{o.stderr}")
  catch e => pure (.error s!"{cmd}: {e}")

/-- Copy a file if its content differs. -/
def install (src dst : System.FilePath) : IO Unit := do
  let new ← IO.FS.readBinFile src
  if ← dst.pathExists then
    if (← IO.FS.readBinFile dst) == new then return
  if let some d := dst.parent then IO.FS.createDirAll d
  let tmp := dst.toString ++ s!".tmp{← IO.Process.getPID}"
  IO.FS.writeBinFile tmp new
  IO.setAccessRights tmp { user := { read := true, write := true, execution := true },
                           group := { read := true, execution := true }, other := { read := true, execution := true } }
  IO.FS.rename tmp dst

/-- Build the executable `name` from `file`'s `main`: check → IR → C → object → link,
installed as `.grail/bin/<name>`. -/
def Runner.exe (r : Runner) (name file : String) : IO (Except String System.FilePath) := do
  let ck ← match ← r.check file with | .ok k => pure k | .error e => return .error e
  let tc := r.ctx.tc
  let decls (s : CommandState ZeroOneMany) : Except String (Array IR.Decl × Bool) := do
    let (ds, ty) ← Build.irProgram s "main"
    pure (ds, Build.isIO ty)
  let irKey := mixHash (hash "ir") ck
  let _ ← match ← r.job s!"ir {file}" irKey (fun out => do
      match decls (← r.elab file) with
      | .error e => pure (.error e)
      | .ok (ds, _) =>
        IO.FS.writeFile (out / "main.ir") ("\n".intercalate (ds.toList.map (·.toString)))
        pure (.ok ())) with | .ok d => pure d | .error e => return .error e
  let cKey := mixHash (hash "c") irKey
  let cDir ← match ← r.job s!"c {file}" cKey (fun out => do
      let s ← r.elab file
      match decls s with
      | .error e => pure (.error e)
      | .ok (ds, io) =>
        IO.FS.writeFile (out / "main.c") (C.program ds io (Build.extraC s))
        pure (.ok ())) with | .ok d => pure d | .error e => return .error e
  let cText ← IO.FS.readFile (cDir / "main.c")
  let objKey := mixHash (hash "obj") (hash (toString [cText, tc.cc, " ".intercalate tc.cflags]))
  let oDir ← match ← r.job s!"obj {file}" objKey (fun out =>
      run tc.cc (#["-O2", "-w", "-c", "-o", (out / "main.o").toString, (cDir / "main.c").toString] ++ tc.cflags.toArray)) with
    | .ok d => pure d | .error e => return .error e
  let linkKey := mixHash (hash "link") (hash (toString [toString objKey, tc.cc, " ".intercalate tc.ldflags, " ".intercalate tc.libs]))
  let lDir ← match ← r.job s!"link {name}" linkKey (fun out =>
      run tc.cc (#["-o", (out / name).toString, (oDir / "main.o").toString, "-lgmp"] ++ tc.ldflags.toArray ++ tc.libs.toArray)) with
    | .ok d => pure d | .error e => return .error e
  let dst := r.ctx.grailDir / "bin" / name
  install (lDir / name) dst
  pure (.ok dst)

/-- Build one target. -/
def Runner.target (r : Runner) : Target → IO Bool
  | .check _ file => do
    match ← r.check file with
    | .ok _ => pure true
    | .error e => IO.eprint e; pure false
  | .lib _ root => do
    let mut ok := true
    for (m, _) in ← Module.listRoot (r.ctx.dir / root) do
      match ← r.check (System.FilePath.mk root / Module.relPath m).toString with
      | .ok _ => pure ()
      | .error e => IO.eprint e; ok := false
    pure ok
  | .exe name file => do
    match ← r.exe name file with
    | .ok _ => pure true
    | .error e => IO.eprintln e; pure false

end Grail
