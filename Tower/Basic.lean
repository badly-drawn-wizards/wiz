/-!
# tower: the home directory, settings, and processes (stage 26)

```
~/.tower/
  settings                 key value lines (`tower settings`)
  bin/wiz, bin/grail       shims (`tower self shims`); bin/tower (`tower self install`)
  toolchains/NAME/         one toolchain:
    bin/wiz, bin/grail       run these (the toolchain's flags are in them)
    share/wiz/lib/           the standard library
    share/wiz/.lake/build/bin/{wiz,grail}   the binaries (grail finds lib/ from there)
    share/wiz/TOOLCHAIN      a marker: editors find the toolchain a library file belongs to
    tower.info               where it came from (spec, source, ref, commit, flags)
```

A Nix toolchain's `bin` and `share` are symlinks into the store path (`nix`, a GC root).
-/

namespace Tower

/-- The toolchain flags a wrapper passes, in this order (the names of `wiz`'s flags). -/
def flagKeys : List String := ["cc", "cflags", "ldflags", "libs", "llc", "gc-cflags", "gc-ldflags"]

structure Settings where
  /-- the default toolchain (a spec) -/
  default : Option String := none
  /-- where installs come from: `auto`, `nix`, `release` or `source` -/
  source : String := "auto"
  /-- the flake (`nix` installs): `github:O/R` or a `git+…`/path flake URL -/
  flake : String := "github:wiz-pl/wiz"
  /-- the git repository (`source` installs, and resolving refs to commits) -/
  git : String := "https://github.com/wiz-pl/wiz"
  /-- release tarballs: `BASE/TAG/wiz-ARCH-linux.tar.gz` (a URL or a directory) -/
  releases : String := "https://github.com/wiz-pl/wiz/releases/download"
  /-- the branch `nightly` follows -/
  nightlyRef : String := "master"
  /-- shims install a missing toolchain on first use -/
  autoInstall : Bool := true
  /-- toolchain flags for the wrappers of non-Nix toolchains (`cc`, `cflags`, …) -/
  flags : List (String × String) := []
  /-- directory overrides: (directory, spec) -/
  overrides : List (String × String) := []
  deriving Repr, Inhabited

/-- Everything a command needs: the home directory and how shims call tower. -/
structure Env where
  home : System.FilePath
  /-- the command a shim runs to reach tower (a path, then arguments) -/
  self : List String
  deriving Inhabited

def Env.settingsFile (e : Env) : System.FilePath := e.home / "settings"
def Env.toolchains (e : Env) : System.FilePath := e.home / "toolchains"
def Env.binDir (e : Env) : System.FilePath := e.home / "bin"

/-- The value after the first space of a line. -/
def splitKey (l : String) : String × String :=
  match l.splitOn " " with
  | [] => ("", "")
  | k :: rest => (k, " ".intercalate rest)

def Settings.set (s : Settings) (k v : String) : Except String Settings :=
  match k with
  | "default" => .ok { s with default := if v.isEmpty then none else some v }
  | "source" =>
    if ["auto", "nix", "release", "source"].contains v then .ok { s with source := v }
    else .error s!"source: expected auto, nix, release or source, got {v}"
  | "flake" => .ok { s with flake := v }
  | "git" => .ok { s with git := v }
  | "releases" => .ok { s with releases := v }
  | "nightly-ref" => .ok { s with nightlyRef := v }
  | "auto-install" => .ok { s with autoInstall := v == "true" }
  | "override" =>
    let (spec, dir) := splitKey v
    .ok { s with overrides := (s.overrides.filter (·.1 != dir)) ++ [(dir, spec)] }
  | k =>
    if flagKeys.contains k then
      .ok { s with flags := (s.flags.filter (·.1 != k)) ++ (if v.isEmpty then [] else [(k, v)]) }
    else .error s!"unknown setting {k} (default, source, flake, git, releases, nightly-ref, auto-install, {", ".intercalate flagKeys})"

def Settings.parse (text : String) : Except String Settings := do
  let mut s : Settings := {}
  for l in text.splitOn "\n" do
    let l := l.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then continue
    let (k, v) := splitKey l
    s ← s.set k v.trimAscii.toString
  pure s

def Settings.render (s : Settings) : String :=
  "# tower settings (`tower set KEY VALUE`)\n" ++
  (match s.default with | some d => s!"default {d}\n" | none => "") ++
  s!"source {s.source}\nflake {s.flake}\ngit {s.git}\nreleases {s.releases}\nnightly-ref {s.nightlyRef}\n" ++
  s!"auto-install {s.autoInstall}\n" ++
  String.join (s.flags.map fun (k, v) => s!"{k} {v}\n") ++
  String.join (s.overrides.map fun (d, t) => s!"override {t} {d}\n")

def Env.settings (e : Env) : IO Settings := do
  unless ← e.settingsFile.pathExists do return {}
  match Settings.parse (← IO.FS.readFile e.settingsFile) with
  | .ok s => pure s
  | .error m => throw (IO.userError s!"{e.settingsFile}: {m}")

/-- Write a file through a temporary name and a rename (shims read it concurrently). -/
def writeAtomic (f : System.FilePath) (text : String) : IO Unit := do
  if let some d := f.parent then IO.FS.createDirAll d
  let tmp := f.toString ++ s!".tmp{← IO.monoNanosNow}"
  IO.FS.writeFile tmp text
  IO.FS.rename tmp f

def Env.saveSettings (e : Env) (s : Settings) : IO Unit := writeAtomic e.settingsFile s.render

/-! ## Processes -/

/-- Lake and Lean variables of the process that runs us (the test driver runs under
`lake test`): a build in another checkout must not see them. -/
def leanVars : List String :=
  ["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP", "LEAN", "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT",
   "LEAN_AR", "LEAN_CC", "ELAN_TOOLCHAIN", "LD_LIBRARY_PATH"]

/-- Run a command, capturing its output; `.error` with its output when it fails. -/
def run (cmd : String) (args : List String) (cwd : Option System.FilePath := none)
    (cleanEnv : Bool := false) : IO (Except String String) := do
  try
    let env := if cleanEnv then (leanVars.map fun v => (v, none)).toArray else #[]
    let o ← IO.Process.output { cmd, args := args.toArray, cwd, env }
    pure (if o.exitCode == 0 then .ok o.stdout.trimAscii.toString
      else .error s!"{cmd} {" ".intercalate args}: exit {o.exitCode}\n{(o.stderr ++ o.stdout).trimAscii}")
  catch e => pure (.error s!"{cmd}: {e}")

def runOrThrow (cmd : String) (args : List String) (cwd : Option System.FilePath := none)
    (cleanEnv : Bool := false) : IO String := do
  match ← run cmd args cwd cleanEnv with
  | .ok o => pure o
  | .error e => throw (IO.userError e)

/-- Is `cmd` a program we can run? -/
def have? (cmd : String) (args : List String := ["--version"]) : IO Bool := do
  pure ((← run cmd args) matches .ok _)

def note (msg : String) : IO Unit := IO.eprintln s!"tower: {msg}"

/-- A shell word: single-quoted. -/
def shQuote (s : String) : String := "'" ++ s.replace "'" "'\\''" ++ "'"

def makeExecutable (f : System.FilePath) : IO Unit :=
  IO.setAccessRights f { user := { read := true, write := true, execution := true },
                         group := { read := true, execution := true },
                         other := { read := true, execution := true } }

def writeScript (f : System.FilePath) (text : String) : IO Unit := do
  writeAtomic f text
  makeExecutable f

/-- Remove a file, a symlink, or a directory tree (symlinks are not followed). -/
def removeAll (p : System.FilePath) : IO Unit := do
  match ← (p.symlinkMetadata.toBaseIO) with
  | .error _ => pure ()
  | .ok m => if m.type == .dir then IO.FS.removeDirAll p else IO.FS.removeFile p

def isHex (s : String) : Bool := !s.isEmpty && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-! ## Toolchain names and info -/

/-- A toolchain's directory name: its spec, with `/` (a branch like `agent/x`) as `--`. -/
def tcName (spec : String) : String := (spec.replace "/" "--").replace " " "-"

def Env.tcDir (e : Env) (spec : String) : System.FilePath := e.toolchains / tcName spec

/-- What `tower.info` records about an installed toolchain. -/
structure Info where
  spec : String
  source : String
  ref : String := ""
  commit : String := ""
  /-- a linked toolchain's directory -/
  path : String := ""
  flags : List (String × String) := []
  deriving Repr, Inhabited

def Info.render (i : Info) : String :=
  s!"spec {i.spec}\nsource {i.source}\nref {i.ref}\ncommit {i.commit}\npath {i.path}\n" ++
  String.join (i.flags.map fun (k, v) => s!"flag {k} {v}\n")

def Info.parse (text : String) : Info := Id.run do
  let mut i : Info := { spec := "", source := "" }
  for l in text.splitOn "\n" do
    let (k, v) := splitKey l.trimAscii.toString
    match k with
    | "spec" => i := { i with spec := v }
    | "source" => i := { i with source := v }
    | "ref" => i := { i with ref := v }
    | "commit" => i := { i with commit := v }
    | "path" => i := { i with path := v }
    | "flag" => let (fk, fv) := splitKey v; i := { i with flags := i.flags ++ [(fk, fv)] }
    | _ => pure ()
  pure i

def readInfo (dir : System.FilePath) : IO (Option Info) := do
  let f := dir / "tower.info"
  if ← f.pathExists then pure (some (Info.parse (← IO.FS.readFile f))) else pure none

/-- The installed toolchains (directory names). -/
def Env.installed (e : Env) : IO (Array String) := do
  unless ← e.toolchains.pathExists do return #[]
  let mut out := #[]
  for d in ← e.toolchains.readDir do
    if d.fileName.startsWith "." then continue
    if ← (d.path / "tower.info").pathExists then out := out.push d.fileName
  pure (out.qsort (· < ·))

end Tower
