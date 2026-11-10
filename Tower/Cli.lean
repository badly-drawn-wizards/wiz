import Tower.Install

/-!
# tower's commands (stage 26c)

Which toolchain runs in a directory (`tower show`): a `+SPEC` first argument of a shim,
else, walking up from the directory, an override set for it (`tower override set`) or a
`wiz-toolchain` file in it, else the default (`tower default`).

The shims (`~/.tower/bin/wiz`, `…/grail`) are shell scripts: they ask tower for the
toolchain's directory (`tower resolve`, which installs it on first use) and `exec` its
`bin/TOOL`, so the process that runs is the toolchain's own (signals, exit codes and the
language server's stdio are untouched).
-/

namespace Tower

def usage : String := "tower: Wiz toolchains (stage 26)

usage: tower [--home DIR] COMMAND

  toolchain install SPEC… [--source auto|nix|release|source] [--force] [--cflags …]
  toolchain uninstall NAME…
  toolchain list
  toolchain link NAME DIR [--cflags …]   a checkout (.lake/build/bin) or a toolchain dir
  default [SPEC]                 show or set the default toolchain (installs it)
  override set SPEC [DIR]        DIR (default: here) uses SPEC
  override unset [DIR]
  override list
  show                           the toolchain here, and why
  which TOOL                     the path of TOOL (wiz, grail) in the toolchain here
  run SPEC [--] CMD ARGS…        run CMD with SPEC's bin/ first on PATH
  update [NAME…]                 reinstall channel and branch toolchains that moved
  set KEY VALUE / settings       settings (source, flake, git, releases, nightly-ref,
                                 auto-install, cc, cflags, ldflags, libs, llc,
                                 gc-cflags, gc-ldflags)
  self shims                     write the shims in ~/.tower/bin
  self install                   copy tower to ~/.tower/bin and write the shims

SPEC: nightly, stable, a tag, a branch, a commit, REF@COMMIT, or a linked name.
A project names its toolchain in a file `wiz-toolchain` (one line: a SPEC).
"

/-- The tools that get a shim. -/
def tools : List String := ["wiz", "grail"]

/-- The spec in a `wiz-toolchain` file: its first line that isn't blank or a comment. -/
def readToolchainFile (f : System.FilePath) : IO (Option String) := do
  let ls := (← IO.FS.readFile f).splitOn "\n" |>.map (·.trimAscii.toString)
  pure (ls.find? fun l => !l.isEmpty && !l.startsWith "#" && !l.startsWith "--")

/-- The toolchain for `dir`, and why. -/
partial def active (e : Env) (dir : System.FilePath) : IO (Option (String × String)) := do
  let s ← e.settings
  let rec go (d : System.FilePath) : IO (Option (String × String)) := do
    if let some (_, spec) := s.overrides.find? (·.1 == d.toString) then
      return some (spec, s!"override for {d}")
    let f := d / "wiz-toolchain"
    if ← f.pathExists then
      if let some spec ← readToolchainFile f then return some (spec, s!"{f}")
    match d.parent with
    | some p => if p == d then pure none else go p
    | none => pure none
  match ← go (← IO.FS.realPath dir) with
  | some r => pure (some r)
  | none => pure (s.default.map (·, "the default toolchain"))

/-- The toolchain directory for a spec, installing it if allowed. -/
def ensure (e : Env) (spec : String) (allowInstall : Bool) : IO (Except String System.FilePath) := do
  let d := e.tcDir spec
  if ← (d / "tower.info").pathExists then return .ok d
  unless allowInstall do return .error s!"toolchain {spec} is not installed (tower toolchain install {spec})"
  note s!"toolchain {spec} is not installed; installing it"
  install e spec

def fail (m : String) : IO UInt32 := do IO.eprintln s!"tower: {m}"; pure 1

/-- Take `--flag VALUE` toolchain flags, `--source X`, `--force` out of the arguments. -/
partial def installOpts : List String → List (String × String) × Option String × Bool × List String
  | "--source" :: v :: rest => let (f, _, force, r) := installOpts rest; (f, some v, force, r)
  | "--force" :: rest => let (f, s, _, r) := installOpts rest; (f, s, true, r)
  | flag :: v :: rest =>
    let k := (flag.drop 2).toString
    if flag.startsWith "--" && flagKeys.contains k then
      let (f, s, force, r) := installOpts rest; ((k, v) :: f, s, force, r)
    else let (f, s, force, r) := installOpts (v :: rest); (f, s, force, flag :: r)
  | [a] => ([], none, false, [a])
  | [] => ([], none, false, [])

def shimText (e : Env) (tool : String) : String :=
  let self := " ".intercalate (e.self.map shQuote) ++ " --home " ++ shQuote e.home.toString
  s!"#!/bin/sh
# tower shim: runs `{tool}` of the toolchain for this directory (`tower show`).
# Written by `tower self shims`; it is overwritten.
case \"$1\" in
  +*) tc=$({self} resolve \"$1\") || exit; shift ;;
  *) tc=$({self} resolve) || exit ;;
esac
exec \"$tc/bin/{tool}\" \"$@\"
"

def writeShims (e : Env) : IO Unit := do
  for t in tools do writeScript (e.binDir / t) (shimText e t)

def describe (e : Env) (name : String) (s : Settings) (here : Option String) : IO String := do
  let i ← readInfo (e.toolchains / name)
  let what := match i with
    | some i => if i.source == "link" then s!"link {i.path}"
      else s!"{i.source}, {i.ref}{if i.commit.isEmpty then "" else "@" ++ i.commit.take 12}"
    | none => "?"
  let spec := (i.map (·.spec)).getD name
  let marks := (if s.default == some spec then [" (default)"] else []) ++ (if here == some spec then [" (here)"] else [])
  pure s!"{spec}  [{what}]{String.join marks}"

def toolchainCmd (e : Env) : List String → IO UInt32
  | "install" :: args => do
    let (flags, source, force, specs) := installOpts args
    if specs.isEmpty then return ← fail "toolchain install: which toolchain?"
    let mut status := 0
    for spec in specs do
      match ← install e spec source force flags with
      | .ok d => IO.println d.toString
      | .error m => status := 1; IO.eprintln s!"tower: {spec}: {m}"
    pure status
  | "uninstall" :: names => do
    let mut status := 0
    for n in names do
      let d := e.tcDir n
      if ← d.pathExists then removeAll d; note s!"removed {n}"
      else status := 1; IO.eprintln s!"tower: {n} is not installed"
    pure status
  | ["list"] => do
    let s ← e.settings
    let here := (← active e (← IO.currentDir)).map (·.1)
    for n in ← e.installed do IO.println (← describe e n s here)
    pure 0
  | "link" :: args => do
    let (flags, _, _, rest) := installOpts args
    let [name, dir] := rest | fail "toolchain link NAME DIR"
    match ← link e name dir flags with
    | .ok d => IO.println d.toString; pure 0
    | .error m => fail m
  | _ => do IO.eprint usage; pure 2

def overrideCmd (e : Env) : List String → IO UInt32
  | "set" :: spec :: rest => do
    let dir ← IO.FS.realPath (rest.head?.getD ".")
    let s ← e.settings
    e.saveSettings { s with overrides := (s.overrides.filter (·.1 != dir.toString)) ++ [(dir.toString, spec)] }
    note s!"{dir} uses {spec}"
    pure 0
  | "unset" :: rest => do
    let dir ← IO.FS.realPath (rest.head?.getD ".")
    let s ← e.settings
    unless s.overrides.any (·.1 == dir.toString) do return ← fail s!"no override for {dir}"
    e.saveSettings { s with overrides := s.overrides.filter (·.1 != dir.toString) }
    pure 0
  | ["list"] => do
    for (d, t) in (← e.settings).overrides do IO.println s!"{d}  {t}"
    pure 0
  | _ => do IO.eprint usage; pure 2

/-- The spec for the shims: `+SPEC`, or the one for the current directory. -/
def specHere (e : Env) (plus : Option String) : IO (Except String String) := do
  if let some p := plus then return .ok (p.drop 1).toString
  match ← active e (← IO.currentDir) with
  | some (spec, _) => pure (.ok spec)
  | none => pure (.error "no toolchain here: no wiz-toolchain file, override or default (tower default nightly)")

def update (e : Env) (names : List String) : IO UInt32 := do
  let s ← e.settings
  let all := (← e.installed).toList
  let names := if names.isEmpty then all else names
  let mut status := 0
  for n in names do
    let some i ← readInfo (e.toolchains / n) | do status := 1; IO.eprintln s!"tower: {n} is not installed"; continue
    if i.source == "link" || (i.spec.splitOn "@").length == 2 then continue
    match ← resolveSpec s i.spec with
    | .error m => status := 1; IO.eprintln s!"tower: {n}: {m}"
    | .ok w =>
      if w.commit == some i.commit then IO.println s!"{i.spec}: up to date"; continue
      match ← install e i.spec (some i.source) true i.flags with
      | .ok _ => pure ()
      | .error m => status := 1; IO.eprintln s!"tower: {n}: {m}"
  pure status

partial def globalOpts (e : Env) : List String → Env × List String
  | "--home" :: d :: rest => globalOpts { e with home := d } rest
  | "--self" :: p :: rest => globalOpts { e with self := [p] } rest
  | "--self-arg" :: a :: rest => globalOpts { e with self := e.self ++ [a] } rest
  | rest => (e, rest)

def runIn (dir : System.FilePath) (cmd : String) (args : List String) : IO UInt32 := do
  let path := (← IO.getEnv "PATH").getD ""
  let child ← IO.Process.spawn { cmd, args := args.toArray, env := #[("PATH", some s!"{dir / "bin"}:{path}")],
                                 stdin := .inherit, stdout := .inherit, stderr := .inherit }
  child.wait

def selfCmd (e : Env) : List String → IO UInt32
  | ["shims"] => do
    writeShims e
    note s!"shims for {", ".intercalate tools} in {e.binDir}; put it first on PATH"
    pure 0
  | ["install"] => do
    let exe ← IO.appPath
    let e ← if exe.toString.startsWith "/nix/store/" then pure e else do
      let dst := e.binDir / "tower"
      IO.FS.createDirAll e.binDir
      if exe != dst then
        let tmp := e.binDir / s!".tower.tmp{← IO.monoNanosNow}"
        IO.FS.writeBinFile tmp (← IO.FS.readBinFile exe)
        makeExecutable tmp
        IO.FS.rename tmp dst
      pure { e with self := [dst.toString] }
    writeShims e
    note s!"tower and shims in {e.binDir}: add it to PATH, e.g. export PATH=\"{e.binDir}:$PATH\""
    pure 0
  | _ => do IO.eprint usage; pure 2

def main (e : Env) (args : List String) : IO UInt32 := do
  let (e, args) := globalOpts e args
  try
    match args with
    | "toolchain" :: rest => toolchainCmd e rest
    | "install" :: rest => toolchainCmd e ("install" :: rest)
    | "uninstall" :: rest => toolchainCmd e ("uninstall" :: rest)
    | ["list"] => toolchainCmd e ["list"]
    | "link" :: rest => toolchainCmd e ("link" :: rest)
    | ["default"] => do
      match (← e.settings).default with
      | some d => IO.println d; pure 0
      | none => fail "no default toolchain (tower default nightly)"
    | ["default", spec] => do
      if let .error m ← ensure e spec true then return ← fail m
      e.saveSettings { (← e.settings) with default := some spec }
      note s!"default toolchain: {spec}"
      pure 0
    | "override" :: rest => overrideCmd e rest
    | ["show"] => do
      match ← active e (← IO.currentDir) with
      | some (spec, why) =>
        let d := e.tcDir spec
        let inst := if ← (d / "tower.info").pathExists then d.toString else "not installed"
        IO.println s!"{spec}\n  from {why}\n  {inst}"; pure 0
      | none => fail "no toolchain here (no wiz-toolchain file, override or default)"
    | "resolve" :: rest => do
      let spec ← match ← specHere e rest.head? with
        | .ok s => pure s
        | .error m => return ← fail m
      match ← ensure e spec (← e.settings).autoInstall with
      | .ok d => IO.println d.toString; pure 0
      | .error m => fail m
    | ["which", tool] => do
      let spec ← match ← specHere e none with
        | .ok s => pure s
        | .error m => return ← fail m
      match ← ensure e spec (← e.settings).autoInstall with
      | .error m => fail m
      | .ok d =>
        let p := d / "bin" / tool
        if ← p.pathExists then IO.println p.toString; pure 0
        else fail s!"{spec} has no {tool}"
    | "run" :: spec :: rest => do
      let cmd := if rest.head? == some "--" then rest.drop 1 else rest
      let c :: args := cmd | fail "run SPEC -- CMD ARGS…"
      match ← ensure e spec (← e.settings).autoInstall with
      | .ok d => runIn d c args
      | .error m => fail m
    | "update" :: names => update e names
    | ["set", k] => do
      match (← e.settings).set k "" with
      | .ok s => e.saveSettings s; pure 0
      | .error m => fail m
    | "set" :: k :: v => do
      match (← e.settings).set k (" ".intercalate v) with
      | .ok s => e.saveSettings s; pure 0
      | .error m => fail m
    | ["settings"] => do IO.print (← e.settings).render; pure 0
    | "self" :: rest => selfCmd e rest
    | ["--help"] | ["help"] | [] => do IO.print usage; pure 0
    | _ => do IO.eprint usage; pure 2
  catch err => fail (toString err)

/-- The environment of a `tower` process: `~/.tower`, and this binary for the shims. -/
def defaultEnv : IO Env := do
  let home := (← IO.getEnv "HOME").getD "."
  pure { home := System.FilePath.mk home / ".tower", self := [(← IO.appPath).toString] }

end Tower
