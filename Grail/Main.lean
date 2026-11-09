import Grail.Build

/-!
# grail, a build tool for Wiz

`grail build [TARGET…]` builds the targets of the package in the current directory
(all of them by default), as described by its `grail.wiz`. See the README.
-/

open Wiz Grail

def usage : String := "usage:
  grail build [TARGET…]   build the package's targets (all by default)
  grail targets           list the targets
  grail config            print the toolchain grail would use
  grail clean             remove .grail/build and .grail/bin
options: -C DIR (the package directory), --std DIR (the standard library),
  --cc X --cflags \"…\" --ldflags \"…\" --libs \"…\" --llc X --gc-cflags \"…\" --gc-ldflags \"…\" -I DIR,
  --cache DIR (the elaboration cache, default ~/.cache/wiz), --no-cache
Machine settings (where GMP lives) go in an uncommitted grail.local.wiz:
  import Grail
  def settings : Settings := Settings.empty |> Settings.set \"cflags\" \"-I…\""

/-- What identifies this binary (so a new elaborator or backend rebuilds everything):
its hash, remembered by size and modification time in `~/.cache/grail-binid`. -/
def binaryId (cacheDir : Option System.FilePath) : IO UInt64 := do
  let exe ← IO.appPath
  let md ← exe.metadata
  let stamp := s!"{exe} {md.byteSize} {md.modified.sec} {md.modified.nsec}"
  let file := cacheDir.map (· / "grail-binid")
  if let some f := file then
    if ← f.pathExists then
      match (← IO.FS.readFile f).splitOn "\n" with
      | [st, k] => if st == stamp then if let some n := k.toNat? then return n.toUInt64
      | _ => pure ()
  let h := hash (← IO.FS.readBinFile exe)
  if let some f := file then
    IO.FS.createDirAll (f.parent.getD ".")
    Cache.writeAtomic f s!"{stamp}\n{h.toNat}"
  pure h

/-- `-C DIR` and `--std DIR`, taken out of the arguments. -/
partial def dirOpts (dir : Option String) (std : Option String) : List String → Option String × Option String × List String
  | "-C" :: d :: rest => dirOpts (some d) std rest
  | "--std" :: d :: rest => dirOpts dir (some d) rest
  | a :: rest => let (d, s, r) := dirOpts dir std rest; (d, s, a :: r)
  | [] => (dir, std, [])

/-- The standard library: `--std`, else `lib/` of the checkout this binary was built in
(`.lake/build/bin/grail`), else `./lib`. -/
def findStd (opt : Option String) : IO System.FilePath := do
  if let some d := opt then return d
  let exe ← IO.appPath
  let guess := ((((exe.parent.bind (·.parent)).bind (·.parent)).bind (·.parent)).getD ".") / "lib"
  if ← (guess / "Prelude.wiz").pathExists then return guess
  pure "lib"

def main (args : List String) : IO UInt32 := do
  let (dir, std, args) := dirOpts none none args
  let dir : System.FilePath := dir.getD "."
  let std ← findStd std
  let home := (← IO.getEnv "HOME").getD "."
  let defaults : Toolchain := { cacheDir := some (System.FilePath.mk home / ".cache" / "wiz") }
  -- the flags win over the build files; read them now, apply them last
  let raw := args
  let (flagged, args) := defaults.parseFlags args
  let binId ← binaryId flagged.cacheDir
  match args with
  | ["clean"] =>
    for d in ["build", "bin", "tmp"] do
      if ← (dir / ".grail" / d).pathExists then IO.FS.removeDirAll (dir / ".grail" / d)
    pure 0
  | "build" :: _ | ["targets"] | ["config"] =>
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
    match args with
    | ["config"] => IO.print tc.render; pure 0
    | ["targets"] =>
      for t in pkg.targets do IO.println s!"{t.name}\t{repr t}"
      pure 0
    | _ =>
      let wanted := args.drop 1
      let targets := if wanted.isEmpty then pkg.targets else pkg.targets.filter (wanted.contains ·.name)
      for w in wanted do
        unless pkg.targets.any (·.name == w) do IO.eprintln s!"no target {w}"; return 1
      let r : Runner := { ctx := { dir, std, tc, binId, libRoots := libRootsOf dir pkg.targets }, stats := ← IO.mkRef {}, memo := ← IO.mkRef {} }
      let mut ok := true
      for t in targets do
        ok := (← r.target t) && ok
      let st ← r.stats.get
      IO.println s!"{st.ran} jobs run, {st.upToDate} up to date{if st.failed > 0 then s!", {st.failed} failed" else ""}"
      pure (if ok then 0 else 1)
  | _ => IO.println usage; pure 0
