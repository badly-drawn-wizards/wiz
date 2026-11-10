import Tower.Basic

/-!
# Installing toolchains (stage 26b)

A **spec** names a toolchain: a channel (`nightly`: the branch `nightly-ref`, `stable`:
the highest `vX.Y.Z` tag), a ref (a tag, a branch, a commit), or `REF@COMMIT` (a commit,
with the ref it came from as documentation; `solutions@<sha>`). Installing resolves the
spec to a commit with `git ls-remote` on the `git` setting, then realises it from one
source:

* `nix`: `nix build FLAKE/COMMIT#wiz`, the package of `flake.nix` (from the Cachix cache
  `badlydrawnwizards` when the user is trusted), linked as a GC root;
* `release`: the tarball `RELEASES/TAG/wiz-ARCH-linux.tar.gz` that CI attaches to the
  GitHub release of a tag (and to `nightly`); only tags and channels have one;
* `source`: `git clone` + `lake build wiz grail` (needs elan).

`auto` (the default) takes `nix` when `nix` runs, else the release when there is one, else
the source. A toolchain is built in `toolchains/.tmp-…` and renamed into place, so a
shim never sees half of one.
-/

namespace Tower

/-- What a spec asks for: the ref to resolve, and a pinned commit. -/
structure Want where
  ref : String
  commit : Option String := none
  /-- a channel's release tag (`nightly`, or the resolved `stable` tag) -/
  tag : Option String := none
  deriving Repr

/-- The refs of the repository: (name, commit), tags peeled. -/
def lsRemote (git : String) : IO (Except String (List (String × String))) := do
  match ← run "git" ["ls-remote", git] with
  | .error e => pure (.error e)
  | .ok out =>
    let rows := (out.splitOn "\n").filterMap fun l =>
      match l.splitOn "\t" with
      | [c, r] => some (r, c)
      | _ => none
    -- a peeled tag (`refs/tags/v1^{}`) is the commit of an annotated tag
    let peeled := rows.filterMap fun (r, c) => if r.endsWith "^{}" then some ((r.dropEnd 3).toString, c) else none
    pure (.ok ((rows.filter fun (r, _) => !r.endsWith "^{}").map fun (r, c) =>
      (r, ((peeled.find? (·.1 == r)).map (·.2)).getD c)))

/-- A version tag `vX.Y.Z` as numbers. -/
def versionOf (tag : String) : Option (List Nat) :=
  if tag.startsWith "v" then (tag.drop 1).toString.splitOn "." |>.mapM String.toNat? else none

def versionLt : List Nat → List Nat → Bool
  | [], _ :: _ => true
  | a :: as, b :: bs => a < b || (a == b && versionLt as bs)
  | _, _ => false

def latestTag (refs : List (String × String)) : Option String :=
  let tags := refs.filterMap fun (r, _) =>
    if r.startsWith "refs/tags/" then
      let t := (r.drop 10).toString
      (versionOf t).map (t, ·)
    else none
  (tags.foldl (fun best t => match best with
    | some b => if versionLt b.2 t.2 then some t else best
    | none => some t) none).map (·.1)

/-- What a spec asks for, resolved against the repository's refs. -/
def resolveSpec (s : Settings) (spec : String) : IO (Except String Want) := do
  match spec.splitOn "@" with
  | [r, c] => return .ok { ref := r, commit := some c }
  | _ => pure ()
  let refs ← lsRemote s.git
  let find (ref : String) : Option String := match refs with
    | .ok rs => ["refs/tags/" ++ ref, "refs/heads/" ++ ref, ref].findSome? fun n => (rs.find? (·.1 == n)).map (·.2)
    | .error _ => none
  match spec with
  | "nightly" =>
    match find s.nightlyRef with
    | some c => pure (.ok { ref := s.nightlyRef, commit := some c, tag := some "nightly" })
    | none => pure (.error s!"nightly: no branch {s.nightlyRef} in {s.git}{(refs.toOption.map fun _ => "").getD " (could not list it)"}")
  | "stable" =>
    match refs with
    | .error e => pure (.error s!"stable: {e}")
    | .ok rs => match latestTag rs with
      | some t => pure (.ok { ref := t, commit := find t, tag := some t })
      | none => pure (.error s!"stable: no release tags (vX.Y.Z) in {s.git} yet; use nightly")
  | ref =>
    match find ref with
    | some c =>
      let isTag := match refs with | .ok rs => rs.any (·.1 == "refs/tags/" ++ ref) | .error _ => false
      pure (.ok { ref, commit := some c, tag := if isTag then some ref else none })
    | none =>
      if isHex ref && ref.length ≥ 7 then pure (.ok { ref, commit := some ref })
      else pure (.error s!"{ref}: no such tag or branch in {s.git}")

/-! ## Wrappers -/

/-- The flag words a wrapper passes (`--cflags '…'`). -/
def flagWords (flags : List (String × String)) : String :=
  String.join (flagKeys.filterMap fun k => (flags.find? (·.1 == k)).map fun (_, v) => s!" --{k} {shQuote v}")

/-- `bin/wiz` and `bin/grail` of a toolchain whose binaries are in `binDir` and whose
standard library is `lib`: they run the binary with the toolchain's flags (no
environment variables, as the Nix wrapper). -/
def writeWrappers (tc binDir lib : System.FilePath) (name : String) (flags : List (String × String)) : IO Unit := do
  let head := s!"#!/bin/sh\n# toolchain {name}, written by tower: the binary with this toolchain's flags\n"
  writeScript (tc / "bin" / "wiz") <|
    head ++ s!"exec {shQuote (binDir / "wiz").toString}{flagWords flags} -I {shQuote lib.toString} \"$@\"\n"
  writeScript (tc / "bin" / "grail") <|
    head ++ s!"exec {shQuote (binDir / "grail").toString}{flagWords flags} \"$@\"\n"

/-! ## Sources -/

def arch : IO String := do
  match ← run "uname" ["-m"] with
  | .ok a => pure a
  | .error _ => pure "x86_64"

/-- The flake reference of a commit. -/
def flakeRef (flake commit : String) : String :=
  if flake.startsWith "github:" || flake.startsWith "gitlab:" then s!"{flake}/{commit}"
  else if flake.contains '?' then s!"{flake}&rev={commit}" else s!"{flake}?rev={commit}"

def cachixOptions (s : Settings) : List String :=
  if s.flake == "github:badly-drawn-wizards/wiz" then
    ["--option", "extra-substituters", "https://badlydrawnwizards.cachix.org",
     "--option", "extra-trusted-public-keys",
     "badlydrawnwizards.cachix.org-1:TxG+RHY8RMC/AXc0LJbYtYm9LW/XRjfQwgz+EEaAjBI="]
  else []

def nixArgs : List String := ["--extra-experimental-features", "nix-command flakes"]

/-- `nix build` the package; the store path. -/
def nixRealise (s : Settings) (commit : String) : IO (Except String String) := do
  let ref := flakeRef s.flake commit ++ "#wiz"
  note s!"nix build {ref}"
  run "nix" (nixArgs ++ ["build", "--no-link", "--print-out-paths"] ++ cachixOptions s ++ [ref])

/-- Make `tc` a Nix toolchain on `storePath`: `nix` is a GC root, `bin` and `share` point into it. -/
def nixLink (tc : System.FilePath) (storePath : String) : IO (Except String Unit) := do
  if let .error e ← run "nix" (nixArgs ++ ["build", "--out-link", (tc / "nix").toString, storePath]) then return .error e
  for d in ["bin", "share"] do
    removeAll (tc / d)
    if let .error e ← run "ln" ["-s", s!"nix/{d}", (tc / d).toString] then return .error e
  pure (.ok ())

/-- Fetch a URL or a local file (`file://`, a path) to `dst`. -/
def fetch (url : String) (dst : System.FilePath) : IO (Except String Unit) := do
  let local? := if url.startsWith "file://" then some (url.drop 7).toString
    else if url.startsWith "/" || url.startsWith "." then some url else none
  match local? with
  | some p =>
    if ← System.FilePath.pathExists p then
      IO.FS.writeBinFile dst (← IO.FS.readBinFile p); pure (.ok ())
    else pure (.error s!"no {p}")
  | none => pure ((← run "curl" ["-fsSL", "-o", dst.toString, url]).map fun _ => ())

def tarballName (a : String) : String := s!"wiz-{a}-linux.tar.gz"

/-- Unpack the release tarball of `tag` into `work`; the toolchain directory in it. -/
def releaseFetch (s : Settings) (tag : String) (work : System.FilePath) : IO (Except String System.FilePath) := do
  let url := s!"{s.releases}/{tag}/{tarballName (← arch)}"
  note s!"downloading {url}"
  let file := work / "wiz.tar.gz"
  if let .error e ← fetch url file then return .error e
  -- a checksum next to it, when there is one
  if (← fetch (url ++ ".sha256") (work / "sum")) matches .ok _ then
    let want := ((← IO.FS.readFile (work / "sum")).splitOn " ").head!.trimAscii.toString
    let got := ((← runOrThrow "sha256sum" [file.toString]).splitOn " ").head!
    if want != got then return .error s!"{url}: sha256 {got}, expected {want}"
  let x := work / "x"
  IO.FS.createDirAll x
  if let .error e ← run "tar" ["-xzf", file.toString, "-C", x.toString] then return .error e
  let dirs ← (← x.readDir).filterM (·.path.isDir)
  let some d := dirs[0]? | return .error s!"{url}: an empty tarball"
  unless ← (d.path / "share/wiz/.lake/build/bin/wiz").pathExists do
    return .error s!"{url}: no share/wiz/.lake/build/bin/wiz in the tarball"
  pure (.ok d.path)

/-- Copy what a toolchain needs from a built checkout `src` into `tc/share/wiz`. -/
def layoutFrom (src tc : System.FilePath) (commit : String) : IO (Except String Unit) := do
  let share := tc / "share" / "wiz"
  IO.FS.createDirAll (share / ".lake/build/bin")
  for b in ["wiz", "grail"] do
    if let .error e ← run "cp" [(src / ".lake/build/bin" / b).toString, (share / ".lake/build/bin").toString] then return .error e
  if let .error e ← run "cp" ["-R", (src / "lib").toString, share.toString] then return .error e
  if ← (src / "editors").pathExists then
    if let .error e ← run "cp" ["-R", (src / "editors").toString, share.toString] then return .error e
  IO.FS.writeFile (share / "REVISION") (commit ++ "\n")
  pure (.ok ())

/-- Clone, check out and build with Lake. -/
def sourceBuild (s : Settings) (w : Want) (work tc : System.FilePath) : IO (Except String String) := do
  let src := work / "src"
  note s!"cloning {s.git}"
  if let .error e ← run "git" ["clone", "--quiet", s.git, src.toString] then return .error e
  let rev := w.commit.getD w.ref
  if let .error e ← run "git" ["-c", "advice.detachedHead=false", "checkout", "--quiet", rev] src then return .error e
  let commit ← match ← run "git" ["rev-parse", "HEAD"] src with
    | .ok c => pure c
    | .error e => return .error e
  unless ← have? "lake" do return .error "building from source needs `lake` (install elan: https://github.com/leanprover/elan)"
  note s!"lake build wiz grail (at {commit.take 12}; this takes a while the first time)"
  if let .error e ← run "lake" ["build", "wiz", "grail"] src (cleanEnv := true) then return .error e
  if let .error e ← layoutFrom src tc commit then return .error e
  removeAll src
  pure (.ok commit)

/-- Install `spec` (as `name`). `source` overrides the setting. Returns the toolchain dir. -/
def install (e : Env) (spec : String) (source : Option String := none) (force : Bool := false)
    (extraFlags : List (String × String) := []) : IO (Except String System.FilePath) := do
  let s ← e.settings
  let final := e.tcDir spec
  if (← (final / "tower.info").pathExists) && !force then return .ok final
  let w ← match ← resolveSpec s spec with
    | .ok w => pure w
    | .error m => return .error m
  let flags := (s.flags.filter fun (k, _) => !extraFlags.any (·.1 == k)) ++ extraFlags
  let src := source.getD s.source
  let candidates ← match src with
    | "auto" => do
      let n ← if ← have? "nix" then pure ["nix"] else pure []
      pure (n ++ (if w.tag.isSome then ["release"] else []) ++ ["source"])
    | x => pure [x]
  IO.FS.createDirAll e.toolchains
  let mut errs : List String := []
  for how in candidates do
    let work := e.toolchains / s!".tmp-{tcName spec}-{← IO.monoNanosNow}"
    IO.FS.createDirAll work
    let tc := work / "tc"
    let r : Except String (Info × Option String) ← match how with
      | "nix" => do
        let some commit := w.commit | pure (.error "nix: no commit")
        match ← nixRealise s commit with
        | .error m => pure (.error m)
        | .ok path =>
          IO.FS.createDirAll tc
          pure (.ok ({ spec, source := "nix", ref := w.ref, commit }, some path))
      | "release" => do
        let some tag := w.tag | pure (.error s!"release: {spec} is not a tag or a channel (only those have release tarballs)")
        match ← releaseFetch s tag work with
        | .error m => pure (.error m)
        | .ok d =>
          IO.FS.rename d tc
          let rev ← if ← (tc / "share/wiz/REVISION").pathExists then
              pure (← IO.FS.readFile (tc / "share/wiz/REVISION")).trimAscii.toString else pure (w.commit.getD "")
          pure (.ok ({ spec, source := "release", ref := w.ref, commit := rev, flags }, none))
      | "source" => do
        IO.FS.createDirAll tc
        match ← sourceBuild s w work tc with
        | .error m => pure (.error m)
        | .ok commit => pure (.ok ({ spec, source := "source", ref := w.ref, commit, flags }, none))
      | x => pure (.error s!"unknown source {x}")
    match r with
    | .error m =>
      removeAll work
      errs := errs ++ [s!"{how}: {m}"]
      if candidates.length > 1 then note s!"{how} failed; trying the next source"
    | .ok (info, nixPath) =>
      IO.FS.writeFile (tc / "tower.info") info.render
      if nixPath.isNone then
        writeWrappers tc (final / "share/wiz/.lake/build/bin") (final / "share/wiz/lib") spec info.flags
      if ← final.pathExists then removeAll final
      IO.FS.rename tc final
      removeAll work
      if let some p := nixPath then
        if let .error m ← nixLink final p then removeAll final; return .error m
      note s!"installed {spec} ({info.source}, {info.ref}{if info.commit.isEmpty then "" else "@" ++ info.commit.take 12})"
      return .ok final
  pure (.error ("\n".intercalate errs))

/-- `tower toolchain link NAME DIR`: a checkout (its `.lake/build/bin`) or an installed
toolchain layout (`bin/wiz`, e.g. a Nix `result`). -/
def link (e : Env) (name : String) (dir : System.FilePath) (flags : List (String × String)) : IO (Except String System.FilePath) := do
  let dir ← IO.FS.realPath dir
  let final := e.tcDir name
  let work := e.toolchains / s!".tmp-{tcName name}-{← IO.monoNanosNow}"
  IO.FS.createDirAll work
  if ← (dir / ".lake/build/bin/wiz").pathExists then
    writeWrappers work (dir / ".lake/build/bin") (dir / "lib") name flags
  else if ← (dir / "bin/wiz").pathExists then
    for d in ["bin", "share"] do
      if ← (dir / d).pathExists then
        if let .error m ← run "ln" ["-s", (dir / d).toString, (work / d).toString] then return .error m
  else
    removeAll work
    return .error s!"{dir}: neither a built checkout (.lake/build/bin/wiz) nor a toolchain (bin/wiz)"
  IO.FS.writeFile (work / "tower.info") ({ spec := name, source := "link", path := dir.toString, flags } : Info).render
  if ← final.pathExists then removeAll final
  IO.FS.createDirAll e.toolchains
  IO.FS.rename work final
  pure (.ok final)

end Tower
