import Tests.Harness
import Tower

/-!
Stage 26: tower, the toolchain manager. No network: the "upstream" is a local bare git
repository (a tiny Lake project whose `wiz` and `grail` print their arguments), a release
directory made by `scripts/release-tarball.sh`, and a local flake whose package is a
plain directory (no nixpkgs).
-/

namespace Tests.Tower
open Tests

def mkTree (files : List (String × String)) : IO System.FilePath := do
  let dir ← IO.FS.createTempDir
  for (p, text) in files do
    let f := dir / p
    if let some d := f.parent then IO.FS.createDirAll d
    IO.FS.writeFile f text
  pure dir

def gitIn (dir : System.FilePath) (args : List String) : IO String := do
  let o ← IO.Process.output {
    cmd := "git", cwd := dir,
    args := #["-c", "user.name=tower", "-c", "user.email=tower@example.com", "-c", "init.defaultBranch=main",
              "-c", "commit.gpgsign=false", "-c", "tag.gpgsign=false"] ++ args.toArray }
  if o.exitCode != 0 then throw (IO.userError s!"git {args}: {o.stderr}")
  pure o.stdout.trimAscii.toString

def fakeMain (tool version : String) : String :=
  s!"def main (args : List String) : IO Unit := IO.println s!\"{tool} {version} \{args}\"\n"

/-- An upstream: a Lake project with `wiz` and `grail` executables, tagged `v1` (version
1) and with `main` at version 2. (bare repository, work tree) -/
def upstream : IO (System.FilePath × System.FilePath) := do
  let work ← mkTree [
    ("lakefile.toml", "name = \"fakewiz\"\n\n[[lean_exe]]\nname = \"wiz\"\nroot = \"FakeWiz\"\n\n[[lean_exe]]\nname = \"grail\"\nroot = \"FakeGrail\"\n"),
    ("lean-toolchain", ← IO.FS.readFile "lean-toolchain"),
    ("FakeWiz.lean", fakeMain "wiz" "1"), ("FakeGrail.lean", fakeMain "grail" "1"),
    ("lib/Prelude.wiz", "-- fake prelude\n")]
  let bare ← IO.FS.createTempDir
  let _ ← gitIn bare ["init", "--quiet", "--bare"]
  let _ ← gitIn work ["init", "--quiet"]
  let _ ← gitIn work ["add", "."]
  let _ ← gitIn work ["commit", "--quiet", "-m", "v1"]
  let _ ← gitIn work ["tag", "v1"]
  IO.FS.writeFile (work / "FakeWiz.lean") (fakeMain "wiz" "2")
  let _ ← gitIn work ["commit", "--quiet", "-am", "v2"]
  let _ ← gitIn work ["push", "--quiet", bare.toString, "HEAD:refs/heads/main", "v1"]
  pure (bare, work)

/-- A tower home whose shims call this test driver (`--tower`). -/
def mkEnv : IO Tower.Env := do
  let home ← IO.FS.createTempDir
  pure { home, self := [(← IO.appPath).toString, "--tower"] }

def tower (e : Tower.Env) (args : List String) : IO Unit := do
  let r ← Tower.main e args
  unless r == 0 do throw (IO.userError s!"tower {args}: exit {r}")

/-- Run a program; its trimmed stdout (it must succeed). -/
def runOut (cmd : String) (args : List String) (cwd : Option System.FilePath := none) : IO String := do
  let o ← IO.Process.output { cmd, args := args.toArray, cwd }
  if o.exitCode != 0 then throw (IO.userError s!"{cmd} {args}: exit {o.exitCode}\n{o.stderr}{o.stdout}")
  pure o.stdout.trimAscii.toString

def contains (s t : String) : Bool := (s.splitOn t).length > 1

def checkHas (out t : String) : IO Unit := check (contains out t) s!"expected {t} in: {out}"

def readFile? (f : System.FilePath) : IO String := do
  if ← f.pathExists then IO.FS.readFile f else pure ""

def group : Group where
  name := "tower"
  exercise := "Stage 26"
  cases := [
    { name := "settings, wiz-toolchain files, overrides and the default", run := fun _ => do
        let e ← mkEnv
        let s := ((({} : Tower.Settings).set "cflags" "-I/x y").toOption.get!.set "override" "v1 /a b").toOption.get!
        checkEq s.render ((Tower.Settings.parse s.render).toOption.get!).render
        checkEq [("/a b", "v1")] s.overrides
        let proj ← IO.FS.realPath (← mkTree [("wiz-toolchain", "-- the toolchain\nv1\n"), ("sub/deep/x.wiz", ""), ("other/y", "")])
        checkEq none (← Tower.active e proj)
        tower e ["set", "default", "nightly"]
        checkEq (some ("v1", (proj / "wiz-toolchain").toString)) (← Tower.active e (proj / "sub/deep"))
        tower e ["override", "set", "branch-x", (proj / "sub").toString]
        checkEq (some "branch-x") ((← Tower.active e (proj / "sub/deep")).map (·.1))
        checkEq (some "v1") ((← Tower.active e (proj / "other")).map (·.1))
        tower e ["override", "unset", (proj / "sub").toString]
        checkEq (some "v1") ((← Tower.active e (proj / "sub/deep")).map (·.1))
        let tmp ← IO.FS.createTempDir
        checkEq (some ("nightly", "the default toolchain")) (← Tower.active e tmp)
        -- specs: versions order numerically
        checkEq (some "v1.10.0") (Tower.latestTag [("refs/tags/v1.9.2", ""), ("refs/tags/v1.10.0", ""), ("refs/tags/x", ""), ("refs/heads/v9", "")])
        checkEq "github:o/r/abc" (Tower.flakeRef "github:o/r" "abc")
        checkEq "git+file:///r?rev=abc" (Tower.flakeRef "git+file:///r" "abc") },
    { name := "from source: install, channels, update, shims, +SPEC, run", run := fun _ => do
        let (bare, work) ← upstream
        let e ← mkEnv
        tower e ["set", "git", bare.toString]
        tower e ["set", "nightly-ref", "main"]
        tower e ["set", "source", "source"]
        tower e ["set", "cflags", "-I/opt/gmp/include"]
        tower e ["toolchain", "install", "v1"]
        let tc := e.tcDir "v1"
        let out ← runOut (tc / "bin/wiz").toString ["check", "a.wiz"]
        checkHas out "wiz 1"
        checkHas out "--cflags, -I/opt/gmp/include"
        checkHas out s!"-I, {tc / "share/wiz/lib"}, check, a.wiz"
        check (← (tc / "share/wiz/lib/Prelude.wiz").pathExists) "no lib"
        checkHas (← runOut (tc / "bin/grail").toString ["build"]) "grail 1"
        -- shims: the project says v1; a directory without one gets the default
        tower e ["self", "shims"]
        let proj ← IO.FS.realPath (← mkTree [("wiz-toolchain", "v1\n"), ("sub/x", "")])
        let shim := (e.binDir / "wiz").toString
        checkHas (← runOut shim ["check"] proj) "wiz 1"
        -- +SPEC, and installing on first use (nightly = main = version 2)
        checkHas (← runOut shim ["+nightly", "check"] (proj / "sub")) "wiz 2"
        let nightly ← readFile? (e.tcDir "nightly" / "tower.info")
        checkHas nightly s!"commit {← gitIn work ["rev-parse", "HEAD"]}"
        -- an override beats the file
        tower e ["override", "set", "nightly", (proj / "sub").toString]
        checkHas (← runOut shim ["check"] (proj / "sub")) "wiz 2"
        checkHas (← runOut shim ["check"] proj) "wiz 1"
        -- run puts the toolchain's bin/ first on PATH
        let sh ← IO.FS.realPath (← mkTree [("t.sh", "wiz from-run\n")])
        let self := (← IO.appPath).toString
        let o ← IO.Process.output {
          cmd := self, args := #["--tower", "--home", e.home.toString, "run", "v1", "--", "sh", (sh / "t.sh").toString] }
        checkHas o.stdout "wiz 1 [--cflags"
        checkHas o.stdout "from-run]"
        -- nightly moves: update reinstalls it, v1 (a tag) stays
        IO.FS.writeFile (work / "FakeWiz.lean") (fakeMain "wiz" "3")
        let _ ← gitIn work ["commit", "--quiet", "-am", "v3"]
        let _ ← gitIn work ["push", "--quiet", bare.toString, "HEAD:refs/heads/main"]
        tower e ["update"]
        checkHas (← runOut shim ["check"] (proj / "sub")) "wiz 3"
        checkHas (← runOut shim ["check"] proj) "wiz 1"
        -- uninstall; without auto-install the shim says how to install it
        tower e ["toolchain", "uninstall", "v1"]
        tower e ["set", "auto-install", "false"]
        let o ← IO.Process.output { cmd := shim, args := #["check"], cwd := proj }
        check (o.exitCode != 0) "ran an uninstalled toolchain"
        checkHas o.stderr "tower toolchain install v1" },
    { name := "from a release tarball (scripts/release-tarball.sh), and linked toolchains", run := fun _ => do
        let (bare, _) ← upstream
        let fake ← mkTree [("wiz", "#!/bin/sh\necho release wiz \"$@\"\n"), ("grail", "#!/bin/sh\necho release grail \"$@\"\n"),
                           ("tower", "#!/bin/sh\necho tower\n")]
        for b in ["wiz", "grail", "tower"] do Tower.makeExecutable (fake / b)
        let rel ← IO.FS.createTempDir
        IO.FS.createDirAll (rel / "v1")
        let a ← Tower.arch
        let _ ← runOut "sh" ["scripts/release-tarball.sh", (rel / "v1" / Tower.tarballName a).toString, fake.toString, "abc123"]
        -- the tarball works on its own
        let x ← IO.FS.createTempDir
        let _ ← runOut "tar" ["-xzf", (rel / "v1" / Tower.tarballName a).toString, "-C", x.toString]
        checkHas (← runOut (x / s!"wiz-{a}-linux/bin/wiz").toString ["check"]) s!"wiz-{a}-linux/share/wiz/lib check"
        let e ← mkEnv
        tower e ["set", "git", bare.toString]
        tower e ["set", "releases", rel.toString]
        tower e ["toolchain", "install", "v1", "--source", "release", "--cc", "gcc"]
        let tc := e.tcDir "v1"
        checkHas (← runOut (tc / "bin/wiz").toString ["check"]) s!"release wiz --cc gcc -I {tc / "share/wiz/lib"} check"
        checkHas (← readFile? (tc / "tower.info")) "commit abc123"
        -- a corrupt download is refused
        IO.FS.writeFile (rel / "v1" / (Tower.tarballName a ++ ".sha256")) "0000  x\n"
        match ← Tower.install e "v1" (some "release") (force := true) with
        | .error m => checkHas m "sha256"
        | .ok _ => throw (IO.userError "installed a tarball with the wrong checksum")
        -- a branch has no release
        match ← Tower.install e "main" (some "release") with
        | .error m => checkHas m "not a tag"
        | .ok _ => throw (IO.userError "installed a release of a branch")
        -- link the unpacked tarball (a toolchain layout) and use it by name
        tower e ["toolchain", "link", "mine", (x / s!"wiz-{a}-linux").toString]
        tower e ["self", "shims"]
        checkHas (← runOut (e.binDir / "wiz").toString ["+mine", "x"]) "release wiz -I"
        tower e ["default", "mine"]
        checkHas (← runOut (e.binDir / "grail").toString ["y"] (← IO.FS.createTempDir)) "release grail y" },
    { name := "from Nix: a flake's package, linked as a GC root", run := fun _ => do
        unless ← Tower.have? "nix" do IO.println "    (no nix: skipped)"; return
        let (bare, _) ← upstream
        let flake ← mkTree [
          ("flake.nix", "{ outputs = { self }: let p = builtins.path { path = ./tc; name = \"fake-wiz\"; }; in\n" ++
                        "  { packages.x86_64-linux.wiz = p; packages.aarch64-linux.wiz = p; }; }\n"),
          ("tc/bin/wiz", "#!/bin/sh\necho nix wiz \"$@\"\n"), ("tc/share/wiz/lib/Prelude.wiz", "")]
        Tower.makeExecutable (flake / "tc/bin/wiz")
        let _ ← gitIn flake ["init", "--quiet"]
        let _ ← gitIn flake ["add", "."]
        let _ ← gitIn flake ["commit", "--quiet", "-m", "flake"]
        let e ← mkEnv
        tower e ["set", "git", bare.toString]
        tower e ["set", "flake", s!"git+file://{flake}"]
        -- the flake's own commit stands in for the wiz commit
        let c ← gitIn flake ["rev-parse", "HEAD"]
        tower e ["toolchain", "install", s!"main@{c}", "--source", "nix"]
        let tc := e.tcDir s!"main@{c}"
        checkHas (← runOut (tc / "bin/wiz").toString ["check"]) "nix wiz check"
        let target ← runOut "readlink" [(tc / "nix").toString]
        check (target.startsWith "/nix/store/") s!"nix -> {target}"
        let roots ← runOut "nix-store" ["--query", "--roots", target]
        checkHas roots (tc / "nix").toString
        tower e ["toolchain", "uninstall", s!"main@{c}"]
        check (← System.FilePath.pathExists target) "uninstall removed the store path" }
  ]

end Tests.Tower
