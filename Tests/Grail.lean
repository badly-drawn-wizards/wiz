import Tests.Harness
import Wiz
import Grail
import Tests.Elab

/-!
Stage 23: modules by path (23b), per-module cache keys and atomic writes (23c), and
grail, the build tool (23d).
-/

namespace Tests.Grail
open Wiz Tests

/-- A fresh directory with these files in it. -/
def mkTree (files : List (String × String)) : IO System.FilePath := do
  let dir ← IO.FS.createTempDir
  for (p, text) in files do
    let f := dir / p
    if let some d := f.parent then IO.FS.createDirAll d
    IO.FS.writeFile f text
  pure dir

def loaderOf (m : Std.HashMap Name (System.FilePath × String)) : Name → Option String := fun n => (m[n]?).map (·.2)

/-- A small library: `Data.Two` (in a subdirectory) imports `Prelude`; `Use` imports it. -/
def libFiles : List (String × String) :=
  [("Data/Two.wiz", "import Prelude\ndef two : Nat := 2\n"),
   ("Use.wiz", "import Data.Two\ndef four : Nat := two + two\n"),
   ("Other.wiz", "import Prelude\ndef one : Nat := 1\n")]

def modulesGroup : Group where
  name := "modules"
  exercise := "Stage 23b–c"
  cases := [
    { name := "dotted names are paths", run := fun _ => do
        checkEq "A/B/C.wiz" (Module.relPath "A.B.C").toString
        checkEq "A.B" (Module.nameOf "A/B.wiz")
        checkEq ["Prelude", "Data.Two"] (Module.importsOf "import Prelude\n-- c\n  import Data.Two\nimport_c \"m.h\"\ndef x := 1\n")
        checkEq ["m.h"] (Module.headersOf "import_c \"m.h\" (pure)\n") },
    { name := "a file reaches modules in subdirectories", run := fun _ => do
        let dir ← mkTree libFiles
        let ms ← Module.loadClosure ["lib", dir] "import Use\n#eval four\n"
        checkEq ["Data.Two", "Prelude", "Use"] (ms.toList.map (·.1) |>.toArray.qsort (· < ·)).toList
        let s := runFrontend (R := ZeroOneMany) "import Use\n#eval four\n" { loader := loaderOf ms }
        checkEq "[2:1: info: 4]" (toString (s.messages.toList.map (·.render "import Use\n#eval four\n")))
        let all ← Module.listRoot dir
        checkEq #["Data.Two", "Other", "Use"] (all.map (·.1)) },
    { name := "a module's key changes with it and with what it imports, only", run := fun _ => do
        let dir ← mkTree libFiles
        let keys (dir : System.FilePath) : IO (Std.HashMap Name UInt64) := do
          let ms ← Module.loadAll ["lib", dir]
          pure (Cache.moduleKeys (loaderOf ms) (fun _ => none) 0 ["Use", "Other", "Data.Two"])
        let k1 ← keys dir
        IO.FS.writeFile (dir / "Data/Two.wiz") "import Prelude\ndef two : Nat := 1 + 1\n"
        let k2 ← keys dir
        check (k1["Data.Two"]? != k2["Data.Two"]?) "the edited module kept its key"
        check (k1["Use"]? != k2["Use"]?) "its importer kept its key"
        checkEq k1["Other"]? k2["Other"]?
        checkEq k1["Prelude"]? k2["Prelude"]?
        -- the toolchain enters every key
        let ms ← Module.loadAll ["lib", dir]
        check (Cache.moduleKey (loaderOf ms) (fun _ => none) 0 "Other" != Cache.moduleKey (loaderOf ms) (fun _ => none) 1 "Other")
          "the toolchain is not in the key" },
    { name := "a module is cached once, for every file that imports it", run := fun _ => do
        let dir ← mkTree libFiles
        let cache ← IO.FS.createTempDir
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany := { loader := loaderOf ms }
        let (_, h1) ← Cache.elaborateCached cache "import Data.Two\ndef a : Nat := two\n" init 0
        checkEq 0 h1
        -- another file: the modules come from the cache (Prelude's commands, and `two`)
        let (s, h2) ← Cache.elaborateCached cache "import Use\ndef b : Nat := four\n" init 0
        check s.messages.isEmpty s!"messages: {s.messages.toList.map (·.text)}"
        check (h2 > 100) s!"only {h2} commands came from the cache"
        -- no temporary files are left behind
        for e in ← cache.readDir do
          check ((e.fileName.splitOn ".tmp").length == 1) s!"left behind: {e.fileName}" },
    { name := "editing a module re-elaborates only it and what imports it", run := fun _ => do
        let dir ← mkTree libFiles
        let cache ← IO.FS.createTempDir
        let elabSrc (src : String) : IO Nat := do
          let ms ← Module.loadAll ["lib", dir]
          let (s, h) ← Cache.elaborateCached cache src ({ loader := loaderOf ms } : CommandState ZeroOneMany) 0
          check (!s.messages.any (·.severity == .error)) s!"messages: {s.messages.toList.map (·.text)}"
          pure h
        let src := "import Use\nimport Other\ndef c : Nat := four + one\n"
        let _ ← elabSrc src
        let warm ← elabSrc src
        IO.FS.writeFile (dir / "Data/Two.wiz") "import Prelude\ndef two : Nat := 1 + 1\n"
        let after ← elabSrc src
        -- Prelude and Other still come from the cache; Data.Two, Use and `c` don't
        check (after + 3 ≤ warm) s!"{after} hits after the edit, {warm} before"
        check (after + 10 ≥ warm) s!"{after} hits after the edit, {warm} before: too much was redone" },
    { name := "a module sees only what it imports (with the cache)", run := fun _ => do
        let dir ← mkTree [("Sneaky.wiz", "def three : Nat := 3\n")]
        let ms ← Module.loadAll ["lib", dir]
        let cache ← IO.FS.createTempDir
        let (s, _) ← Cache.elaborateCached cache "import Prelude\nimport Sneaky\n" ({ loader := loaderOf ms } : CommandState ZeroOneMany) 0
        check (s.messages.any fun m => (m.text.splitOn "module Sneaky has errors").length > 1)
          s!"Sneaky used Nat without importing Prelude: {s.messages.toList.map (·.text)}" },
    { name := "without the cache too", run := fun _ => do
        let dir ← mkTree [("Sneaky.wiz", "def three : Nat := 3\n")]
        let ms ← Module.loadAll ["lib", dir]
        let s ← Cache.elaborateUncached "import Prelude\nimport Sneaky\n" ({ loader := loaderOf ms } : CommandState ZeroOneMany)
        check (s.messages.any fun m => (m.text.splitOn "module Sneaky has errors").length > 1)
          s!"Sneaky used Nat without importing Prelude: {s.messages.toList.map (·.text)}"
        let ms ← Module.loadAll ["lib"]
        let s ← Cache.elaborateUncached "import Std\ndef n : Nat := 2 + 2\n" ({ loader := loaderOf ms } : CommandState ZeroOneMany)
        check s.messages.isEmpty s!"messages: {s.messages.toList.map (·.text)}" },
    { name := "an import cycle is an error, not a hang", run := fun _ => do
        let dir ← mkTree [("A.wiz", "import B\n"), ("B.wiz", "import A\n")]
        let ms ← Module.loadAll [dir]
        let cache ← IO.FS.createTempDir
        let (s, _) ← Cache.elaborateCached cache "import A\n" ({ loader := loaderOf ms } : CommandState ZeroOneMany) 0
        check (s.messages.any fun m => (m.text.splitOn "import cycle").length > 1)
          s!"messages: {s.messages.toList.map (·.text)}" }
  ]

/-- A package: a library with two modules, and a file that checks against it. -/
def pkgFiles : List (String × String) :=
  [("grail.wiz", "import Grail\ndef package : Package := Package.new \"demo\"\n  |> Package.lib \"mylib\" \"src\"\n  |> Package.check \"app\" \"app.wiz\"\n"),
   ("src/Demo/Two.wiz", "import Prelude\ndef two : Nat := 2\n"),
   ("src/Demo/Three.wiz", "import Prelude\ndef three : Nat := 3\n"),
   ("app.wiz", "import Demo.Two\n#eval two + two\n")]

/-- A runner for a package directory; its jobs run as `<this test driver> --grail-job …`,
and its report goes to `log`. -/
def runner (dir : System.FilePath) (tc : Toolchain) (pkg : Grail.Package) (jobs : Nat := 1)
    (log : IO.Ref String) : IO Grail.Runner := do
  pure { ctx := { dir, std := "lib", tc, binId := 7, libRoots := Grail.libRootsOf dir pkg.targets },
         stats := ← IO.mkRef {}, memo := ← IO.mkRef {}, jobs, self := ← IO.appPath,
         out := fun s => log.modify (· ++ s), err := fun s => log.modify (· ++ s) }

/-- Run grail's build on a package directory; also returns the report. -/
def buildLog (dir : System.FilePath) (tc : Toolchain) (only : List String := []) (jobs : Nat := 1)
    (timeoutMs : Option Nat := none) : IO (Grail.Stats × Bool × String) := do
  match ← Grail.readConfig tc 7 "lib" dir with
  | .error e => throw (IO.userError e)
  | .ok (pkg, _) =>
    let log ← IO.mkRef ""
    let r ← runner dir tc pkg jobs log
    let r := { r with timeoutMs := timeoutMs.getD r.timeoutMs }
    let ok ← r.build pkg.targets (pkg.targets.filter fun t => only.isEmpty || only.contains t.name)
    pure (← r.stats.get, ok, ← log.get)

def build (dir : System.FilePath) (tc : Toolchain) (only : List String := []) (jobs : Nat := 1) : IO (Grail.Stats × Bool) := do
  let (s, ok, _) ← buildLog dir tc only jobs
  pure (s, ok)

/-- Every `.lean` file under a directory. -/
partial def leanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← leanFiles e.path)
    else if e.path.extension == some "lean" then out := out.push e.path
  pure out

def toolchainGroup : Group where
  name := "toolchain"
  exercise := "Stage 23a"
  cases := [
    { name := "wiz, grail and the test driver read no environment variables", run := fun _ => do
        let files := (← leanFiles "Wiz") ++ (← leanFiles "Grail") ++ #[System.FilePath.mk "Main.lean", "Tests/Main.lean"]
        for f in files do
          let text ← IO.FS.readFile f
          check ((text.splitOn "getEnv \"WIZ").length == 1) s!"{f} reads a WIZ_ variable" },
    { name := "flags fill the toolchain record", run := fun _ => do
        let (tc, rest) := ({} : Toolchain).parseFlags
          ["check", "--cc", "clang", "--cflags", "-I/a  -I/b", "-I", "src", "x.wiz", "--no-cache", "--llvm"]
        checkEq ["check", "x.wiz", "--llvm"] rest
        checkEq "clang" tc.cc
        checkEq ["-I/a", "-I/b"] tc.cflags
        checkEq ["src"] (tc.searchPath.map toString)
        check tc.cacheDir.isNone "the cache is on"
        -- and back to flags, for another process
        let tc := { tc with ldflags := ["-L/x"], cacheDir := some "/c" }
        let (tc', rest) := ({} : Toolchain).parseFlags tc.toFlags
        checkEq [] rest
        checkEq (repr tc).pretty (repr tc').pretty
        check (tc.id != ({ tc with cflags := [] } : Toolchain).id) "cflags are not in the id"
        checkEq tc.id ({ tc with cacheDir := none } : Toolchain).id },
    { name := "-I DIR adds a module root", run := fun _ => do
        let dir ← mkTree [("Pkg/Three.wiz", "import Prelude\ndef three : Nat := 3\n")]
        let (tc, _) := ({} : Toolchain).parseFlags ["check", "main.wiz", "-I", dir.toString]
        let src := "import Pkg.Three\n#eval three\n"
        let ms ← Module.loadClosure ("lib" :: tc.searchPath) src
        let s := runFrontend (R := ZeroOneMany) src { loader := loaderOf ms }
        checkEq "[2:1: info: 3]" (toString (s.messages.toList.map (·.render src))) }
  ]

def grailGroup : Group where
  name := "grail"
  exercise := "Stage 23d"
  cases := [
    { name := "the build file is Wiz", run := fun _ => do
        let dir ← mkTree (pkgFiles ++ [("grail.local.wiz", "import Grail\ndef settings : Settings := Settings.empty |> Settings.set \"cflags\" \"-I \\\"x\\\"\"\n")])
        let cache ← IO.FS.createTempDir
        match ← Grail.readConfig { cacheDir := some cache } 7 "lib" dir with
        | .error e => throw (IO.userError e)
        | .ok (pkg, localSettings) =>
          checkEq "demo" pkg.name
          check (pkg.targets == [Grail.Target.lib "mylib" "src", .check "app" "app.wiz"]) s!"targets: {repr pkg.targets}"
          checkEq [("cflags", "-I \"x\"")] localSettings },
    { name := "a second build runs no jobs", run := fun _ => do
        let dir ← mkTree pkgFiles
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (s1, ok1) ← build dir tc
        check ok1 "the first build failed"
        checkEq 3 s1.ran
        let (s2, ok2) ← build dir tc
        check ok2 "the second build failed"
        checkEq 0 s2.ran
        checkEq 3 s2.upToDate },
    { name := "an edit reruns the checks that depend on it", run := fun _ => do
        let dir ← mkTree pkgFiles
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let _ ← build dir tc
        IO.FS.writeFile (dir / "src/Demo/Two.wiz") "import Prelude\ndef two : Nat := 1 + 1\n"
        let (s, ok) ← build dir tc
        check ok "the build failed"
        -- Demo.Two and app.wiz; not Demo.Three
        checkEq 2 s.ran
        checkEq 1 s.upToDate },
    { name := "a failed check is reported and not recorded", run := fun _ => do
        let dir ← mkTree (pkgFiles.map fun (p, t) => if p == "app.wiz" then (p, "import Demo.Two\ndef bad : Nat := true\n") else (p, t))
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (s, ok) ← build dir tc ["app"]
        check (!ok) "the build succeeded"
        checkEq 1 s.failed
        let (s, _) ← build dir tc ["app"]
        checkEq 1 s.failed
        -- nothing half-written is left
        let tmp := dir / ".grail" / "tmp"
        if ← tmp.pathExists then checkEq 0 (← tmp.readDir).size },
    { name := "an executable: check, IR, C, object, link", run := fun _ => do
        let tc : Toolchain := { (← toolchain) with cacheDir := some (← IO.FS.createTempDir) }
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"p\" |> Package.exe \"hello\" \"hello.wiz\"\n"),
                          ("hello.wiz", "import IO\ndef main : IO Unit := IO.println \"hello from grail\"\n")]
        let (s, ok) ← build dir tc
        if !ok then
          IO.println "    (skipped: no toolchain)"
          return
        checkEq 5 s.ran
        let out ← IO.Process.output { cmd := (dir / ".grail" / "bin" / "hello").toString }
        checkEq "hello from grail\n" out.stdout
        let (s, _) ← build dir tc
        checkEq 0 s.ran
        -- a change that doesn't change the program's code: only check, IR and C rerun
        IO.FS.writeFile (dir / "hello.wiz") "import IO\n-- a comment\ndef main : IO Unit := IO.println \"hello from grail\"\n"
        let (s, _) ← build dir tc
        checkEq 3 s.ran
        checkEq 2 s.upToDate }
  ]

/-- A diamond: `B` and `C` import `A`, `D` imports both, and `app.wiz` imports `D`. -/
def diamondFiles : List (String × String) :=
  [("grail.wiz", "import Grail\ndef package : Package := Package.new \"diamond\"\n  |> Package.lib \"lib\" \"src\"\n  |> Package.check \"app\" \"app.wiz\"\n"),
   ("src/A.wiz", "import Prelude\ndef a : Nat := 1\n"),
   ("src/B.wiz", "import A\ndef b : Nat := a + 1\n"),
   ("src/C.wiz", "import A\ndef c : Nat := a + 2\n"),
   ("src/D.wiz", "import B\nimport C\ndef d : Nat := b + c\n"),
   ("app.wiz", "import D\n#eval d\n")]

/-- The names in a package's `.grail/build`, sorted. -/
def buildDirs (dir : System.FilePath) : IO (List String) := do
  let entries ← (dir / ".grail" / "build").readDir
  pure (entries.map (·.fileName)).toList.mergeSort

def grailJobsGroup : Group where
  name := "grail-jobs"
  exercise := "Stage 23g"
  cases := [
    { name := "a diamond builds with -j 4 as with -j 1, and again runs nothing", run := fun _ => do
        let cache ← IO.FS.createTempDir
        let tc : Toolchain := { cacheDir := some cache }
        let d1 ← mkTree diamondFiles
        let (s1, ok1, log1) ← buildLog d1 tc (jobs := 1)
        check ok1 s!"-j 1 failed:\n{log1}"
        let d4 ← mkTree diamondFiles
        let (s4, ok4, log4) ← buildLog d4 tc (jobs := 4)
        check ok4 s!"-j 4 failed:\n{log4}"
        checkEq 5 s1.ran
        checkEq 5 s4.ran
        -- the same report, in the graph's order, and the same outputs
        checkEq log1 log4
        checkEq "[check src/A.wiz]\n[check src/B.wiz]\n[check src/C.wiz]\n[check src/D.wiz]\n[check app.wiz]\napp.wiz:2:1: info: 5\n" log4
        checkEq (← buildDirs d1) (← buildDirs d4)
        let (s, ok, _) ← buildLog d4 tc (jobs := 4)
        check ok "the second build failed"
        checkEq 0 s.ran
        checkEq 5 s.upToDate },
    { name := "a failed job stops what depends on it, only", run := fun _ => do
        let dir ← mkTree (diamondFiles.map fun (p, t) => if p == "src/B.wiz" then (p, "import A\ndef b : Nat := Nat.zero Nat.zero\n") else (p, t))
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (s, ok, log) ← buildLog dir tc (jobs := 4)
        check (!ok) "the build succeeded"
        -- A and C ran; B failed; D and app were skipped
        checkEq 2 s.ran
        checkEq 1 s.failed
        checkEq 2 s.skipped
        check ((log.splitOn "✗ check src/B.wiz\n  src/B.wiz:2:").length == 2) log
        check ((log.splitOn "- check src/D.wiz: skipped (check src/B.wiz failed)").length == 2) log
        check ((log.splitOn "- check app.wiz: skipped (check src/B.wiz failed)").length == 2) log
        -- nothing half-written is left
        let tmp := dir / ".grail" / "tmp"
        if ← tmp.pathExists then checkEq 0 (← tmp.readDir).size },
    { name := "a job has a time limit", run := fun _ => do
        let dir ← mkTree diamondFiles
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (s, ok, log) ← buildLog dir tc (jobs := 2) (timeoutMs := some 1)
        check (!ok) "the build succeeded"
        checkEq 0 s.ran
        check ((log.splitOn "timed out after 0.001 s").length > 1) log }
  ]

/-- Run `grail test` in-process on a package directory. -/
def runTests (dir : System.FilePath) (tc : Toolchain) (update : Bool := false) : IO (Array Grail.TestResult × Grail.Stats) := do
  let std : System.FilePath := "lib"
  match ← Grail.readConfig tc 7 std dir with
  | .error e => throw (IO.userError e)
  | .ok (pkg, _) =>
    let r ← runner dir tc pkg 2 (← IO.mkRef "")
    let res ← r.tests pkg.targets [] update
    pure (res, ← r.stats.get)

def testPkg : List (String × String) :=
  [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
   ("tests/two.wiz", "import Prelude\n#eval 1 + 1\n"),
   ("tests/sub/bad.wiz", "import Prelude\ndef b : Nat := true\n")]

def testRunnerGroup : Group where
  name := "testrunner"
  exercise := "Stage 23f"
  cases := [
    { name := "tests are files with expected output; --update writes it", run := fun _ => do
        let dir ← mkTree testPkg
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (res, _) ← runTests dir tc
        checkEq 2 res.size
        check (res.all (!·.ok)) "a test without .expected passed"
        let (res, _) ← runTests dir tc (update := true)
        check (res.all (·.ok)) "--update failed"
        checkEq "tests/two.wiz:2:1: info: 2\n" (← IO.FS.readFile (dir / "tests/two.expected"))
        let bad ← IO.FS.readFile (dir / "tests/sub/bad.expected")
        check ((bad.splitOn "tests/sub/bad.wiz:2:").length > 1 && (bad.splitOn "error").length > 1) s!"bad.expected: {bad}"
        let (res, _) ← runTests dir tc
        check (res.all (·.ok)) "the tests failed after --update"
        -- passes are recorded: nothing runs again
        let (res, st) ← runTests dir tc
        check (res.all (·.cached)) "a pass was not recorded"
        checkEq 0 st.ran },
    { name := "a wrong output fails, with the first difference", run := fun _ => do
        let dir ← mkTree (testPkg ++ [("tests/two.expected", "tests/two.wiz:2:1: info: 3\n")])
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (res, _) ← runTests dir tc
        let some two := res.find? (·.file == "tests/two.wiz") | throw (IO.userError "no test two")
        check (!two.ok) "a wrong output passed"
        check ((two.message.splitOn "info: 3").length > 1 && (two.message.splitOn "info: 2").length > 1) two.message },
    { name := "-- test: run compiles and runs main", run := fun _ => do
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/hello.wiz", "-- test: run\nimport IO\ndef main : IO Unit := IO.println \"hi\"\n"),
          ("tests/hello.expected", "hi\n"),
          ("tests/value.wiz", "-- test: run\nimport Prelude\ndef main : Nat := 6 * 7\n"),
          ("tests/value.expected", "42\n")]
        let tc : Toolchain := { (← toolchain) with cacheDir := some (← IO.FS.createTempDir) }
        let (res, _) ← runTests dir tc
        if res.any fun t => (t.message.splitOn "gmp.h").length > 1 then
          IO.println "    (skipped: no toolchain)"; return
        for t in res do check t.ok s!"{t.file}: {t.message}" }
  ]

def grailSelfhostGroup : Group where
  name := "grail-selfhost"
  exercise := "Stage 23e"
  cases := [
    { name := "grail builds the self-hosted checker, the same program as the tests'", run := fun _ => do
        -- the suite's elaboration cache (`lake test -- --cache DIR`, as CI does), else a fresh one
        let tc ← toolchain
        let tc : Toolchain := { tc with cacheDir := some (← tc.cacheDir.getDM IO.FS.createTempDir) }
        let dir ← IO.FS.realPath "."
        let log ← IO.mkRef ""
        let target := Grail.Target.selfhost "selfhost-checker" "checker"
        let r ← runner dir tc { name := "wiz", targets := [target], settings := [] } 4 log
        if !(← r.build [target] [target]) then
          if ((← log.get).splitOn "gmp.h").length > 1 then IO.println "    (skipped: no toolchain)"; return
          throw (IO.userError (← log.get))
        let mine := dir / ".grail" / "bin" / "selfhost-checker"
        let .ok theirs ← Tests.Elab.selfhostChecker | throw (IO.userError "the tests' checker failed")
        let work ← IO.FS.createTempDir
        IO.FS.writeFile (work / "input.wiz") "import Prelude\ndef two : Nat := 1 + 1\n#check two\n"
        let a ← IO.Process.output { cmd := mine.toString, cwd := work }
        let b ← IO.Process.output { cmd := theirs.toString, cwd := work }
        checkEq b.stdout a.stdout
        check (!a.stdout.isEmpty) "no output"
        -- again: nothing runs
        let r : Grail.Runner := { r with stats := ← IO.mkRef ({} : Grail.Stats), memo := ← IO.mkRef ({} : Grail.Memo) }
        check (← r.build [target] [target]) "the second build failed"
        checkEq 0 (← r.stats.get).ran }
  ]

end Tests.Grail
