import Tests.Harness
import Wiz
import Grail

/-!
Stage 22: modules by path (22b), per-module cache keys and atomic writes (22c), and
grail, the build tool (22d).
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
  exercise := "Stage 22b–c"
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
        checkEq "[1:1: info: 4]" (toString (s.messages.toList.map (·.render "import Use\n#eval four\n")))
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
        let elab (src : String) : IO Nat := do
          let ms ← Module.loadAll ["lib", dir]
          let (s, h) ← Cache.elaborateCached cache src { loader := loaderOf ms } 0
          check (!s.messages.any (·.severity == .error)) s!"messages: {s.messages.toList.map (·.text)}"
          pure h
        let src := "import Use\nimport Other\ndef c : Nat := four + one\n"
        let _ ← elab src
        let warm ← elab src
        IO.FS.writeFile (dir / "Data/Two.wiz") "import Prelude\ndef two : Nat := 1 + 1\n"
        let after ← elab src
        -- Prelude and Other still come from the cache; Data.Two, Use and `c` don't
        check (after + 3 ≤ warm) s!"{after} hits after the edit, {warm} before"
        check (after + 10 ≥ warm) s!"{after} hits after the edit, {warm} before: too much was redone" },
    { name := "a module sees only what it imports (with the cache)", run := fun _ => do
        let dir ← mkTree [("Sneaky.wiz", "def three : Nat := 3\n")]
        let ms ← Module.loadAll ["lib", dir]
        let cache ← IO.FS.createTempDir
        let (s, _) ← Cache.elaborateCached cache "import Prelude\nimport Sneaky\n" { loader := loaderOf ms } 0
        check (s.messages.any fun m => (m.text.splitOn "module Sneaky has errors").length > 1)
          s!"Sneaky used Nat without importing Prelude: {s.messages.toList.map (·.text)}" },
    { name := "an import cycle is an error, not a hang", run := fun _ => do
        let dir ← mkTree [("A.wiz", "import B\n"), ("B.wiz", "import A\n")]
        let ms ← Module.loadAll [dir]
        let cache ← IO.FS.createTempDir
        let (s, _) ← Cache.elaborateCached cache "import A\n" { loader := loaderOf ms } 0
        check (s.messages.any fun m => (m.text.splitOn "import cycle").length > 1)
          s!"messages: {s.messages.toList.map (·.text)}" }
  ]

/-- A package: a library with two modules, and a file that checks against it. -/
def pkgFiles : List (String × String) :=
  [("grail.wiz", "import Grail\ndef package : Package := Package.new \"demo\"\n  |> Package.lib \"mylib\" \"src\"\n  |> Package.check \"app\" \"app.wiz\"\n"),
   ("src/Demo/Two.wiz", "import Prelude\ndef two : Nat := 2\n"),
   ("src/Demo/Three.wiz", "import Prelude\ndef three : Nat := 3\n"),
   ("app.wiz", "import Demo.Two\n#eval two + two\n")]

/-- Run grail's build in-process on a package directory. -/
def build (dir : System.FilePath) (tc : Toolchain) (only : List String := []) : IO (Grail.Stats × Bool) := do
  let std : System.FilePath := "lib"
  match ← Grail.readConfig tc 7 std dir with
  | .error e => throw (IO.userError e)
  | .ok (pkg, _) =>
    let r : Grail.Runner := { ctx := { dir, std, tc, binId := 7, libRoots := Grail.libRootsOf dir pkg.targets }, stats := ← IO.mkRef {}, memo := ← IO.mkRef {},
                              log := fun _ => pure () }
    let mut ok := true
    for t in pkg.targets do
      if only.isEmpty || only.contains t.name then ok := (← r.target t) && ok
    pure (← r.stats.get, ok)

def grailGroup : Group where
  name := "grail"
  exercise := "Stage 22d"
  cases := [
    { name := "the build file is Wiz", run := fun _ => do
        let dir ← mkTree (pkgFiles ++ [("grail.local.wiz", "import Grail\ndef settings : Settings := Settings.empty |> Settings.set \"cflags\" \"-I \\\"x\\\"\"\n")])
        let cache ← IO.FS.createTempDir
        match ← Grail.readConfig { cacheDir := some cache } 7 "lib" dir with
        | .error e => throw (IO.userError e)
        | .ok (pkg, local) =>
          checkEq "demo" pkg.name
          checkEq [Grail.Target.lib "mylib" "src", .check "app" "app.wiz"] pkg.targets
          checkEq [("cflags", "-I \"x\"")] local },
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
        -- the C toolchain comes from the environment here until stage 22a
        let words (v : Option String) := Toolchain.words (v.getD "")
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir), cflags := words (← IO.getEnv "WIZ_CFLAGS"),
                                ldflags := words (← IO.getEnv "WIZ_LDFLAGS"), cc := (← IO.getEnv "WIZ_CC").getD "cc" }
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

end Tests.Grail
