import Grail.Elab

/-!
# Build files

`grail.wiz` is a Wiz file that imports `Grail` (`lib/Grail.wiz`) and defines
`package : Package`; the uncommitted `grail.local.wiz` may define `settings : Settings`
(this machine's compiler flags). grail elaborates the file, evaluates
`Package.render package` (an S-expression) in the interpreter, and reads it back.
-/

namespace Grail
open Wiz

inductive Target where
  | lib (name : String) (root : String)
  | check (name : String) (file : String)
  | exe (name : String) (file : String)
  /-- every `.wiz` file under a directory is a test, its expected output beside it -/
  | tests (name : String) (root : String)
  /-- the self-hosted toolchain: `checker`, `compiler`, or the `bootstrap` check -/
  | selfhost (name : String) (role : String)
  deriving Repr, Inhabited, BEq

def Target.name : Target → String
  | .lib n _ | .check n _ | .exe n _ | .tests n _ | .selfhost n _ => n

/-- Built by `grail build` without naming it? Not the bootstrap check (it takes minutes). -/
def Target.isDefault : Target → Bool
  | .selfhost _ "bootstrap" => false
  | _ => true

structure Package where
  name : String
  targets : List Target
  settings : List (String × String)
  deriving Repr, Inhabited

open Cache in
def decodeSettings (x : Sx) : Except String (List (String × String)) := do
  let some xs := items? x | throw "settings: expected a list"
  xs.toList.drop 1 |>.mapM fun
    | .l #[.a "set", .a k, .a v] => pure (k, v)
    | _ => throw "settings: expected (set key value)"

open Cache in
def decodePackage (x : Sx) : Except String Package := do
  let .l #[.a "package", .a name, ts, ss] := x | throw "expected (package name targets settings)"
  let some ts := items? ts | throw "targets: expected a list"
  let targets ← ts.toList.drop 1 |>.mapM fun
    | .l #[.a "lib", .a n, .a r] => pure (Target.lib n r)
    | .l #[.a "check", .a n, .a f] => pure (.check n f)
    | .l #[.a "exe", .a n, .a f] => pure (.exe n f)
    | .l #[.a "tests", .a n, .a r] => pure (.tests n r)
    | .l #[.a "selfhost", .a n, .a r] => pure (.selfhost n r)
    | t => throw s!"unknown target {t.render}"
  pure { name, targets, settings := ← decodeSettings ss }

/-- Evaluate `expr` (a `String`) in the build file `path`. -/
def evalBuildFile (tc : Toolchain) (salt : UInt64) (roots : List System.FilePath) (path : System.FilePath)
    (expr : String) : IO (Except String Cache.Sx) := do
  let src := (← IO.FS.readFile path) ++ s!"\ndef grailOut : String := {expr}\n"
  let l ← load tc roots salt src
  let s ← elaborate tc salt l
  if hasErrors s then return .error (render path.toString l s)
  match evalString s "grailOut" with
  | .error e => pure (.error s!"{path}: {e}")
  | .ok str => match Cache.Sx.parse str with
    | some x => pure (.ok x)
    | none => pure (.error s!"{path}: could not read {str}")

/-- Read `grail.wiz` (and `grail.local.wiz`, if there is one) in `dir`. -/
def readConfig (tc : Toolchain) (salt : UInt64) (std dir : System.FilePath) :
    IO (Except String (Package × List (String × String))) := do
  let roots := [std, dir]
  let file := dir / "grail.wiz"
  unless ← file.pathExists do return .error s!"no {file}"
  let pkg ← match ← evalBuildFile tc salt roots file "Package.render package" with
    | .error e => return .error e
    | .ok x => match decodePackage x with
      | .error e => return .error s!"{file}: {e}"
      | .ok p => pure p
  let localFile := dir / "grail.local.wiz"
  if !(← localFile.pathExists) then return .ok (pkg, [])
  match ← evalBuildFile tc salt roots localFile "Settings.render settings" with
  | .error e => pure (.error e)
  | .ok x => match decodeSettings x with
    | .error e => pure (.error s!"{localFile}: {e}")
    | .ok ss => pure (.ok (pkg, ss))

end Grail
