import Wiz

open Wiz

def usage : String := "usage:
  wiz parse FILE          print the syntax tree of every command
  wiz check FILE          elaborate and type check (quantities: 0, 1, ω)
  wiz build FILE -o OUT   compile the definition `main` to an executable (via C)
  wiz run FILE            build and run `main`, printing its value
C compiler: $WIZ_CC (default cc), extra flags in $WIZ_CFLAGS and $WIZ_LDFLAGS (GMP)"

def parseCmd (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let r := parseFile input
  for cmd in r.commands do
    IO.println cmd.toSExpr
  for m in r.messages do
    IO.eprintln s!"{path}:{m.render input}"
  pure (if r.messages.isEmpty then 0 else 1)

/-- Read every `lib/*.wiz` (and `$WIZ_PATH/*.wiz`) up front: the frontend is pure. -/
def loadLibrary : IO (Std.HashMap Name String) := do
  let dirs := ["lib"] ++ ((← IO.getEnv "WIZ_PATH").map ([·])).getD []
  let mut m : Std.HashMap Name String := {}
  for d in dirs do
    if ← System.FilePath.isDir d then
      for e in ← System.FilePath.readDir d do
        if e.path.extension == some "wiz" then
          m := m.insert (e.path.fileStem.getD "") (← IO.FS.readFile e.path)
  pure m

def checkCmd (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let lib ← loadLibrary
  let s := runFrontend (R := ZeroOneMany) input { loader := (lib[·]?) }
  for m in s.messages do
    let line := s!"{path}:{m.render input}"
    if m.severity == .error then IO.eprintln line else IO.println line
  pure (if s.messages.any (·.severity == .error) then 1 else 0)

def elabFile (path : String) : IO (Option (CommandState ZeroOneMany)) := do
  let input ← IO.FS.readFile path
  let lib ← loadLibrary
  let s := runFrontend (R := ZeroOneMany) input { loader := (lib[·]?) }
  for m in s.messages do
    if m.severity == .error then IO.eprintln s!"{path}:{m.render input}"
  pure (if s.messages.any (·.severity == .error) then none else some s)

def buildCmd (path out : String) : IO UInt32 := do
  let some s ← elabFile path | pure 1
  match Build.cProgram s "main" with
  | .error e => IO.eprintln e; pure 1
  | .ok (src, _) =>
    match ← Build.compileC src out with
    | .error e => IO.eprintln e; pure 1
    | .ok () => pure 0

def runCmd (path : String) : IO UInt32 := do
  let some s ← elabFile path | pure 1
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal s "main" dir with
  | .error e => IO.eprintln e; pure 1
  | .ok v => IO.println v; pure 0

def main : List String → IO UInt32
  | ["parse", path] => parseCmd path
  | ["check", path] => checkCmd path
  | ["build", path, "-o", out] => buildCmd path out
  | ["run", path] => runCmd path
  | _ => do IO.println usage; pure 0
