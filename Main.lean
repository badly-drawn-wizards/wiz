import Wiz

open Wiz

def usage : String := "usage:
  wiz parse FILE          print the syntax tree of every command
  wiz check FILE          elaborate and type check (quantities: 0, 1, ω)
  wiz build FILE -o OUT [--llvm]   compile the definition `main` to an executable (via C or LLVM)
  wiz run FILE [--llvm]            build and run `main`, printing its value
  wiz lsp                          a language server on stdin/stdout
options: --cache DIR (the elaboration cache, default ~/.cache/wiz; shared, since it is
content-addressed), --no-cache
C compiler: $WIZ_CC (default cc), extra flags in $WIZ_CFLAGS and $WIZ_LDFLAGS (GMP); llc: $WIZ_LLC"

def parseCmd (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let r := parseFile input
  for cmd in r.commands do
    IO.println cmd.toSExpr
  for m in r.messages do
    IO.eprintln s!"{path}:{m.render input}"
  pure (if r.messages.isEmpty then 0 else 1)

/-- The module roots: `lib/` (the standard library), then `$WIZ_PATH`. -/
def moduleRoots : IO (List System.FilePath) := do
  pure (([System.FilePath.mk "lib"] : List System.FilePath) ++ ((← IO.getEnv "WIZ_PATH").map ([System.FilePath.mk ·])).getD [])

/-- Read every module the file can reach (`import A.B` is `A/B.wiz` under a root) up
front: the frontend is pure. -/
def loadLibrary (input : String) : IO (Std.HashMap Name String) := do
  pure ((← Module.loadClosure (← moduleRoots) input).fold (fun m n (_, src) => m.insert n src) {})

/-- Library modules with their paths (for the language server's go-to-definition). -/
def loadLibraryPaths : IO (Std.HashMap String (String × String)) := do
  let mut m : Std.HashMap String (String × String) := {}
  for (n, p, src) in (← Module.loadAll (← moduleRoots)).toList do
    m := m.insert n ((← IO.FS.realPath p).toString, src)
  pure m

/-- Elaborate a file, through the cache in `cache` (none: no cache). -/
def elaborate (cache : Option String) (input : String) : IO (CommandState ZeroOneMany) := do
  let lib ← loadLibrary input
  -- the C headers of the file and of the modules it imports
  let headers ← Build.preprocessHeaders (String.join (input :: lib.values))
  let init : CommandState ZeroOneMany := { loader := (lib[·]?), cHeaders := (headers[·]?) }
  match cache with
  | none => pure (runFrontend input init)
  | some dir =>
    -- the key starts from the headers the file sees; modules enter it by their own keys
    let key₀ := hash (toString (headers.toList.map (·.2)))
    pure (← Cache.elaborateCached dir input init key₀).1

def checkCmd (cache : Option String) (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let s ← elaborate cache input
  for m in s.messages do
    let line := s!"{path}:{m.render input}"
    if m.severity == .error then IO.eprintln line else IO.println line
  pure (if s.messages.any (·.severity == .error) then 1 else 0)

def elabFile (cache : Option String) (path : String) : IO (Option (CommandState ZeroOneMany)) := do
  let input ← IO.FS.readFile path
  let s ← elaborate cache input
  for m in s.messages do
    if m.severity == .error then IO.eprintln s!"{path}:{m.render input}"
  pure (if s.messages.any (·.severity == .error) then none else some s)

def buildCmd (cache : Option String) (path out : String) (llvm : Bool) : IO UInt32 := do
  let some s ← elabFile cache path | pure 1
  match Build.irProgram s "main" with
  | .error e => IO.eprintln e; pure 1
  | .ok (decls, ty) =>
    let io := Build.isIO ty
    let r ← if llvm then Build.compileLLVM (LLVM.program decls io) out (Build.extraC s ++ "\n" ++ C.glue (C.externs decls))
      else Build.compileC (C.program decls io (Build.extraC s)) out
    match r with
    | .error e => IO.eprintln e; pure 1
    | .ok () => pure 0

def runCmd (cache : Option String) (path : String) (llvm : Bool) : IO UInt32 := do
  let some s ← elabFile cache path | pure 1
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal s "main" dir llvm with
  | .error e => IO.eprintln e; pure 1
  | .ok v => IO.print (if v.endsWith "\n" then v else v ++ "\n"); pure 0

/-- The cache options, taken out of the arguments: `--cache DIR`, `--no-cache`. -/
def cacheOpt (dflt : Option String) : List String → Option String × List String
  | "--cache" :: dir :: rest => cacheOpt (some dir) rest
  | "--no-cache" :: rest => cacheOpt none rest
  | a :: rest => let (c, r) := cacheOpt dflt rest; (c, a :: r)
  | [] => (dflt, [])

def main (args : List String) : IO UInt32 := do
  let home := (← IO.getEnv "HOME").getD "."
  let (cache, args) := cacheOpt (some (home ++ "/.cache/wiz")) args
  match args with
  | ["parse", path] => parseCmd path
  | ["check", path] => checkCmd cache path
  | ["build", path, "-o", out] => buildCmd cache path out false
  | ["build", path, "-o", out, "--llvm"] => buildCmd cache path out true
  | ["run", path] => runCmd cache path false
  | ["run", path, "--llvm"] => runCmd cache path true
  | ["lsp"] => do LSP.serve (← loadLibraryPaths); pure 0
  | _ => do IO.println usage; pure 0
