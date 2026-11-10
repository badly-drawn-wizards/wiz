import Wiz

open Wiz

def usage : String := "usage:
  wiz parse FILE          print the syntax tree of every command
  wiz check FILE          elaborate and type check (quantities: 0, 1, ω)
  wiz build FILE -o OUT [--llvm]   compile the definition `main` to an executable (via C or LLVM)
  wiz run FILE [--llvm]            build and run `main`, printing its value
  wiz lsp                          a language server on stdin/stdout
  wiz lsp --infoview SOCK          … and for infoviews on the Unix socket SOCK
  wiz lsp --ws [ADDR:]PORT         … and on a WebSocket (127.0.0.1 unless ADDR is given;
                                   both flags may be given; --no-stdio: no editor on stdin)
options: --cache DIR (the elaboration cache, default ~/.cache/wiz; shared, since it is
content-addressed), --no-cache, -I DIR (another module root, after lib/)
experimental kernel options (D1, they turn the cache off): --regularity off|full|nonprop|refl
(default off),
--predicative-prop, --eager-proofs (P2: the evaluator runs proofs, as it did before; the
default never evaluates them),
--inert syntactic|ground|conv (P1: regularity at inert types; default ground)
toolchain: --cc X (default cc), --cflags \"…\" --ldflags \"…\" (where GMP lives),
  --libs \"…\" (say -lm), --llc X (default llc)"

def parseCmd (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let r := parseFile input
  for cmd in r.commands do
    IO.println cmd.toSExpr
  for m in r.messages do
    IO.eprintln s!"{path}:{m.render input}"
  pure (if r.messages.isEmpty then 0 else 1)

/-- The module roots: `lib/` (the standard library), then the `-I` directories. -/
def moduleRoots (tc : Toolchain) : List System.FilePath := "lib" :: tc.searchPath

/-- The library modules from the toolchain's own `lib/` (the first root): their
`builtin` registrations are trusted. -/
def libTrusted (tc : Toolchain) : IO (List String) := do
  return Module.fromFirstRoot (moduleRoots tc) (← Module.loadAll (moduleRoots tc))

/-- Library modules with their paths (for the language server's go-to-definition). -/
def loadLibraryPaths (tc : Toolchain) : IO (Std.HashMap String (String × String)) := do
  let mut m : Std.HashMap String (String × String) := {}
  for (n, p, src) in (← Module.loadAll (moduleRoots tc)).toList do
    m := m.insert n ((← IO.FS.realPath p).toString, src)
  pure m

/-- `wiz lsp`'s options: `--infoview SOCK`, `--ws [ADDR:]PORT`, `--no-stdio`. -/
def lspOptions : List String → Option (LSP.Listen × Bool)
  | [] => some ({}, true)
  | "--infoview" :: sock :: rest => do let (l, io) ← lspOptions rest; pure ({ l with infoview := some sock }, io)
  | "--ws" :: spec :: rest => do
    let (l, io) ← lspOptions rest
    let (addr, port) ← match spec.splitOn ":" with
      | [p] => pure (Socket.loopback, p)
      | [a, p] => do pure (← Socket.parseIPv4 a, p)
      | _ => none
    let port ← port.toNat?
    if port ≥ 65536 then none
    pure ({ l with ws := some (addr, port.toUInt16) }, io)
  | "--no-stdio" :: rest => do let (l, _) ← lspOptions rest; pure (l, false)
  | _ => none

/-- The experimental kernel options (D1): `--regularity MODE`, `--predicative-prop`. -/
initialize kernelOpts : IO.Ref (Regularity × Bool) ← IO.mkRef (.off, false)

/-- P2: proofs are never evaluated, unless `--eager-proofs` (the old behaviour). -/
initialize lazyProofsOpt : IO.Ref Bool ← IO.mkRef true

/-- (P1) `--inert MODE`: regularity at inert types. -/
initialize inertOpt : IO.Ref InertReg ← IO.mkRef .ground

/-- Take `--inert MODE` out of the arguments. -/
def takeInertOpt : List String → Except String (Option InertReg × List String)
  | "--inert" :: m :: rest => do
    let r ← match m with
      | "syntactic" => pure InertReg.syntactic | "ground" => pure .ground | "conv" => pure .conv
      | _ => throw s!"unknown inert mode {m}"
    let (_, rest) ← takeInertOpt rest
    return (some r, rest)
  | a :: rest => do
    let (r, rest) ← takeInertOpt rest
    return (r, a :: rest)
  | [] => return (none, [])

/-- Elaborate a file, through the toolchain's cache (if any). -/
def elaborate (tc : Toolchain) (input : String) : IO (CommandState ZeroOneMany) := do
  let closure ← Module.loadClosure (moduleRoots tc) input
  let lib : Std.HashMap Name String := closure.fold (fun m n (_, src) => m.insert n src) {}
  -- the C headers of the file and of the modules it imports
  let headers ← Build.preprocessHeaders tc (String.join (input :: lib.values))
  let (regularity, predicativeProp) ← kernelOpts.get
  let lazyProofs ← lazyProofsOpt.get
  let inertReg ← inertOpt.get
  -- `builtin` registrations are trusted only in the toolchain's own library
  let own := Module.fromFirstRoot (moduleRoots tc) closure
  let init : CommandState ZeroOneMany :=
    { loader := (lib[·]?), cHeaders := (headers[·]?), globals := { regularity, predicativeProp, lazyProofs, inertReg },
      trustedModule := own.contains }
  -- the cache doesn't know the experimental options
  let cache := if regularity == .off && !predicativeProp && lazyProofs && inertReg == .ground then tc.cacheDir else none
  match cache with
  | none => Cache.elaborateUncached input init
  | some dir =>
    -- the key starts from the headers the file sees; modules enter it by their own keys
    let key₀ := hash (toString (headers.toList.map (·.2)))
    pure (← Cache.elaborateCached dir input init key₀).1

def checkCmd (tc : Toolchain) (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let s ← elaborate tc input
  for m in s.messages do
    let line := s!"{path}:{m.render input}"
    if m.severity == .error then IO.eprintln line else IO.println line
  pure (if s.messages.any (·.severity == .error) then 1 else 0)

def elabFile (tc : Toolchain) (path : String) : IO (Option (CommandState ZeroOneMany)) := do
  let input ← IO.FS.readFile path
  let s ← elaborate tc input
  for m in s.messages do
    if m.severity == .error then IO.eprintln s!"{path}:{m.render input}"
  pure (if s.messages.any (·.severity == .error) then none else some s)

def buildCmd (tc : Toolchain) (path out : String) (llvm : Bool) : IO UInt32 := do
  let some s ← elabFile tc path | pure 1
  match Build.irProgram s "main" with
  | .error e => IO.eprintln e; pure 1
  | .ok (decls, ty) =>
    let io := Build.isIO ty
    let r ← if llvm then Build.compileLLVM tc (LLVM.program decls io) out (Build.extraC s ++ "\n" ++ C.glue (C.externs decls) (Build.extraC s))
      else Build.compileC tc (C.program decls io (Build.extraC s)) out
    match r with
    | .error e => IO.eprintln e; pure 1
    | .ok () => pure 0

def runCmd (tc : Toolchain) (path : String) (llvm : Bool) : IO UInt32 := do
  let some s ← elabFile tc path | pure 1
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal tc s "main" dir llvm with
  | .error e => IO.eprintln e; pure 1
  | .ok v => IO.print (if v.endsWith "\n" then v else v ++ "\n"); pure 0

/-- The experimental kernel options, taken out of the arguments. -/
def kernelOpt : List String → Except String (Regularity × Bool × List String)
  | "--regularity" :: m :: rest => do
    let r ← match m with
      | "full" => pure Regularity.full | "nonprop" => pure .nonProp | "refl" => pure .refl
      | "off" => pure .off | _ => throw s!"unknown regularity mode {m}"
    let (_, p, rest) ← kernelOpt rest
    return (r, p, rest)
  | "--predicative-prop" :: rest => do
    let (r, _, rest) ← kernelOpt rest
    return (r, true, rest)
  | a :: rest => do
    let (r, p, rest) ← kernelOpt rest
    return (r, p, a :: rest)
  | [] => return (.off, false, [])

def main (args : List String) : IO UInt32 := do
  let home := (← IO.getEnv "HOME").getD "."
  -- the toolchain comes from flags only (no environment variables)
  let (tc, args) := ({ cacheDir := some (System.FilePath.mk home / ".cache" / "wiz") } : Toolchain).parseFlags args
  lazyProofsOpt.set (!args.contains "--eager-proofs")
  let args := args.filter (· != "--eager-proofs")
  let args ← match takeInertOpt args with
    | .ok (r, a) => do if let some r := r then inertOpt.set r
                       pure a
    | .error e => do IO.eprintln e; return 1
  let args ← match kernelOpt args with
    | .ok (r, p, a) => do kernelOpts.set (r, p); pure a
    | .error e => do IO.eprintln e; return 1
  match args with
  | ["parse", path] => parseCmd path
  | ["check", path] => checkCmd tc path
  | ["build", path, "-o", out] => buildCmd tc path out false
  | ["build", path, "-o", out, "--llvm"] => buildCmd tc path out true
  | ["run", path] => runCmd tc path false
  | ["run", path, "--llvm"] => runCmd tc path true
  | ["lsp"] => do LSP.serve (← loadLibraryPaths tc) (trusted := ← libTrusted tc); pure 0
  | "lsp" :: opts => do
    match lspOptions opts with
    | none => IO.println usage; pure 2
    | some (listen, stdio) =>
      LSP.serve (← loadLibraryPaths tc) listen stdio (← libTrusted tc)
      -- (an infoview's reader thread may still be blocked: don't wait for it)
      IO.Process.exit 0
  | _ => do IO.println usage; pure 0
