import Wiz
import Wiz.Version

open Wiz

def usage : String := "usage:
  wiz --version           print the version (and, for a release, its commit)
  wiz parse FILE          print the syntax tree of every command
  wiz check FILE          elaborate and type check (quantities: 0, 1, ω)
  wiz build FILE -o OUT [--llvm]   compile the definition `main` to an executable (via C or LLVM)
  wiz build FILE -o OUT --lib      … or the exported functions to an object file, with OUT.h
  wiz build FILE -o OUT --no-main  … or the exported functions, linked without a `main`
                                   (say, a Wasm module: --cc emcc --ldflags --no-entry)
  wiz run FILE [--llvm]            build and run `main`, printing its value
  wiz lsp                          a language server on stdin/stdout
  wiz lsp --infoview SOCK          … and for infoviews on the Unix socket SOCK
  wiz lsp --ws [ADDR:]PORT         … and on a WebSocket (127.0.0.1 unless ADDR is given;
                                   both flags may be given; --no-stdio: no editor on stdin)
options: --cache DIR (the elaboration cache, default ~/.cache/wiz; shared, since it is
content-addressed), --no-cache, -I DIR (another module root, after lib/)
trust: --trust-native (27a: `def X : a = b := native_refl` is decided by running a and b;
the kernel does not check it, `#print axioms` lists it), --native-fuel N (its step limit)
experimental kernel options (D1, they turn the cache off): --regularity off|full|nonprop|refl
(default off),
--predicative-prop, --eager-proofs (P2: the evaluator runs proofs, as it did before; the
default never evaluates them),
--inert syntactic|ground|conv (P1: regularity at inert types; default ground)
compiler option (turns the cache off): --unbox-structs (22i: a structure's last field is
unboxed; not stable under substitution, so off by default)
--strict-privacy (13b, an experiment; turns the cache off): check each declaration again with
  the definitions of other modules' types with private parts hidden
--pp-all (11r; turns the cache off): print terms without notation (as `set_option pp.all true`)
toolchain: --cc X (default: a release's own share/wiz/cc, else cc), --cflags \"…\" --ldflags \"…\" (where GMP lives),
  --libs \"…\" (say -lm), --gmp \"…\" (default -lgmp), --llc X (default llc)"

def parseCmd (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let r := parseFile input
  for cmd in r.commands do
    IO.println cmd.toSExpr
  for m in r.messages do
    IO.eprintln s!"{path}:{m.render input}"
  pure (if r.messages.isEmpty then 0 else 1)

/-- The module roots: the toolchain's library (`Module.toolchainLib`, the binary's own,
whatever the current directory; `./lib` only when there is none), then the `-I`
directories. Only the first root's modules are trusted (stage 22f), and since the first
root that has a module wins, no other directory can stand in for one of them. (`./lib`
is not searched besides: run in another checkout, every module of its `lib/` would be
reported as shadowed.) -/
def moduleRoots (tc : Toolchain) : IO (List System.FilePath) :=
  Module.roots tc.searchPath

/-- The library modules from the toolchain's own `lib/` (the first root): their
`builtin` registrations are trusted. -/
def libTrusted (tc : Toolchain) : IO (List String) := do
  let roots ← moduleRoots tc
  return Module.fromFirstRoot roots (← Module.loadAll roots)

/-- Library modules with their paths (for the language server's go-to-definition). -/
def loadLibraryPaths (tc : Toolchain) : IO (Std.HashMap String (String × String)) := do
  let mut m : Std.HashMap String (String × String) := {}
  for (n, p, src) in (← Module.loadAll (← moduleRoots tc)).toList do
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

/-- `--strict-privacy` (13b, an experiment): the second check of every declaration against
the elaborator's view. Off by default. -/
initialize strictPrivacyOpt : IO.Ref Bool ← IO.mkRef false

/-- (11r) `--pp-all`: terms print without notation. -/
initialize ppAllOpt : IO.Ref Bool ← IO.mkRef false

/-- P2: proofs are never evaluated, unless `--eager-proofs` (the old behaviour). -/
initialize lazyProofsOpt : IO.Ref Bool ← IO.mkRef true

/-- (P1) `--inert MODE`: regularity at inert types. -/
initialize inertOpt : IO.Ref InertReg ← IO.mkRef .ground

/-- `--unbox-structs` (22i): the last field of a structure is unboxed. Off by default: the
representation is not stable under substitution (`unboxedSigma` in `Erase.lean`). -/
initialize unboxOpt : IO.Ref Bool ← IO.mkRef false

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
def elaborate (tc : Toolchain) (path : String) (input : String) : IO (CommandState ZeroOneMany) := do
  -- every module the file can reach (`import A.B` is `A/B.wiz` under a root), read up
  -- front: the frontend is pure
  let roots ← moduleRoots tc
  let closure ← Module.loadClosure roots input
  let lib : Std.HashMap Name String := closure.fold (fun m n (_, src) => m.insert n src) {}
  -- the C headers of the file and of the modules it imports
  let headers ← Build.preprocessHeaders tc (String.join (input :: lib.values))
  -- (9f) the `link_c` files, each relative to its own file
  let sources ← Module.cSourceTable ((System.FilePath.mk path).parent.getD ".") input closure
  let (regularity, predicativeProp) ← kernelOpts.get
  let lazyProofs ← lazyProofsOpt.get
  let inertReg ← inertOpt.get
  let unboxStructs ← unboxOpt.get
  -- `builtin` registrations are trusted only in the toolchain's own library
  let own := Module.fromFirstRoot roots closure
  -- a file that would replace one of them is ignored: say so (loudly: it may be meant
  -- to stand in for the toolchain's module, `builtin`s and all)
  let shadow := (← Module.shadowed roots closure).map fun (n, p) =>
    ({ info := {}, severity := .warning,
       text := s!"{p} is ignored: module {n} is the toolchain's own ({roots.head!}), which a module root cannot replace" } : Msg)
  let init : CommandState ZeroOneMany :=
    { loader := (lib[·]?), cHeaders := (headers[·]?), cSources := some (Module.cSourceResolver sources),
      messages := shadow.toArray,
      globals := { regularity, predicativeProp, lazyProofs, inertReg, unboxStructs, strictPrivacy := ← strictPrivacyOpt.get,
                   pp := { useNotation := !(← ppAllOpt.get) } },
      trustedModule := own.contains, trustNative := tc.trustNative,
      nativeFuel := tc.nativeFuel.getD NativeRun.defaultFuel, smt := ← tc.smt.resolve }
  -- the cache doesn't know the experimental options
  let cache := if regularity == .off && !predicativeProp && lazyProofs && inertReg == .ground && !unboxStructs &&
      !(← strictPrivacyOpt.get) && !(← ppAllOpt.get)
    then tc.cacheDir else none
  match cache with
  | none => Cache.elaborateUncached input init
  | some dir =>
    -- the key starts from the headers the file sees; modules enter it by their own keys
    let key₀ := hash (toString (headers.toList.map (·.2)))
    pure (← Cache.elaborateCached dir input init key₀).1

/-- (27a) `--trust-native` and `--native-fuel N`. -/
def nativeOpts (tc : Toolchain) : Bool × Nat := (tc.trustNative, tc.nativeFuel.getD NativeRun.defaultFuel)

def checkCmd (tc : Toolchain) (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let s ← elaborate tc path input
  for m in s.messages do
    let line := s!"{path}:{m.render input}"
    if m.severity == .error then IO.eprintln line else IO.println line
  pure (if s.messages.any (·.severity == .error) then 1 else 0)

def elabFile (tc : Toolchain) (path : String) : IO (Option (CommandState ZeroOneMany)) := do
  let input ← IO.FS.readFile path
  let s ← elaborate tc path input
  for m in s.messages do
    if m.severity == .error then IO.eprintln s!"{path}:{m.render input}"
  pure (if s.messages.any (·.severity == .error) then none else some s)

def buildCmd (tc : Toolchain) (path out : String) (llvm : Bool) (lib : Bool := false) (noMain : Bool := false) : IO UInt32 := do
  let some s ← elabFile tc path | pure 1
  match ← Build.build tc s "main" out llvm lib noMain with
  | .error e => IO.eprintln e; pure 1
  | .ok _ => pure 0

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
  if args == ["--version"] then IO.println (← versionLine "wiz"); return 0
  let home := (← IO.getEnv "HOME").getD "."
  -- the toolchain comes from flags only (no environment variables)
  -- (26f) a release toolchain's own C compiler, GMP and GC are the defaults
  let defaults ← ({ cacheDir := some (System.FilePath.mk home / ".cache" / "wiz") } : Toolchain).withBundled
  let (tc, args) := defaults.parseFlags args
  if args.contains "--strict-privacy" then strictPrivacyOpt.set true
  let args := args.filter (· != "--strict-privacy")
  if args.contains "--pp-all" then ppAllOpt.set true
  let args := args.filter (· != "--pp-all")
  if args.contains "--unbox-structs" then unboxOpt.set true
  let args := args.filter (· != "--unbox-structs")
  lazyProofsOpt.set (!args.contains "--eager-proofs")
  let args := args.filter (· != "--eager-proofs")
  let args ← match takeInertOpt args with
    | .ok (r, a) => do if let some r := r then inertOpt.set r
                       pure a
    | .error e => do IO.eprintln e; return 1
  let args ← match kernelOpt args with
    | .ok (r, p, a) => do kernelOpts.set (r, p); pure a
    | .error e => do IO.eprintln e; return 1
  -- a `panic!` (a kernel-internal failure) ends a batch command with status 1 instead of
  -- going on with a default value; the language server keeps running
  unless args.head? == some "lsp" do exitOnPanic
  match args with
  | ["parse", path] => parseCmd path
  | ["check", path] => checkCmd tc path
  | ["build", path, "-o", out] => buildCmd tc path out false
  | ["build", path, "-o", out, "--llvm"] => buildCmd tc path out true
  | ["build", path, "-o", out, "--lib"] => buildCmd tc path out false true
  | ["build", path, "-o", out, "--lib", "--llvm"] | ["build", path, "-o", out, "--llvm", "--lib"] =>
    buildCmd tc path out true true
  | ["build", path, "-o", out, "--no-main"] => buildCmd tc path out false false true
  | ["build", path, "-o", out, "--no-main", "--llvm"] | ["build", path, "-o", out, "--llvm", "--no-main"] =>
    buildCmd tc path out true false true
  | ["run", path] => runCmd tc path false
  | ["run", path, "--llvm"] => runCmd tc path true
  | ["lsp"] => do LSP.serve (← loadLibraryPaths tc) (trusted := ← libTrusted tc) (native := nativeOpts tc) (smt := ← tc.smt.resolve); pure 0
  | "lsp" :: opts => do
    match lspOptions opts with
    | none => IO.println usage; pure 2
    | some (listen, stdio) =>
      LSP.serve (← loadLibraryPaths tc) listen stdio (← libTrusted tc) (nativeOpts tc) (← tc.smt.resolve)
      -- (an infoview's reader thread may still be blocked: don't wait for it)
      IO.Process.exit 0
  | _ => do IO.println usage; pure 0
