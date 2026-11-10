import Wiz.Elab.Command
import Wiz.Compiler.C
import Wiz.Compiler.LLVM
import Wiz.Compiler.Lower
import Wiz.Toolchain

/-!
# Building executables

`wiz build FILE -o OUT` compiles the definition `main` of a file to C (`C.lean`) and
then to an executable with the C compiler of the **toolchain** (`Wiz/Toolchain.lean`:
`--cc`, `--cflags`, `--ldflags`, for example where GMP lives), passed explicitly; nothing
is read from the environment. The executable
prints its result as a generic tree (`(tag fields…)` and numbers); `wiz run` reads
that back with `main`'s type, like `#eval`.
-/

namespace Wiz.Build

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- The optimised IR of a program computing the global `n`, and `n`'s type. -/
def irProgram (s : CommandState R) (n : Name) : Except String (Array IR.Decl × Term R) := do
  let some d := s.globals.find? n | throw s!"no definition {n}"
  let code ← (compileReachable s.globals s.builtins [n]).mapError toString
  let decls ← IR.lowerProgram code (.global n)
  pure (IR.optimizeProgram (IR.hoistConsts decls), d.type)

/-- Header includes and glue functions, in order. -/
def extraC (s : CommandState R) : String := "\n".intercalate s.cCode.toList

/-- Is this the type `IO A`? Then `main` is run, not printed. -/
def isIO (ty : Term R) : Bool := match (Term.spine ty).1 with
  | .const "IO" _ => true
  | _ => false

/-- The C program that computes the global `n`, and `n`'s type. -/
def cProgram (s : CommandState R) (n : Name) : Except String (String × Term R) := do
  let (decls, ty) ← irProgram s n
  pure (C.program decls (isIO ty) (extraC s), ty)

def words (s : Option String) : List String :=
  ((s.getD "").splitOn " ").filter (· ≠ "")

/-- Compile C source to an executable. -/
def compileC (tc : Toolchain) (src : String) (exe : System.FilePath) : IO (Except String Unit) := do
  let cFile := exe.withExtension "c"
  IO.FS.writeFile cFile src
  let cc := tc.cc
  let args := #["-O2", "-w", "-o", exe.toString, cFile.toString] ++ tc.cflags.toArray ++
    #["-lgmp"] ++ tc.ldflags.toArray ++ tc.libs.toArray
  let out ← IO.Process.output { cmd := cc, args }
  if out.exitCode == 0 then pure (.ok ()) else pure (.error s!"{cc} failed:\n{out.stderr}")

/-- Compile an LLVM module to an executable: `llc` (the toolchain's) for the module, the C
compiler for the runtime (exported with `-DWIZ_API=`), and the C compiler to link. -/
def compileLLVM (tc : Toolchain) (ll : String) (exe : System.FilePath) (glue : String := "") : IO (Except String Unit) := do
  let llFile := exe.withExtension "ll"
  let rtFile := exe.withFileName "wiz_runtime.c"
  IO.FS.writeFile llFile ll
  IO.FS.writeFile rtFile (C.runtime ++ "\n" ++ glue)
  let cc := tc.cc
  let llc := tc.llc
  let cflags := tc.cflags.toArray
  let step (cmd : String) (args : Array String) : IO (Except String Unit) := do
    try
      let out ← IO.Process.output { cmd, args }
      pure (if out.exitCode == 0 then .ok () else .error s!"{cmd} failed:\n{out.stderr}")
    catch e => pure (.error s!"{cmd}: {e}")
  let rtObj := exe.withFileName "wiz_runtime.o"
  let mainObj := exe.withExtension "o"
  if let .error e ← step cc (#["-O2", "-w", "-c", "-DWIZ_API=", "-o", rtObj.toString, rtFile.toString] ++ cflags) then
    return .error e
  if let .error e ← step llc #["-O2", "-filetype=obj", "-relocation-model=pic", "-o", mainObj.toString, llFile.toString] then
    return .error e
  step cc (#["-o", exe.toString, mainObj.toString, rtObj.toString, "-lgmp"] ++ tc.ldflags.toArray ++ tc.libs.toArray)

/-- Parse the printed result: numbers, `(tag fields…)`, `<fn>`, `#bits`. -/
partial def parseValue (s : String) : Option RVal :=
  match go s.toList with
  | some (v, rest) => if rest.all (·.isWhitespace) then some v else none
  | none => none
where
  ws (cs : List Char) : List Char := cs.dropWhile (·.isWhitespace)
  num (cs : List Char) : Option (Nat × List Char) :=
    let ds := cs.takeWhile Char.isDigit
    if ds.isEmpty then none else some (String.mk ds |>.toNat!, cs.drop ds.length)
  go (cs : List Char) : Option (RVal × List Char) := do
    match ws cs with
    | '(' :: rest =>
      let (t, rest) ← num (ws rest)
      let rec fields (cs : List Char) (acc : Array RVal) : Option (Array RVal × List Char) :=
        match ws cs with
        | ')' :: rest => some (acc, rest)
        | cs => do let (v, rest) ← go cs; fields rest (acc.push v)
      let (fs, rest) ← fields rest #[]
      return (.obj t fs, rest)
    | '<' :: 'f' :: 'n' :: '>' :: rest => return (.clo [] .erased, rest)
    -- a raw machine word (a native word of 64 bits, stage 22d)
    | '#' :: rest => let (n, rest) ← num rest; return (.nat n, rest)
    | cs => let (n, rest) ← num cs; return (.nat n, rest)

/-- Build and run the global `n` (through C, or LLVM); returns its result, read back
with its type. With `timeout`, the program is stopped after that many seconds (by
coreutils' `timeout`). -/
def runGlobal (tc : Toolchain) (s : CommandState R) (n : Name) (dir : System.FilePath) (llvm : Bool := false)
    (timeout : Option Nat := none) (args : Array String := #[]) :
    IO (Except String String) := do
  match irProgram s n with
  | .error e => pure (.error e)
  | .ok (decls, ty) =>
    let exe := dir / "wiz_main"
    let io := isIO ty
    let built ← if llvm then compileLLVM tc (LLVM.program decls io) exe (extraC s ++ "\n" ++ C.glue (C.externs decls) (extraC s))
      else compileC tc (C.program decls io (extraC s)) exe
    match built with
    | .error e => pure (.error e)
    | .ok () =>
      let out ← match timeout with
        | some t => IO.Process.output { cmd := "timeout", args := #[toString t, exe.toString] ++ args }
        | none => IO.Process.output { cmd := exe.toString, args }
      if out.exitCode == 124 && timeout.isSome then return .error "the program timed out"
      if out.exitCode != 0 then return .error s!"the program failed ({out.exitCode}): {out.stderr}"
      -- an `IO` program prints for itself
      if io then return .ok out.stdout
      match parseValue out.stdout with
      | none => pure (.error s!"could not read the result: {out.stdout}")
      | some v => pure (.ok (readback s.globals s.builtins (eval s.globals [] ty) v).pretty)

/-- Preprocess the headers a file imports (`import_c "h"`), since the frontend is pure. -/
def preprocessHeaders (tc : Toolchain) (input : String) : IO (Std.HashMap String String) := do
  let mut m : Std.HashMap String String := {}
  for part in (input.splitOn "import_c \"").drop 1 do
    let h := (part.splitOn "\"").headD ""
    if h.isEmpty || m.contains h then continue
    let cc := tc.cc
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "h.c") s!"#include <{h}>\n"
    let out ← IO.Process.output { cmd := cc, args := #["-E", "-P", (dir / "h.c").toString] ++ tc.cflags.toArray }
    if out.exitCode == 0 then m := m.insert h out.stdout
  pure m


end Wiz.Build
