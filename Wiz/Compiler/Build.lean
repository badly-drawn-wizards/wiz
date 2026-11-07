import Wiz.Elab.Command
import Wiz.Compiler.C
import Wiz.Compiler.Lower

/-!
# Building executables

`wiz build FILE -o OUT` compiles the definition `main` of a file to C (`C.lean`) and
then to an executable with a C compiler: `$WIZ_CC` (default `cc`), with extra flags
from `$WIZ_CFLAGS` and `$WIZ_LDFLAGS` (for example where GMP lives). The executable
prints its result as a generic tree (`(tag fields…)` and numbers); `wiz run` reads
that back with `main`'s type, like `#eval`.
-/

namespace Wiz.Build

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- The C program that computes the global `n`, and `n`'s type. -/
def cProgram (s : CommandState R) (n : Name) : Except String (String × Term R) := do
  let some d := s.globals.find? n | throw s!"no definition {n}"
  let code ← (compileReachable s.globals s.builtins [n]).mapError toString
  let decls ← IR.lowerProgram code (.global n)
  pure (C.program (decls.map (·.insertRC)), d.type)

def words (s : Option String) : List String :=
  ((s.getD "").splitOn " ").filter (· ≠ "")

/-- Compile C source to an executable. -/
def compileC (src : String) (exe : System.FilePath) : IO (Except String Unit) := do
  let cFile := exe.withExtension "c"
  IO.FS.writeFile cFile src
  let cc := (← IO.getEnv "WIZ_CC").getD "cc"
  let args := #["-O2", "-w", "-o", exe.toString, cFile.toString] ++ (words (← IO.getEnv "WIZ_CFLAGS")).toArray ++
    #["-lgmp"] ++ (words (← IO.getEnv "WIZ_LDFLAGS")).toArray
  let out ← IO.Process.output { cmd := cc, args }
  if out.exitCode == 0 then pure (.ok ()) else pure (.error s!"{cc} failed:\n{out.stderr}")

/-- Parse the printed result: numbers, `(tag fields…)`, `<fn>`. -/
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
    | cs => let (n, rest) ← num cs; return (.nat n, rest)

/-- Build and run the global `n`; returns its result, read back with its type. -/
def runGlobal (s : CommandState R) (n : Name) (dir : System.FilePath) : IO (Except String String) := do
  match cProgram s n with
  | .error e => pure (.error e)
  | .ok (src, ty) =>
    let exe := dir / "wiz_main"
    match ← compileC src exe with
    | .error e => pure (.error e)
    | .ok () =>
      let out ← IO.Process.output { cmd := exe.toString }
      if out.exitCode != 0 then return .error s!"the program failed ({out.exitCode}): {out.stderr}"
      match parseValue out.stdout with
      | none => pure (.error s!"could not read the result: {out.stdout}")
      | some v => pure (.ok (readback s.globals s.builtins (eval s.globals [] ty) v).pretty)

end Wiz.Build
