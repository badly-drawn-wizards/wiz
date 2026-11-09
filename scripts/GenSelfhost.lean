/- Writes the inputs of the bootstrap fixpoint check (scripts/fixpoint.sh) into $OUT:
     compiler.wiz  the self-hosted compiler (Lex, Parse, Kernel, Frontend, Backend and the
                   driver of `selfhostCompiler` in Tests/Elab.lean): reads `input.wiz` in
                   its working directory and prints C (the frontend's output as comments)
     self.wiz      the same program as an input (the toolchain compiling itself)
   usage (from the repository root): OUT=DIR lake lean scripts/GenSelfhost.lean
   (/workspace/wiz-tools/bench/GenBench.lean generates these and more for benchmarks.) -/
import Wiz
import Tests.Elab
open Wiz Tests.Elab

def strip (f : String) : String :=
  "\n".intercalate ((f.splitOn "\n").filter (!·.startsWith "import"))

def gen (out : String) : IO Unit := do
  IO.FS.createDirAll out
  let src ← ["Lex", "Parse", "Kernel", "Frontend", "Backend"].mapM fun f =>
    IO.FS.readFile s!"selfhost/{f}.wiz"
  let t := Builtin.tables
  let compiler := "import IO\nimport Std\n" ++ "\n".intercalate (src.map strip) ++ "\n" ++ wizTables t ++
    s!"def tokens : List String := {wizList (t.tokens.toList.map wizLit)}\n" ++
    "def commentLines : List String → List String\n  | .nil => .nil\n  | .cons l rest => .cons (String.append \"/* \" (String.append l \" */\")) (commentLines rest)\n" ++
    "def main : IO Unit := do\n  text ← IO.readFile \"input.wiz\";\n  match runCommands cats tokens .nil (String.codes text) 0 Globals.empty .nil with\n    | .mk out gs _ _ _ => do\n      printAll (commentLines (List.reverseOf out .nil));\n      printDocs (genProgram gs)\n"
  IO.FS.writeFile s!"{out}/compiler.wiz" compiler
  IO.FS.writeFile s!"{out}/self.wiz" ("import Prelude\n" ++ strip compiler)

-- `lake lean` passes no arguments to the file, so the output directory comes from $OUT.
#eval show IO Unit from do gen ((← IO.getEnv "OUT").getD ".")
