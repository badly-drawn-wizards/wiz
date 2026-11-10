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

def gen (out : String) : IO Unit := do
  IO.FS.createDirAll out
  let src ← Selfhost.compilerFiles.mapM fun (f : String) => IO.FS.readFile f
  -- (the driver of `Selfhost.compilerSource`: `--rc` on the command line picks reference
  -- counting, stage 21k)
  IO.FS.writeFile s!"{out}/compiler.wiz" (Selfhost.compilerSource src)
  IO.FS.writeFile s!"{out}/self.wiz" (Selfhost.selfSource src)

-- `lake lean` passes no arguments to the file, so the output directory comes from $OUT.
#eval show IO Unit from do gen ((← IO.getEnv "OUT").getD ".")
