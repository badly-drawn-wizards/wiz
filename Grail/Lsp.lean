import Grail.Build

/-!
# `grail lsp` (stage 23l, docs/stages/23-grail.md)

The language server, `wiz lsp`, finds modules under the toolchain's library, `./lib` and
its `-I` directories. In a grail package the modules live under the roots of its `lib`
targets (and of its dependencies' `lib` targets), which only grail knows: `grail lsp`
reads `grail.wiz`, and runs `wiz lsp` in the package directory with the toolchain grail
would use for a `check` (`grail.wiz`'s and `grail.local.wiz`'s settings, then the
flags) and the package's module roots as `-I` directories, in grail's order (the package
directory, the `lib` roots, the dependencies' roots, then the toolchain's own `-I`). Its
stdin, stdout and stderr are the server's; grail prints nothing on stdout.
-/

namespace Grail
open Wiz

/-- The `wiz` to run: `--wiz PATH`, else the `wiz` beside this program (an installed
toolchain, or `.lake/build/bin`), else `wiz` on `PATH`. -/
def wizExe (opt : Option String) : IO String := do
  if let some w := opt then return w
  let beside := ((← IO.appPath).parent.getD ".") / "wiz"
  if ← beside.pathExists then return beside.toString
  pure "wiz"

/-- `wiz`'s arguments: the toolchain's flags, with `roots` first among the `-I`
directories, then `lsp` and its own options. -/
def lspArgs (tc : Toolchain) (roots : List System.FilePath) (opts : List String) : Array String :=
  let rest := tc.searchPath.filter (!roots.contains ·)
  ({ tc with searchPath := roots ++ rest }.toFlags ++ "lsp" :: opts).toArray

/-- Absolute paths (the server runs in the package directory). -/
def absolute (p : System.FilePath) : IO System.FilePath := do
  if p.isAbsolute then return p
  pure ((← IO.currentDir) / p)

/-- Run `wiz ARGS` in `dir` with this process's stdio; its exit code. -/
def runLsp (wiz : String) (args : Array String) (dir : System.FilePath) : IO UInt32 := do
  let child ← try IO.Process.spawn { cmd := wiz, args, cwd := dir }
    catch e => IO.eprintln s!"grail lsp: {wiz}: {e}"; return 127
  child.wait

end Grail
