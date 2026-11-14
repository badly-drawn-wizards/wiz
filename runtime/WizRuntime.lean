/-!
# The C runtime, as text

`runtime/wiz.c`, embedded in the compiler (`Wiz.C.program` pastes it at the top of every
C program). This module is a library of its own, `WizRuntime` in `lakefile.lean`, whose
`needs` names `wiz.c` as an input file: Lake mixes the file's content hash into this
module's trace, so editing `wiz.c` rebuilds this module (and its importers) and nothing
else, and Lake's artifact cache never serves a stale one.
-/

namespace Wiz.C

/-- The runtime, `runtime/wiz.c`. -/
def runtime : String := include_str "wiz.c"

end Wiz.C
