import Tests.Rig
import Tests.Eval
import Tests.Check
import Tests.Parser

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

open Tests

def groups : List Group :=
  [Rig.group, Eval.evalGroup, Eval.convGroup, Check.mlttGroup, Check.qttGroup,
   Parser.lexGroup, Parser.termGroup, Parser.cmdGroup]

/-- `lake test` runs everything; `lake test -- conv rig` runs only groups whose name
starts with one of the arguments. -/
def main : List String → IO UInt32
  | ["--run", group, ix] =>
    match groups.find? (·.name == group) >>= (·.cases[ix.toNat!]?) with
    | some c => c.runHere
    | none => do IO.eprintln s!"no such case: {group} #{ix}"; pure 2
  | args => do
    let selected := if args.isEmpty then groups
      else groups.filter fun g => args.any (g.name.startsWith ·)
    let mut passed := 0
    let mut failed := 0
    for g in selected do
      let (p, f) ← g.run
      passed := passed + p
      failed := failed + f
    IO.println s!"\n{passed} passed, {failed} failed"
    pure (if failed == 0 then 0 else 1)
