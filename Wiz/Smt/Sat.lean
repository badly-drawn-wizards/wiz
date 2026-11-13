import Wiz.Smt.Process

/-!
# The SAT solver's side of `sat_decide` (stage 28b): untrusted

The CNF comes from Wiz (`Sat.fullCnf`, literals `2v` / `2v+1` over variables `0 …`); it
is written as DIMACS (variable `v` is `v+1`), the solver (CaDiCaL: `cadical IN OUT --lrat
--no-binary`) writes an LRAT proof, and this module reads it back into steps
`(id, literals, hints)`. Nothing here is trusted: the kernel checks the proof
(`Sat.lratCheck`, lib/Sat.wiz), so a bug here can only make `sat_decide` fail.
-/

namespace Wiz.Smt

def dimacs (nvars : Nat) (clauses : List (List Nat)) : String := Id.run do
  let mut out := s!"p cnf {nvars} {clauses.length}\n"
  for c in clauses do
    for l in c do
      let v := l / 2 + 1
      out := out ++ (if l % 2 == 1 then s!"-{v} " else s!"{v} ")
    out := out ++ "0\n"
  pure out

private def litOfInt (i : Int) : Nat :=
  if i < 0 then 2 * ((-i).toNat - 1) + 1 else 2 * (i.toNat - 1)

/-- LRAT text (`id lits… 0 hints… 0`, and deletions `id d ids… 0`, dropped) as steps. A
RAT step (a negative hint) is refused: the Wiz checker does RUP only. -/
def parseLrat (txt : String) : Except String (List (Nat × List Nat × List Nat)) := do
  let mut steps : Array (Nat × List Nat × List Nat) := #[]
  for line in txt.splitOn "\n" do
    let ws := (line.splitOn " ").filter (· ≠ "")
    match ws with
    | [] => continue
    | _ :: "d" :: _ => continue
    | idS :: rest =>
      let some id := idS.toNat? | throw s!"LRAT: bad line `{line}`"
      let ints ← rest.mapM fun w => match w.toInt? with
        | some i => pure i
        | none => throw s!"LRAT: bad line `{line}`"
      let (lits, rest) := ints.span (· ≠ 0)
      let hints := (rest.drop 1).takeWhile (· ≠ 0)
      if hints.any (· < 0) then throw "LRAT: a RAT step (the checker does RUP only)"
      steps := steps.push (id, lits.map litOfInt, hints.map Int.toNat)
  pure steps.toList

inductive SatResult where
  | unsat (proof : List (Nat × List Nat × List Nat))
  | sat (model : List Nat)
  | error (msg : String)
  deriving Inhabited

/-- Ask the SAT solver (exit code 20: unsatisfiable, with the proof; 10: a model, from the
`v` lines). -/
def satSolve (cfg : Config) (nvars : Nat) (clauses : List (List Nat)) : SatResult :=
  let secs := max 1 (cfg.timeoutMs / 1000)
  match runSolver cfg cfg.satSolver ["-q", "-t", toString secs, "--lrat", "--no-binary", "{in}", "{out}"]
      (dimacs nvars clauses) "cnf" true (fun a => a.exitCode == 10 || a.exitCode == 20) with
  | .error e => .error e
  | .ok (_, a) =>
    if a.exitCode == 20 then
      match parseLrat a.outFile with
      | .ok p => .unsat p
      | .error e => .error e
    else if a.exitCode == 10 then
      let lits := (a.stdout.splitOn "\n").filter (·.startsWith "v ") |>.flatMap fun l =>
        ((l.drop 2).toString.splitOn " ").filterMap String.toInt?
      .sat (lits.filter (· > 0) |>.map litOfInt)
    else .error s!"the SAT solver gave no answer (exit code {a.exitCode}): {a.stdout.trimAscii.toString}"

end Wiz.Smt
