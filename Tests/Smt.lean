import Wiz
import Tests.Harness
import Tests.Elab

/-!
# Solvers: `sat_decide` with LRAT proofs checked by the kernel (stage 28b)

The group `sat`. Cases that need the solver skip (with the reason) when it is not on PATH;
CI's Nix shell has it (flake.nix: cadical).
-/

open Wiz

set_option compiler.extract_closed false

namespace Tests.Smt

def render (s : CommandState ZeroOneMany) : List String :=
  s.messages.toList.map fun m =>
    s!"{match m.severity with | .error => "error" | .warning => "warning" | .info => "info"}: {m.text}"

/-- Every message of `input`, with all of `lib/` importable. -/
def msgs (input : String) (cfg : Smt.Config := {}) : IO (List String) := do
  let loader ← Elab.libLoader
  pure (render (runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule, smt := cfg }))

def has (ms : List String) (fragment : String) : Bool := ms.any fun m => (m.splitOn fragment).length > 1

def expect (ms : List String) (fragment : String) : IO Unit :=
  unless has ms fragment do throw (IO.userError s!"no message mentions '{fragment}':\n{"\n".intercalate ms}")

def noErrors (ms : List String) : IO Unit := do
  let errs := ms.filter (·.startsWith "error")
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs}")

/-- Is `cmd` on PATH? -/
def onPath (cmd : String) : IO Bool := do
  try
    let out ← IO.Process.output { cmd, args := #["--version"] }
    pure (out.exitCode == 0)
  catch _ => pure false

def needs (cmd : String) (k : IO Unit) : IO Unit := do
  if ← onPath cmd then k else skip s!"no {cmd} on PATH (nix develop has it)"

/-- The four clauses over two variables, refuted by CaDiCaL (its LRAT, by hand). -/
def tinyCnf : String :=
  "import Sat\n" ++
  "def P (v : Nat) : Sat.Lit := Sat.Lit.mk v .true\ndef N (v : Nat) : Sat.Lit := Sat.Lit.mk v .false\n" ++
  "def cnf : List (List Sat.Lit) := [[P 1, P 2], [N 1, P 2], [P 1, N 2], [N 1, N 2]]\n" ++
  "def proof : List Sat.Step := [Sat.Step.add 5 [P 1] [1, 3], Sat.Step.add 6 [P 2] [5, 2], Sat.Step.add 7 [] [5, 6, 4]]\n"

def group : Group where
  name := "sat"
  exercise := "—"
  cases := [
    { name := "lib/Sat.wiz: the checker and its soundness proof check, with no axioms", run := fun _ => do
        let ms ← msgs ("import Sat\n#print axioms Sat.lratCheck_sound\n#print axioms Sat.decide_sound\n")
        noErrors ms
        expect ms "info: 'Sat.lratCheck_sound' does not depend on any axioms"
        expect ms "info: 'Sat.decide_sound' does not depend on any axioms" },
    { name := "an LRAT proof is checked by the kernel; a wrong one is not accepted", run := fun _ => do
        let ms ← msgs (tinyCnf ++ "def ok : Sat.lratCheck cnf proof = .true := rfl\n" ++
          "def unsat (τ : Nat → Bool) (h : Sat.Cnf.eval τ cnf = .true) : False := Sat.lratCheck_sound cnf proof ok τ h\n")
        noErrors ms
        -- a hint that does not propagate (clause 2 is not unit under ¬1)
        let ms ← msgs (tinyCnf ++ "def bad : Sat.lratCheck cnf [Sat.Step.add 5 [P 1] [2, 3], Sat.Step.add 7 [] [5, 4]] = .true := rfl\n")
        check (has ms "error") s!"a wrong proof was accepted: {ms}"
        -- a proof that never derives the empty clause
        let ms ← msgs (tinyCnf ++ "def bad : Sat.lratCheck cnf [Sat.Step.add 5 [P 1] [1, 3]] = .true := rfl\n")
        check (has ms "error") s!"an unfinished proof was accepted: {ms}" },
    { name := "sat_decide: Bool identities, checked by the kernel, no axioms", run := fun _ => needs "cadical" do
        let ms ← msgs ("import SatTactic\n" ++
          "def demorgan (a b : Bool) : Bool.not (Bool.and a b) = Bool.or (Bool.not a) (Bool.not b) := by sat_decide\n" ++
          "def xorAssoc (a b c : Bool) : Bool.xor a (Bool.xor b c) = Bool.xor (Bool.xor a b) c := by sat_decide\n" ++
          "def excluded : (a : Bool) → Bool.or a (Bool.not a) = .true := by sat_decide\n" ++
          "def atoms (m n : Nat) : Bool.or (Nat.lt m n) (Bool.not (Nat.lt m n)) = .true := by sat_decide\n" ++
          "#print axioms demorgan\n#print axioms atoms\n")
        noErrors ms
        expect ms "info: 'demorgan' does not depend on any axioms"
        expect ms "info: 'atoms' does not depend on any axioms" },
    { name := "sat_decide: circuit equivalence (a 2-bit adder: ripple carry against the majority form)", run := fun _ => needs "cadical" do
        let ms ← msgs ("import SatTactic\n" ++
          "def maj (a b c : Bool) : Bool := Bool.or (Bool.or (Bool.and a b) (Bool.and a c)) (Bool.and b c)\n" ++
          "def carry (a b c : Bool) : Bool := Bool.or (Bool.and a b) (Bool.and c (Bool.xor a b))\n" ++
          "def carry_maj (a b c : Bool) : carry a b c = maj a b c := by\n  unfold carry, maj\n  sat_decide\n" ++
          "def add2 (a0 a1 b0 b1 c : Bool) : Bool.xor (Bool.xor a1 b1) (carry a0 b0 c) = Bool.xor (Bool.xor b1 a1) (maj b0 a0 c) := by\n  unfold carry, maj\n  sat_decide\n" ++
          "#print axioms add2\n")
        noErrors ms
        expect ms "info: 'add2' does not depend on any axioms" },
    { name := "sat_decide with sharing (28c): a 4-bit carry chain over definitions, not unfolded", run := fun _ => needs "cadical" do
        let maj := "def maj (a b c : Bool) : Bool := Bool.or (Bool.or (Bool.and a b) (Bool.and a c)) (Bool.and b c)\n"
        let carry := "def carry (a b c : Bool) : Bool := Bool.or (Bool.and a b) (Bool.and c (Bool.xor a b))\n"
        let c1 := "(carry a2 b2 (carry a1 b1 (carry a0 b0 Bool.false)))"
        let c2 := "(maj b2 a2 (maj b1 a1 (maj b0 a0 Bool.false)))"
        let ms ← msgs ("import SatTactic\n" ++ maj ++ carry ++
          s!"def eq4 (a0 b0 a1 b1 a2 b2 a3 b3 : Bool) : Bool.xor (Bool.xor a3 b3) {c1} = Bool.xor (Bool.xor b3 a3) {c2} := by sat_decide\n" ++
          "#print axioms eq4\n#print axioms Sat.dag_sound\n")
        noErrors ms
        expect ms "info: 'eq4' does not depend on any axioms"
        expect ms "info: 'Sat.dag_sound' does not depend on any axioms" },
    { name := "sat_decide: a false goal fails with a counterexample", run := fun _ => needs "cadical" do
        let ms ← msgs ("import SatTactic\ndef wrong (a b : Bool) : Bool.and a b = Bool.or a b := by sat_decide\n")
        expect ms "sat_decide: the goal is false; a counterexample:" },
    { name := "the flags: --sat-solver and --solver-timeout are taken and passed on; not settings", run := fun _ => do
        let (t, rest) := ({} : Toolchain).parseFlags ["--sat-solver", "kissat", "--solver-timeout", "500", "check", "f.wiz"]
        checkEq ["check", "f.wiz"] rest
        checkEq "kissat" t.smt.satSolver
        checkEq 500 t.smt.timeoutMs
        let (t', _) := ({} : Toolchain).parseFlags t.toFlags
        check (t'.smt == t.smt) "toFlags does not round-trip"
        let (u, _) := ({} : Toolchain).parseFlags ["check", "f.wiz"]
        check (Cache.smtKey u.smt == none) "the default settings must not change cache keys"
        check (Cache.smtKey t.smt != none) "the solver settings are not in the cache keys"
        -- a grail file (`Toolchain.set`) can't name a program for wiz to run
        check (({} : Toolchain).set "sat-solver" "/bin/sh").isNone "sat-solver is a setting" }
  ]

def groups : List Group := [group]

end Tests.Smt
