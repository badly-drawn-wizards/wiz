import Tests.ElabFix

/-!
# Scaling (agent/mem-hunt)

Regression tests for super-linear time or memory: each case scales one dimension of
its input (fields of a structure, …) well past where the old blow-up made it
unusable, and bounds the case's time. The bounds are loose, two orders of magnitude
above what the case takes now: they catch exponential behaviour, not noise.
-/

open Wiz

set_option compiler.extract_closed false

namespace Tests.Scaling


/-- Checking `input` (with the Lean kernel, no library, in a child process:
`tests --check`) succeeds within `secs` seconds. A child process, so that a regression
times out instead of hanging the suite (address space capped at 8 GB, like
`checkDiverges`: the runtime reserves a large thread stack, so a tight cap fails). -/
def checksWithin (secs : Nat) (input : String) : IO Unit := do
  let dir ← IO.FS.createTempDir
  IO.FS.writeFile (dir / "input.wiz") input
  let self ← IO.appPath
  let out ← IO.Process.output { cmd := "sh", cwd := dir, args := #["-c",
    s!"ulimit -v 8000000; exec timeout {secs} \"$0\" --check off input.wiz", self.toString] }
  if out.exitCode == 124 then throw (IO.userError s!"took longer than {secs} s")
  unless out.exitCode == 0 do
    throw (IO.userError s!"exit code {out.exitCode}: {(out.stdout ++ out.stderr).take 1500}")

/-- Unary numbers, so that the inputs need no library. -/
def natDecl : String := "inductive N where\n  | z\n  | s (n : N)\n"

/-- A structure with `n` fields, its constructor applied, and its last field. -/
def wideStructure (n : Nat) : String :=
  natDecl ++ "structure S where\n" ++ String.join ((List.range n).map (s!"  f{·} : N\n")) ++
  s!"def x : S := S.mk {" ".intercalate ((List.range n).map fun _ => "N.z")}\n" ++
  s!"def y : N := x.f{n - 1}\n"

/-- A class with `n` methods shaped like the HDL's `Hw` (an implicit index, two
arguments), and an instance given by `where`. -/
def wideClass (n : Nat) : String :=
  natDecl ++ "class C (r : N → Type) where\n" ++
  String.join ((List.range n).map (s!"  op{·} : \{n : N} → r n → r n → r n\n")) ++
  "def K (n : N) : Type := N\ninstance : C K where\n" ++
  String.join ((List.range n).map (s!"  op{·} := fun a b => a\n"))

/-- A definition `s : String` of an `n`-character literal (`String.mk [Char.mk …, …]`: a
spine of `n` nested applications), checked by the kernel and then erased, within `secs`
seconds. -/
def longLiteral (n secs : Nat) : IO Unit := do
  let text := String.mk ((List.range n).map fun i => Char.ofNat (97 + i % 26))
  let input := s!"import Prelude\ndef s : String := \"{text}\"\n"
  let start ← IO.monoMsNow
  let loader ← Tests.Elab.preludeLoader
  let st := runFrontend (R := ZeroOneMany) input { loader }
  let errs := (st.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let checked := (← IO.monoMsNow) - start
  match compileReachable st.globals st.builtins ["s"] with
  | .ok code => check (code.contains "s") "s was not erased"
  | .error e => throw (IO.userError (toString e))
  let ms := (← IO.monoMsNow) - start
  unless ms ≤ secs * 1000 do
    throw (IO.userError s!"took {ms} ms ({checked} ms to check; bound: {secs} s)")

/-- The peak resident set size of this process in MB (`VmHWM`), after resetting it
(`clear_refs`), around `act`. -/
def peakOf {α : Type} (act : IO α) : IO (α × Nat) := do
  try IO.FS.writeFile "/proc/self/clear_refs" "5" catch _ => pure ()
  let a ← act
  pure (a, ← Tests.ElabFix.peakMB)

/-- The program's IR, reference counted by both `Decl.insertRC` (one pass) and the
specification `insertRC`, with the borrow signatures `optimizeProgram` uses: the
declarations on which they differ. -/
def rcMismatches (st : CommandState ZeroOneMany) (root : Name) : IO (List Name) := do
  let code ← match compileReachable st.globals st.builtins [root] with
    | .ok c => pure c
    | .error e => throw (IO.userError (toString e))
  let decls ← match IR.lowerProgram code (.global root) with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let decls := (IR.hoistConsts decls).map fun d => { d with body := (IR.elimDead d.body).1 }
  let bs := IR.inferBorrow decls
  pure <| decls.toList.filterMap fun d =>
    let σ : IR.BorrowSigs := { fns := bs.fns, jps := (bs.jps.get? d.name).getD {} }
    if (d.insertRC σ).toString == (d.insertRCSpec σ).toString then none else some d.name

/-- Elaborate `src` (with the library), or fail. -/
def elabOk (src : String) : IO (CommandState ZeroOneMany) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let stdLib ← IO.FS.readFile "lib/Std.wiz"
  let effLib ← IO.FS.readFile "lib/Eff.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Std" then some stdLib
    else if m == "Eff" then some effLib else none
  let st := runFrontend (R := ZeroOneMany) src { loader }
  let errs := (st.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure st

/-- A program with an `n`-character string literal (`s`, printed by `main`). -/
def literalProgram (n : Nat) : String :=
  let text := String.mk ((List.range n).map fun i => Char.ofNat (97 + i % 26))
  s!"import IO\ndef s : String := \"{text}\"\ndef main : IO Unit := IO.println s\n"

def group : Group where
  name := "scaling"
  exercise := "super-linear time and memory"
  cases := [
    -- `Level.normalize (imax a b)` normalised `b` twice: 2^n on the chain of `imax`es
    -- that is a telescope's sort (`S.mk`'s type, the class's methods)
    { name := "a structure with 64 fields (Level.normalize was exponential: 24 took 49 s)", run := fun _ =>
        checksWithin 60 (wideStructure 64) },
    { name := "a class with 48 Hw-like methods and an instance (was exponential: 16 took 4 s)", run := fun _ =>
        checksWithin 60 (wideClass 48) },
    -- the kernel's application and pair rules, and erasure's spines, evaluated every
    -- argument for the codomain, which a non-dependent Π doesn't mention: O(n²) on a
    -- nested spine (4000 characters: 32 s to build)
    { name := "a 20000-character string literal is checked and erased in linear time", run := fun _ =>
        longLiteral 20000 60 },
    -- `insertRC` recomputed the free variables of the rest of the body at each binding
    -- (and kept them while handling the rest): quadratic in time and space along a chain
    -- of bindings, the constant a literal becomes (6000 characters: 18 000 bindings, about
    -- 10 s and 4 GB)
    { name := "the IR of a 6000-character literal is reference counted in linear time and space", run := fun _ => do
        let st ← elabOk (literalProgram 6000)
        let start ← IO.monoMsNow
        let (r, mb) ← peakOf (pure (Build.irProgram st "main"))
        let ms := (← IO.monoMsNow) - start
        let .ok (decls, _) := r | throw (IO.userError "no IR")
        check (decls.size > 0) "no declarations"
        unless ms ≤ 30000 && mb ≤ 1000 do
          throw (IO.userError s!"took {ms} ms and {mb} MB (bounds: 30 s, 1000 MB)") },
    { name := "one-pass reference counting agrees with the specification (insertRC)", run := fun _ => do
        let examples ← ["examples/std.wiz", "examples/io.wiz", "examples/effects.wiz"].mapM (fun (f : String) => IO.FS.readFile f)
        for p in examples ++ [literalProgram 300] do
          let bad ← rcMismatches (← elabOk p) "main"
          unless bad.isEmpty do throw (IO.userError s!"they differ on {bad}") }]


/-! ### A probe (`tests --probe-checker`): where building the self-hosted checker spends
its time and memory, phase by phase, and whether the one-pass reference counting agrees
with the specification on all of it. -/

def rss : IO String := do
  let s ← IO.FS.readFile "/proc/self/status"
  let get (k : String) : String := ((s.splitOn "\n").find? (·.startsWith k)).getD "" |>.drop k.length |>.trimAscii.toString
  pure s!"rss {get "VmRSS:"}, peak {get "VmHWM:"}"

def probeChecker : IO Unit := do
  let t0 ← IO.monoMsNow
  let say (what : String) : IO Unit := do
    IO.eprintln s!"[{((← IO.monoMsNow) - t0) / 1000} s] {what}: {← rss}"
    try IO.FS.writeFile "/proc/self/clear_refs" "5" catch _ => pure ()
  let src ← Selfhost.checkerFiles.mapM (fun (f : String) => IO.FS.readFile f)
  let prog := Selfhost.checkerSource src
  say "start"
  let st ← elabOk prog
  say s!"frontend ({st.globals.decls.size} globals)"
  let code ← match compileReachable st.globals st.builtins ["main"] with
    | .ok c => pure c
    | .error e => throw (IO.userError (toString e))
  say s!"erasure ({code.size} definitions)"
  let decls ← match IR.lowerProgram code (.global "main") with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  say s!"lowering ({decls.size} declarations)"
  let hoisted := IR.hoistConsts decls
  say s!"hoisting ({hoisted.size} declarations)"
  let opt := IR.optimizeProgram hoisted
  say s!"optimizeProgram ({opt.size} declarations)"
  let c := C.program opt true (Build.extraC st)
  say s!"C ({c.length} characters)"
  let bad ← rcMismatches st "main"
  say s!"reference counting: one pass and specification differ on {bad.length} declarations {bad.take 10}"

/-- This module's test groups, which `Tests/Main.lean` runs: one per line, in sorted
order, so that branches adding groups rarely touch the same lines. A new group also
needs a shard in `.github/test-shards.json` (CI checks). -/
def groups : List Group :=
  group ::
  []

end Tests.Scaling
