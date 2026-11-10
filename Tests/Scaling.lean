import Tests.Elab

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
        longLiteral 20000 60 }]

end Tests.Scaling

namespace Tests.Scaling
open Wiz

/-- (temporary probe, mem-hunt) the resident set size now and at its peak, in MB -/
def rss : IO String := do
  let s ← IO.FS.readFile "/proc/self/status"
  let get (k : String) : String := ((s.splitOn "\n").find? (·.startsWith k)).getD "" |>.drop k.length |>.trimAscii.toString
  pure s!"rss {get "VmRSS:"} peak {get "VmHWM:"}"

def probeChecker : IO Unit := do
  let t0 ← IO.monoMsNow
  let say (what : String) : IO Unit := do IO.eprintln s!"[{((← IO.monoMsNow) - t0) / 1000} s] {what}: {← rss}"
  let src ← Selfhost.checkerFiles.mapM (fun (f : String) => IO.FS.readFile f)
  let prog := Selfhost.checkerSource src
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let stdLib ← IO.FS.readFile "lib/Std.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Std" then some stdLib else none
  say "start"
  let s := runFrontend (R := ZeroOneMany) prog { loader }
  say s!"frontend ({s.messages.size} messages, {s.globals.decls.size} globals)"
  let some _ := s.globals.find? "main" | throw (IO.userError "no main")
  let code ← match compileReachable s.globals s.builtins ["main"] with
    | .ok c => pure c
    | .error e => throw (IO.userError (toString e))
  say s!"erasure ({code.size} definitions)"
  let mut est : Array (Nat × String) := #[]
  for (n, _) in code.toList do
    if let some d := s.globals.find? n then
      let a ← IO.monoNanosNow
      let r := eraseDecl s.globals d
      let ok := match r with | .ok e => (e.globals #[]).size | .error _ => 0
      let b ← IO.monoNanosNow
      est := est.push ((b - a) / 1000000, s!"erase {n}: {(b - a) / 1000000} ms ({ok} globals, value {(d.value.map (·.pretty.length)).getD 0} chars)")
  for (_, l) in (est.qsort (fun x y => x.1 > y.1)).toList.take 15 do IO.eprintln l
  let decls ← match IR.lowerProgram code (.global "main") with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  say s!"lowering ({decls.size} decls)"
  let hoisted := IR.hoistConsts decls
  say s!"hoist ({hoisted.size} decls)"
  -- per declaration: the time of each pass, and the size of its body
  let rec size : IR.Body → Nat
    | .vdecl _ _ b | .dup _ b | .drop _ b => size b + 1
    | .case _ alts => alts.foldl (fun n a => n + size a) 1
    | .jdecl _ _ b k => size b + size k + 1
    | _ => 1
  let rec depth : IR.Body → Nat
    | .vdecl _ _ b | .dup _ b | .drop _ b => depth b + 1
    | .case _ alts => alts.foldl (fun n a => max n (depth a)) 0 + 1
    | .jdecl _ _ b k => max (depth b) (depth k) + 1
    | _ => 1
  let mut stats : Array (Nat × String) := #[]
  for d in hoisted do
    try IO.FS.writeFile "/proc/self/clear_refs" "5" catch _ => pure ()
    let a ← IO.monoNanosNow
    let d1 := { d with body := (IR.elimDead d.body).1 }
    let n1 := size d1.body
    let b ← IO.monoNanosNow
    let d2 := d1.insertRC
    let n2 := size d2.body
    let c ← IO.monoNanosNow
    let d3 := { d2 with body := IR.insertReuse (IR.reuseAcross {} {} (IR.dropScalars d2.body)) }
    let n3 := size d3.body
    let e ← IO.monoNanosNow
    let hwm ← rss
    stats := stats.push ((e - a) / 1000000, s!"{d.name} [{hwm}]: size {size d.body} depth {depth d.body} -> {n1}/{n2}/{n3}; elimDead {(b-a)/1000000} ms, insertRC {(c-b)/1000000} ms, reuse {(e-c)/1000000} ms")
  for (_, l) in (stats.qsort (fun x y => x.1 > y.1)).toList.take 15 do IO.eprintln l
  let opt := hoisted.map (·.optimize)
  say s!"optimize ({opt.size} decls)"
  let c := C.program opt true (Build.extraC s)
  say s!"C ({c.length} chars)"

end Tests.Scaling
