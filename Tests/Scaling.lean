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

/-- `H₁ ⋆ (… ⋆ (Hₙ ⋆ (p ↦ a))) ⊢ H₁ ⋆ (… ⋆ (Hₙ ⋆ (p ↦ b)))` "proved" by reflexivity: the
mismatch is at the far end of the chain. -/
def wrongStarChain (n : Nat) : String :=
  let hs := (List.range n).map (s!"H{·}")
  let chain (last : String) := hs.foldr (fun h acc => s!"{h} ⋆ ({acc})") last
  s!"import HProp\ndef bad (p a b : Nat) ({" ".intercalate hs} : HProp Nat) :\n  {chain "p ↦ a"} ⊢ {chain "p ↦ b"} :=\n" ++
  s!"  Entails.refl ({chain "p ↦ a"})\n"

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
  let text := String.ofList ((List.range n).map fun i => Char.ofNat (97 + i % 26))
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
def peakOf {α : Type} (act : Unit → IO α) : IO (α × Nat) := do
  try IO.FS.writeFile "/proc/self/clear_refs" "5" catch _ => pure ()
  let a ← act ()
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

/-- `act` within `secs` seconds and `mb` megabytes (peak RSS, reset first). -/
def within {α : Type} (secs mb : Nat) (act : Unit → IO α) : IO α := do
  let start ← IO.monoMsNow
  let (a, peak) ← peakOf act
  let ms := (← IO.monoMsNow) - start
  unless ms ≤ secs * 1000 && peak ≤ mb do
    throw (IO.userError s!"took {ms} ms and {peak} MB (bounds: {secs} s, {mb} MB)")
  pure a

/-- A list of `n` numerals written out: `List.cons 0 (List.cons 1 (… List.nil))`. -/
def listSource (n : Nat) : String :=
  String.join ((List.range n).map (s!"List.cons {·} (")) ++ "List.nil" ++ String.ofList (List.replicate n ')')

/-- Elaborate `src` (with the library), or fail. -/
def elabOk (src : String) (unbox : Bool := false) : IO (CommandState ZeroOneMany) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let stdLib ← IO.FS.readFile "lib/Std.wiz"
  let effLib ← IO.FS.readFile "lib/Eff.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Std" then some stdLib
    else if m == "Eff" then some effLib else none
  let st := runFrontend (R := ZeroOneMany) src { loader, globals := { unboxStructs := unbox } }
  let errs := (st.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure st

/-- A program with an `n`-character string literal (`s`, printed by `main`). -/
def literalProgram (n : Nat) : String :=
  let text := String.ofList ((List.range n).map fun i => Char.ofNat (97 + i % 26))
  s!"import IO\ndef s : String := \"{text}\"\ndef main : IO Unit := IO.println s\n"

/-- Milliseconds to erase `f`, a match on a constructor with `n` fields (returning the
last one): elaboration is not counted. -/
def eraseMatchMs (n : Nat) : IO Nat := do
  let fields := " ".intercalate ((List.range n).map (s!"x{·}"))
  let src := s!"import Prelude\ninductive T where\n  | mk {" ".intercalate ((List.range n).map (s!"(x{·} : Nat)"))}\n" ++
    s!"def f (t : T) : Nat := match t with\n  | .mk {fields} => x{n - 1}\n"
  let st ← elabOk src
  let start ← IO.monoMsNow
  match compileReachable st.globals st.builtins ["f"] with
  | .ok code => check (code.contains "f") "f was not erased"
  | .error e => throw (IO.userError (toString e))
  pure ((← IO.monoMsNow) - start)

/-! ### Direct hypotheses against the template (kernel-eval-2, P2)

`vHyps` computes an induction's hypotheses on a canonical description directly; its
definition is `Templates.hypsTm` (`vHypsTemplate`). They must agree, as read back, on every
description: every global whose type ends in `Desc I`, applied to variables, at every
constructor (the tags enumerated, the other fields variables). -/

/-- The descriptions among `g`'s globals: the level, `I` and `D`, after applying each to
fresh variables (levels from 0). -/
def descsOf (g : Globals ZeroOneMany) : Array (Name × Level × Val ZeroOneMany × Val ZeroOneMany × Nat) := Id.run do
  let mut out := #[]
  for n in g.order do
    let some d := g.find? n | continue
    if d.value.isNone then continue
    let mut ty := whnf (eval g [] d.type)
    let mut v : Val ZeroOneMany := eval g [] (.const n (d.levelParams.map Level.param))
    let mut k := 0
    for _ in [0:12] do
      match ty with
      | .pi _ _ _ _ B _ =>
        ty := whnf (Closure.inst g B (Val.var k)); v := vApp g v (Val.var k); k := k + 1
      | _ => break
    if let .desc l I := ty then out := out.push (n, l, I, v, k)
  pure out

/-- Payloads for `D`: the tags enumerated (at most `budget` in all), other fields fresh
variables from level `k`. -/
partial def payloads (g : Globals ZeroOneMany) (D : Val ZeroOneMany) (k budget : Nat) :
    List (Val ZeroOneMany × Nat) :=
  if budget == 0 then [] else
  match whnf D with
  | .darg _ S E => match tagField? S with
    | some (ls, lifted) =>
      (List.range ls.length).flatMap fun t =>
        let tg : Val ZeroOneMany := if lifted then .up (.tag ls t) else .tag ls t
        (payloads g (vApp g E tg) k (budget / ls.length)).map fun (r, k') => (.pair tg r, k')
    | none => (payloads g (vApp g E (Val.var k)) (k + 1) budget).map fun (r, k') => (.pair (Val.var k) r, k')
  | .drec _ _ E | .dhrec _ _ _ E => (payloads g E (k + 1) budget).map fun (r, k') => (.pair (Val.var k) r, k')
  | _ => [(Val.var k, k + 1)]

/-- The descriptions (and payloads) on which `vHyps` and the template read back differently. -/
def hypsMismatches (g : Globals ZeroOneMany) (extra : List (Name × Level × Val ZeroOneMany × Val ZeroOneMany × Nat) := [])
    (direct : Globals ZeroOneMany → Level → Level → (I D X P f i xs : Val ZeroOneMany) → Val ZeroOneMany := vHyps) :
    Nat × List String := Id.run do
  let mut n := 0
  let mut bad := []
  for (name, l, I, D, k) in (descsOf g).toList ++ extra do
    for (xs, k') in payloads g D k 64 do
      -- X P f i: variables above everything else
      let (X, P, f, i) := (Val.var k', Val.var (k' + 1), Val.var (k' + 2), Val.var (k' + 3))
      let L := k' + 4
      let a := quote g L (direct g l .zero I D X P f i xs)
      let b := quote g L (vHypsTemplate g l .zero I D X P f i xs)
      n := n + 1
      unless a == b do bad := s!"{name}: {a.pretty []} vs {b.pretty []}" :: bad
  pure (n, bad)

/-- Modules of `lib/` that can't be imported together with all the others (`Json`
declares its own `Nat.repr`), checked on their own. -/
def libApart : List String := ["Json", "Infoview"]

/-- Every other module of `lib/` imported at once. -/
def allLibSource : IO String := do
  let mut ms := #[]
  for e in ← System.FilePath.readDir "lib" do
    if e.path.extension == some "wiz" then ms := ms.push (e.path.fileStem.getD "")
    else if ← e.path.isDir then
      for f in ← System.FilePath.readDir e.path do
        if f.path.extension == some "wiz" then ms := ms.push (e.fileName ++ "." ++ f.path.fileStem.getD "")
  pure (String.join (((ms.qsort (· < ·)).toList.filter (!libApart.contains ·)).map (s!"import {·}\n")))

/-- `n` matches on a `len`-element list, checked by `refl`. -/
def listMatchProgram (len n : Nat) : String :=
  "import Prelude\n" ++
  "def rep : Nat → List Nat\n  | .zero => .nil\n  | .succ k => .cons 1 (rep k)\n" ++
  s!"def l : List Nat := rep {len}\n" ++
  "def isNil : List Nat → Bool\n  | .nil => .true\n  | .cons _ _ => .false\n" ++
  "def count : Nat → Nat\n  | .zero => 0\n  | .succ k => match isNil l with\n    | .true => count k\n    | .false => Nat.add 1 (count k)\n" ++
  s!"def t : count {n} = {n} := refl {n}\n"

/-- A structurally recursive function whose recursive call is under a `fun`. -/
def hypUnderBinder : String :=
  "def sumF : List Nat → Nat → Nat\n  | .nil => fun k => k\n  | .cons x xs => fun k => sumF xs (Nat.add k x)\n"

/-- A circuit with a chain of 1500 adders and xors, and a counter on long traces. -/
def hdlScaleSrc : String := "import Hdl.Core
def u8 : HwTy := HwTy.bits 8
def chainOf {r : HwTy → Type} [Hw r] : Nat → r u8 → r u8 → r u8
  | .zero, x, y => x
  | .succ k, x, y => let z := Hw.xor (Hw.add x y) (Hw.lit 8 k); chainOf k z x
def big : Circuit u8 u8 := Circuit.mk u8 (BitVec.ofNat 8 1) (fun s x => let y := chainOf 1500 s x; Hw.pair y y)
def Rng.trace : Nat → Nat → List Nat
  | .zero, _ => .nil
  | .succ k, s => .cons (Nat.mod s 256) (Rng.trace k (Nat.mod (s * 1103515245 + 12345) 2147483648))
def ok : Bool × Nat := let xs := Rng.trace 100 7; (Hdl.natsEq (Circuit.runPacked big xs) (Circuit.simNet .true big xs), Netlist.size (Circuit.netlist \"big\" big))
#eval ok
def ctr : Circuit u8 u8 := Circuit.mk u8 (BitVec.ofNat 8 0) (fun s x => Hw.pair (Hw.add s x) s)
def Rep.go : Nat → List (HwTy.El u8) → List (HwTy.El u8)
  | .zero, acc => acc
  | .succ k, acc => Rep.go k (List.cons (BitVec.ofNat 8 3) acc)
def n : Nat := List.length (Circuit.run ctr (Rep.go 200000 List.nil))
#eval n
def m : Nat := List.length (Netlist.simulate (Circuit.netlist \"c\" ctr) (Hdl.map (fun (v : HwTy.El u8) => List.cons (BitVec.toNat v) List.nil) (Rep.go 200000 List.nil)))
#eval m
"

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
    -- a failed unification of glued definitions tried every order of unfolding, and the
    -- same comparisons again under the fresh variables of each unfolded `Ex`: a wrong
    -- `⋆` law took minutes to be rejected
    { name := "a wrong law about a chain of 16 ⋆ is rejected (was exponential: one ⋆ took over 120 s)", run := fun _ =>
        Tests.Elab.failsLibsWithin 60 (wrongStarChain 16) "mismatch" },
    -- the kernel's application and pair rules, and erasure's spines, evaluated every
    -- argument for the codomain, which a non-dependent Π doesn't mention: O(n²) on a
    -- nested spine (4000 characters: 32 s to build)
    -- the kernel's first `.1` rule (Q1) evaluated the pair to find the second part's
    -- fields, so `(Circuit.netlistS c).1` (lib/Hdl/Core.wiz) ran the netlist builder at
    -- check time and overflowed the stack; here the second part takes 2^40 steps to
    -- evaluate. (R1: the rule no longer looks at the components at all.)
    { name := "p.1 is checked without evaluating p", run := fun _ =>
        checksWithin 60 (natDecl ++
          "def blow : N → N × N\n  | .z => (N.z, N.z)\n  | .s n => let (a, b) := blow n; let (c, d) := blow n; (a, d)\n" ++
          s!"def big : N × (N × N) := (N.z, blow {String.join ((List.range 40).map fun _ => "(N.s ")}N.z{String.mk (List.replicate 40 ')')})\n" ++
          "def y : N := big.1\n") },
    { name := "a 20000-character string literal is checked and erased in linear time", run := fun _ =>
        longLiteral 20000 60 },
    -- `insertRC` recomputed the free variables of the rest of the body at each binding
    -- (and kept them while handling the rest): quadratic in time and space along a chain
    -- of bindings, the constant a literal becomes (6000 characters: 18 000 bindings, about
    -- 10 s and 4 GB)
    { name := "the IR of a 6000-character literal is reference counted in linear time and space", run := fun _ => do
        let st ← elabOk (literalProgram 6000)
        let r ← within 30 1000 fun _ => pure (Build.irProgram st "main")
        let .ok (decls, _) := r | throw (IO.userError "no IR")
        check (decls.size > 0) "no declarations" },
    -- the parser kept the state from before each alternative (`orElse`, `tryAlternative`)
    -- while the alternative ran: every memo and token-table insertion in it copied the
    -- whole table (20000 elements: over 5 GB; now under 200 MB)
    { name := "an 8000-element nested term parses in linear time and space", run := fun _ => do
        let r ← within 30 400 fun _ => pure (parseCategory Builtin.tables "term" (listSource 8000))
        match r with
        | .ok _ => pure ()
        | .error e => throw (IO.userError e) },
    -- checking an application solved each argument's placeholder by evaluating the
    -- argument (and `inferApp` instantiated each codomain with it): quadratic along a
    -- nested spine
    { name := "a 16000-element list written out is elaborated in linear time and space", run := fun _ => do
        let _ ← within 30 1000 fun _ => elabOk s!"import Prelude\ndef l : List Nat := {listSource 16000}\n"
        pure () },
    -- erasure re-inferred the body of each `split` with the kernel (a match's tree of
    -- nested splits was checked again once per level), `erasable` recomputed the sort of
    -- the rest of the telescope at each field, and each step of a field's projection chain
    -- `p.2.2.….1` asked for the type of the rest of the chain, evaluating `p` each time.
    -- 400 fields: 46 s before, under 1 s now (still super-linear: about ×6 per doubling)
    { name := "a match on a 400-field constructor is erased within 10 s (was 46 s)", run := fun _ => do
        let ms ← eraseMatchMs 400
        unless ms ≤ 10000 do throw (IO.userError s!"took {ms} ms (bound: 10 s)") },
    -- (the price of the shortcut: it believes the sort a Π/Σ carries. The kernel validates
    -- it in every term erasure is given, a definition's implementation for the compiler
    -- included, so there is no unchecked term to make an exception for: the flag
    -- `sortNotesChecked` that this case used to test is gone; Status.md, T1)
    { name := "erasure believes a Π's sort, and the kernel rejects a wrong one wherever erasure could read it", run := fun _ => do
        -- `Type → Type` marked as a proposition: erasure would take its values for proofs
        let w : Val ZeroOneMany := .qlit QuantitySyntax.explicitDefault
        let ty : Val ZeroOneMany := .pi "x" .default w (.sort 1) (.mk [] (.sort 1)) (some 0)
        check (erasable { globals := {} } ty) "the annotation is read"
        -- so no declaration may carry it: not in its type, its value, or its implementation
        let bad : Term ZeroOneMany := .pi "x" .default (.qlit QuantitySyntax.explicitDefault) (.sort 1) (.sort 1) (some 0)
        let good : Term ZeroOneMany := .pi "x" .default (.qlit QuantitySyntax.explicitDefault) (.sort 1) (.sort 1) none
        let d (type value : Term ZeroOneMany) (impl : Option (Term ZeroOneMany)) : Decl ZeroOneMany :=
          { name := "T", type, value := some value, impl }
        check ((addDecl {} (d (.sort 2) good none)) matches .ok _) "the unmarked type was rejected"
        check ((addDecl {} (d (.sort 2) good (some good))) matches .ok _) "a good implementation was rejected"
        check ((addDecl {} (d (.sort 2) bad none)) matches .error _) "a wrong sort was accepted in a value"
        check ((addDecl {} (d (.sort 2) good (some bad))) matches .error _)
          "a wrong sort was accepted in an implementation (erasure would believe it)"
        let idT (t : Term ZeroOneMany) : Term ZeroOneMany := .pi "f" .default (.qlit QuantitySyntax.explicitDefault) t (t.lift 1) none
        check ((addDecl {} { name := "i", type := idT good, value := some (.lam "f" (.var 0)) }) matches .ok _)
          "the identity on Type → Type was rejected"
        check ((addDecl {} { name := "i", type := idT bad, value := some (.lam "f" (.var 0)) }) matches .error _)
          "a wrong sort was accepted in a declaration's type" },
    -- (kernel-eval) `ind` computed the hypotheses of a constructor by value, and the
    -- hypothesis of a recursive field is `ind` on it: a `match` (`T.casesOn`, which ignores
    -- them) on a list ran through the whole tail. 1000 matches on a 2000-element list:
    -- 2 million `ind` steps per evaluation of the statement (the elaborator's and the
    -- kernel's); now a hypothesis is computed when used (`Val.lazyInd`)
    { name := "a match on a list does not run through its tail (1000 matches on 2000 elements)", run := fun _ => do
        let _ ← within 30 1000 fun _ => elabOk (listMatchProgram 2000 1000)
        pure () },
    -- the same laziness must not lose a hypothesis that is used, here under a binder
    { name := "a recursive call used under a `fun` is still computed (lazy hypotheses)", run := fun _ => do
        let _ ← elabOk ("import Prelude\n" ++ hypUnderBinder ++ "def t : sumF (.cons 1 (.cons 2 (.cons 3 .nil))) 0 = 6 := refl 6\n")
        let loader ← Tests.Elab.preludeLoader
        let st := runFrontend (R := ZeroOneMany) ("import Prelude\n" ++ hypUnderBinder ++
          "def t : sumF (.cons 1 (.cons 2 (.cons 3 .nil))) 0 = 7 := refl 7\n") { loader }
        check (st.messages.any (·.severity == .error)) "a wrong sum was accepted" },
    -- (P2) the direct hypotheses are the template's, on every description of the library
    -- and the examples, and on stuck descriptions (where the direct one falls back)
    { name := "direct induction hypotheses agree with the template on every Desc in lib/ and examples/", run := fun _ => do
        let loader ← Tests.Elab.libLoader
        let lib := runFrontend (R := ZeroOneMany) (← allLibSource) { trustedModule := Tests.libModule, loader }
        let errs := lib.messages.filter (·.severity == .error)
        unless errs.isEmpty do throw (IO.userError s!"the library has errors: {(errs.toList.take 3).map (·.text)}")
        -- (the comparison can fail: a variant with the pairs swapped is caught)
        let swapped := fun g l v I D X P f i xs => match vHyps g l v I D X P f i xs with
          | .pair a b => .pair b a
          | h => h
        check (!(hypsMismatches lib.globals (direct := swapped)).2.isEmpty) "a wrong variant was not caught"
        let mut total := 0
        -- stuck: the whole description a variable, and an `arg` whose rest is a variable
        let w : Val ZeroOneMany := .qlit QuantitySyntax.explicitDefault
        let stuck := [("a variable", Level.zero, (.unit 0 : Val ZeroOneMany), Val.var 0, 1),
          ("arg then a variable", .zero, .unit 0, .darg w (.sort 0) (Val.var 0), 1),
          ("rec then a variable", .zero, .unit 0, .drec w .tt (.darg w (.sort 0) (Val.var 0)), 1)]
        let (n, bad) := hypsMismatches lib.globals stuck
        unless bad.isEmpty do throw (IO.userError s!"lib: {bad.take 3}")
        total := total + n
        for m in libApart do
          let st := runFrontend (R := ZeroOneMany) s!"import {m}\n" { trustedModule := Tests.libModule, loader }
          unless st.messages.all (·.severity != .error) do throw (IO.userError s!"lib/{m} has errors")
          let (n, bad) := hypsMismatches st.globals
          unless bad.isEmpty do throw (IO.userError s!"{m}: {bad.take 3}")
          total := total + n
        for e in ← System.FilePath.readDir "examples" do
          unless e.path.extension == some "wiz" do continue
          let st := runFrontend (R := ZeroOneMany) (← IO.FS.readFile e.path) { trustedModule := Tests.libModule, loader }
          if st.messages.any (·.severity == .error) then continue  -- (an example of an error)
          let (n, bad) := hypsMismatches st.globals
          unless bad.isEmpty do throw (IO.userError s!"{e.path}: {bad.take 3}")
          total := total + n
        check (total > 1000) s!"only {total} cases" },
    -- (P3) a universe-polymorphic definition unfolds at the cached levels (0, 1, 2) and at
    -- others alike, and a wrong statement at a cached level is still rejected
    { name := "a polymorphic definition unfolds the same at cached and uncached levels", run := fun _ => do
        let src := "import Prelude\ndef pick.{u} (A : Type u) (a b : A) (c : Bool) : A := match c with\n  | .true => a\n  | .false => b\n" ++
          "def t0 : pick Nat 1 2 .false = 2 := refl 2\n" ++
          "def t1 : pick Type Nat Bool .true = Nat := refl Nat\n" ++
          "def t2 : pick (Type 1) Type (Type → Type) .true = Type := refl Type\n" ++
          "def t5 : pick (Type 4) (Type 3) (Type 3 → Type 3) .false = (Type 3 → Type 3) := refl (Type 3 → Type 3)\n"
        let _ ← elabOk src
        let loader ← Tests.Elab.preludeLoader
        let st := runFrontend (R := ZeroOneMany) (src ++ "def bad : pick Type Nat Bool .true = Bool := refl Bool\n") { loader }
        check (st.messages.any (·.severity == .error)) "a wrong unfolding was accepted" },
    -- the elaborator's sort pass (`Sorts.type`) no longer evaluates an equation to learn
    -- that it is a proposition; the kernel still checks every sort note itself
    { name := "a wrong sort note on a Π into an equation is rejected by the kernel", run := fun _ => do
        let w : Term ZeroOneMany := .qlit QuantitySyntax.explicitDefault
        let ty (s : Option Level) : Term ZeroOneMany := .pi "X" .default w (.sort 1) (.eqTy (.var 0) (.var 0)) s
        let d (s : Option Level) : Decl ZeroOneMany :=
          { name := "r", type := ty s, value := some (.lam "X" (.reflTy (.var 0))) }
        check ((addDecl {} (d none)) matches .ok _) "the unmarked declaration was rejected"
        check ((addDecl {} (d (some 0))) matches .ok _) "the right sort note was rejected"
        check ((addDecl {} (d (some 1))) matches .error _) "a wrong sort note (Type for a proposition) was accepted" },
    { name := "one-pass reference counting agrees with the specification (insertRC)", run := fun _ => do
        let examples ← ["examples/std.wiz", "examples/io.wiz", "examples/effects.wiz"].mapM (fun (f : String) => IO.FS.readFile f)
        for p in examples ++ [literalProgram 300] do
          let bad ← rcMismatches (← elabOk p) "main"
          unless bad.isEmpty do throw (IO.userError s!"they differ on {bad}") },
    -- the netlist interpreter appended to its list of node values and looked arguments up
    -- by position: O(n²) per cycle (FINDINGS.md G6 of the iCEstick project: traces were
    -- cut to 6000 cycles); now a random-access list, O(n log n). Here 3258 nodes for 100
    -- cycles (the old interpreter: about 5·10⁸ list steps), compared with the values;
    -- then `Circuit.run` and `Netlist.simulate` on a 200000-cycle trace.
    { name := "the HDL's netlist simulation is O(n log n) per cycle; long traces run", run := fun _ =>
        within 120 1500 fun _ => Tests.Elab.okLibs hdlScaleSrc ["(.true, 3258)", "200000", "200000"] }]


/-! ### A probe (`tests --probe-checker [unbox] [rc]`): where building the self-hosted checker spends
its time and memory, phase by phase, and whether the one-pass reference counting agrees
with the specification on all of it. -/

def rss : IO String := do
  let s ← IO.FS.readFile "/proc/self/status"
  let get (k : String) : String := ((s.splitOn "\n").find? (·.startsWith k)).getD "" |>.drop k.length |>.trimAscii.toString
  pure s!"rss {get "VmRSS:"}, peak {get "VmHWM:"}"

def probeChecker (opts : List String := []) : IO Unit := do
  let t0 ← IO.monoMsNow
  let say (what : String) : IO Unit := do
    IO.eprintln s!"[{((← IO.monoMsNow) - t0) / 1000} s] {what}: {← rss}"
    try IO.FS.writeFile "/proc/self/clear_refs" "5" catch _ => pure ()
  let src ← Selfhost.checkerFiles.mapM (fun (f : String) => IO.FS.readFile f)
  let prog := Selfhost.checkerSource src
  say "start"
  let st ← elabOk prog (unbox := opts.contains "unbox")
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
  say s!"C ({c.length} characters, hash {hash c})"
  -- (the specification is quadratic in space: about 4.7 GB here, so only on request)
  if opts.contains "rc" then
    let bad ← rcMismatches st "main"
    say s!"reference counting: one pass and specification differ on {bad.length} declarations {bad.take 10}"

/-- This module's test groups, which `Tests/Main.lean` runs: one per line, in sorted
order, so that branches adding groups rarely touch the same lines. A new group also
needs a shard in `.github/test-shards.json` (CI checks). -/
def groups : List Group :=
  group ::
  []

end Tests.Scaling
