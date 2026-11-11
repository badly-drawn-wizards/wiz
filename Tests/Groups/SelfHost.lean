import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- (15g) Numerals for the self-hosted compiler, whose numbers are 63-bit words: up to
`2^63 - 1` (and the compiler does not overflow its stack halving 1000000000); arithmetic
wraps, also when the backend folds it at compile time. -/
def selfhostBigLits : String := "import Prelude
def printAll (ns : List Nat) : IO Unit := match ns with
  | .nil => IO.pure ()
  | .cons n rest => do
    IO.println (Nat.toString n);
    printAll rest
def main : IO Unit := printAll (.cons 1000000000 (.cons 2147483648 (.cons 4294967296 (.cons 4611686018427387904
  (.cons 9223372036854775807 (.cons (4611686018427387904 + 4611686018427387904) (.cons (4294967296 * 4294967297) .nil)))))))
"

def selfhostBigLitsExpected : String :=
  "1000000000\n2147483648\n4294967296\n4611686018427387904\n9223372036854775807\n0\n4294967296\n"

/-- Tokens as the Lean lexer reads them, as `kind:text` lines. -/
partial def leanTokens (tokens : Array String) (input : String) : List String :=
  let chars := input.toList.toArray
  let rec go (i : Nat) (acc : List String) : List String :=
    let i := skipWs chars i
    if i ≥ chars.size then acc.reverse else
    match readToken tokens chars i with
    | .ok t =>
      let line := match t.tok with
        | .atom a => "atom:" ++ a | .ident n => "ident:" ++ n | .num d => "num:" ++ d | .str s => "str:" ++ s
      go t.stop (line :: acc)
    | .error e => (("error:" ++ e) :: acc).reverse
  go 0 []

/-- What the Lean parser makes of `input`, printed like `parse` in `Parse.wiz`. -/
def leanParse (t : ParserTables) (cat : Name) (input : String) : String :=
  let chars := input.toList.toArray
  let p : P Syntax := do
    let stx ← categoryParser cat 0
    let i ← P.nextPos
    if i < chars.size then P.failAt i "end of input" else pure stx
  match p.run chars t with
  | .ok (stx, _) => stx.toSExpr (atoms := true)
  | .error e => s!"error {e.pos}: expected {", ".intercalate e.expected.toList}"

/-- What the Lean kernel says about a closed term: its type (printed like the Wiz
kernel prints) or `error`. -/
def leanVerdict (t : MTm) : String :=
  let g := leanGlobals ()
  match infer (R := ZeroOneMany) { globals := g } t.toTerm with
  | .ok (ty, _) => match MTm.ofTerm (quote g 0 ty) with
    | some m => m.pretty 0
    | none => "?"
  | .error _ => "error"

/-- A program for the self-hosted backend (recursion, lists, arrays, maps, strings, mutual
types), printing `6765 5050 1989 2 yes, ünïcode 2 5`. -/
def selfhostProgram1 : String :=
  "import Prelude\npartial def fib : Nat → Nat\n  | 0 => 0\n  | 1 => 1\n  | n + 2 => fib n + fib (n + 1)\npartial def countdown (n : Nat) (acc : List Nat) : List Nat := match n with\n  | 0 => acc\n  | .succ k => countdown k (List.cons n acc)\ndef sum : List Nat → Nat\n  | .nil => 0\n  | .cons x xs => x + sum xs\ndef fill (a : Array Nat) : Nat → Array Nat\n  | 0 => a\n  | .succ k => fill (Array.push a k) k\nmutual\ninductive Tree where\n  | leaf (n : Nat)\n  | node (ts : Forest)\ninductive Forest where\n  | nil\n  | cons (t : Tree) (ts : Forest)\nend\nmutual\ndef sizeT (t : Tree) : Nat := match t with\n  | .leaf _ => 1\n  | .node ts => sizeF ts\ndef sizeF (f : Forest) : Nat := match f with\n  | .nil => 0\n  | .cons t ts => sizeT t + sizeF ts\nend\ndef main : IO Unit := do\n  IO.println (Nat.toString (fib 20));\n  IO.println (Nat.toString (sum (countdown 100 .nil)));\n  let a := fill Array.empty 1000;\n  IO.println (Nat.toString (Array.size a + Array.getD a 10 0));\n  let m := StrMap.insert (StrMap.insert StrMap.empty (Str.ofString \"a\") 1) (Str.ofString \"b\") 2;\n  IO.println (Nat.toString (StrMap.findD m (Str.ofString \"b\") 0));\n  IO.println (if Nat.lt 3 4 then String.append \"yes, \" \"ünïcode\" else \"no\");\n  IO.println (Nat.toString (sizeT (Tree.node (Forest.cons (Tree.leaf 1) (Forest.cons (Tree.leaf 2) Forest.nil)))));\n  IO.println (Nat.toString (String.length \"hello\"))\n"

/-- A program for the reference counting mode: a list a million long (built, walked by
`ind`, freed without deep recursion), a hypothesis never read, a shared array updated
(copied), closures applied twice, a parameter never used, a key inserted twice. -/
def selfhostProgram2 : String :=
  "import Prelude\ndef len : List Nat → Nat\n  | .nil => 0\n  | .cons _ t => len t + 1\npartial def build (n : Nat) (acc : List Nat) : List Nat := match n with\n  | 0 => acc\n  | .succ k => build k (List.cons k acc)\ndef firstOr (d : Nat) : List Nat → Nat\n  | .nil => d\n  | .cons x _ => x\ndef twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)\ndef adder (n : Nat) : Nat → Nat := fun x => x + n\ndef pick (b : Bool) (x y : List Nat) : List Nat := if b then x else y\ndef ignore (x : List Nat) (y : Nat) : Nat := y\ndef main : IO Unit := do\n  let big := build 1000000 .nil;\n  IO.println (Nat.toString (len big));\n  IO.println (Nat.toString (firstOr 7 big));\n  let a := Array.push (Array.push Array.empty 1) 2;\n  let b := Array.set a 0 5;\n  IO.println (Nat.toString (Array.getD a 0 0 + Array.getD b 0 0));\n  let add3 := adder 3;\n  IO.println (Nat.toString (twice add3 1 + twice add3 2));\n  IO.println (Nat.toString (len (pick .false big (List.cons 1 .nil)) + ignore big 4));\n  let m := StrMap.insert (StrMap.insert StrMap.empty (Str.ofString \"k\") 1) (Str.ofString \"k\") 2;\n  IO.println (Nat.toString (StrMap.findD m (Str.ofString \"k\") 0 + StrMap.size m))\n"

/-- A program for reuse under reference counting: a list mapped while shared (copied)
and unique (its cells reused), a tree rebuilt twice, a pair taken apart and rebuilt;
prints `1000000 9900 18 4`. -/
def selfhostProgram3 : String :=
  "import Prelude\ndef mapL (f : Nat → Nat) : List Nat → List Nat\n  | .nil => .nil\n  | .cons x xs => .cons (f x) (mapL f xs)\ndef sumL : List Nat → Nat\n  | .nil => 0\n  | .cons x xs => x + sumL xs\npartial def build (n : Nat) (acc : List Nat) : List Nat := match n with\n  | 0 => acc\n  | .succ k => build k (List.cons k acc)\ninductive T where\n  | leaf (n : Nat)\n  | node (l : T) (r : T)\ndef incT : T → T\n  | .leaf n => .leaf (n + 1)\n  | .node l r => .node (incT l) (incT r)\ndef sumT : T → Nat\n  | .leaf n => n\n  | .node l r => sumT l + sumT r\ndef t0 : T := T.node (T.node (T.leaf 1) (T.leaf 2)) (T.leaf 3)\ndef swapP (p : Prod Nat (List Nat)) : Prod (List Nat) Nat := .mk p.snd p.fst\ndef main : IO Unit := do\n  let xs := build 1000 .nil;\n  let ys := mapL (fun x => x + 1) xs;\n  IO.println (Nat.toString (sumL xs + sumL ys));\n  IO.println (Nat.toString (sumL (mapL (fun x => x * 2) (build 100 .nil))));\n  IO.println (Nat.toString (sumT (incT (incT t0)) + sumT t0));\n  IO.println (Nat.toString (Prod.snd (swapP (.mk 4 xs))))\n"

/-- A program for the demand analysis of `let`s under reference counting: a `let` used
in one branch only (moved into it), a dead one (dropped), one under a `λ` (suspended),
one used on every path (strict); prints `110 0 7 23 13`. -/
def selfhostProgram4 : String :=
  "import Prelude\ndef sumTo : Nat → Nat\n  | .zero => 0\n  | .succ k => sumTo k + k + 1\ndef onlyIf (b : Bool) (n : Nat) : Nat :=\n  let s := sumTo n;\n  match b with\n  | .true => s + s\n  | .false => 0\ndef dead (n : Nat) : Nat :=\n  let unused := sumTo n;\n  n\ndef later (n : Nat) : Nat → Nat :=\n  let s := sumTo n;\n  fun x => x + s\ndef both (b : Bool) (n : Nat) : Nat :=\n  let s := sumTo n;\n  match b with\n  | .true => s\n  | .false => s + 1\ndef main : IO Unit := do\n  IO.println (Nat.toString (onlyIf .true 10));\n  IO.println (Nat.toString (onlyIf .false 10));\n  IO.println (Nat.toString (dead 7));\n  let f := later 4;\n  IO.println (Nat.toString (f 1 + f 2));\n  IO.println (Nat.toString (both .false 3 + both .true 3))\n"

/-- A program for unmemoised hypotheses under reference counting: a function-valued
recursion (`nth`) partially applied and called 3000 times, a hypothesis read once
(`lenL`), one read twice (`twice`: memoised, else exponential), a tree with two
hypotheses read once each; prints `4498500 3000 1099511627775 65536`. -/
def selfhostProgram5 : String :=
  "import Prelude\npartial def build (n : Nat) (acc : List Nat) : List Nat := match n with\n  | 0 => acc\n  | .succ k => build k (List.cons k acc)\ndef nth : List Nat → Nat → Nat\n  | .nil, _ => 0\n  | .cons x xs, i => match i with\n    | .zero => x\n    | .succ j => nth xs j\ndef sumF (f : Nat → Nat) : Nat → Nat\n  | .zero => 0\n  | .succ k => f k + sumF f k\ndef lenL : List Nat → Nat\n  | .nil => 0\n  | .cons _ t => lenL t + 1\ndef twice : List Nat → Nat\n  | .nil => 0\n  | .cons _ t => twice t + twice t + 1\ninductive T where\n  | leaf (n : Nat)\n  | node (l : T) (r : T)\ndef mk : Nat → T\n  | .zero => T.leaf 1\n  | .succ k => T.node (mk k) (mk k)\ndef sumT : T → Nat\n  | .leaf n => n\n  | .node l r => sumT l + sumT r\ndef main : IO Unit := do\n  let xs := build 3000 .nil;\n  let f := nth xs;\n  IO.println (Nat.toString (sumF f 3000));\n  IO.println (Nat.toString (lenL xs));\n  IO.println (Nat.toString (twice (build 40 .nil)));\n  IO.println (Nat.toString (sumT (mk 16)))\n"

/-- Compile a program with the self-hosted compiler, then the C it prints with the
self-hosted runtime (`selfhost/rt.c`, with the garbage collector given by the
toolchain's `gcCflags`/`gcLdflags`), run it, and compare its output. -/
def selfhostCompileRun (file expected : String) (flags : Array String := #[]) (progArgs : Array String := #[])
    (opt : String := "-O2") (smallStack : Bool := false) : IO Unit := do
  let tc ← toolchain
  if tc.gcCflags.isEmpty then skip "no garbage collector, --gc-cflags"; return
  match ← selfhostCompiler with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then skip "no toolchain" else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "input.wiz") file
    let out ← IO.Process.output { cmd := "timeout", args := #["300", exe.toString] ++ flags, cwd := dir }
    unless out.exitCode == 0 do throw (IO.userError s!"the compiler failed ({out.exitCode}): {out.stderr}")
    IO.FS.writeFile (dir / "out.c") out.stdout
    let rt := (← IO.currentDir) / "selfhost"
    let args := #[opt, "-w", s!"-I{rt}"] ++ tc.gcCflags.toArray ++ #["out.c", "-o", "prog"] ++ tc.gcLdflags.toArray
    let cc ← IO.Process.output { cmd := tc.cc, args, cwd := dir }
    unless cc.exitCode == 0 do throw (IO.userError s!"cc failed: {cc.stderr.take 2000}")
    -- (a small stack: 1 MB, and the runtime told not to raise it)
    let run ← if smallStack then
        let env : Array (String × Option String) := #[("WIZ_STACK_SET", some "1")]
        IO.Process.output { cmd := "sh", args := #["-c", "ulimit -s 1024; exec timeout 60 ./prog \"$@\"", "sh"] ++ progArgs, cwd := dir, env }
      else IO.Process.output { cmd := "timeout", args := #["60", (dir / "prog").toString] ++ progArgs, cwd := dir }
    unless run.exitCode == 0 do throw (IO.userError s!"the program failed ({run.exitCode}): {run.stderr}")
    checkEq expected run.stdout

/-- The self-hosted compiler rejects a program: exit code 1, the errors on standard
error, and no C (15g). -/
def selfhostCompileFails (file : String) (errors : String) : IO Unit := do
  match ← selfhostCompiler with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then skip "no toolchain" else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "input.wiz") file
    let out ← IO.Process.output { cmd := "timeout", args := #["300", exe.toString], cwd := dir }
    checkEq (1 : UInt32) out.exitCode
    checkEq errors out.stderr
    checkEq "" out.stdout

/-- (21l) A program with foreign functions gives the same output compiled by the Lean
compiler and by the self-hosted one (with the collector unless `gc := false`, and with
reference counting, which also checks that every object was freed). -/
def ffiAgrees (src expected : String) (gc : Bool := true) : IO Unit := do
  ioRun src expected
  if gc then selfhostCompileRun src expected
  selfhostCompileRun src expected (flags := #["--rc"])

/-- (21l) Foreign functions: headers, prototypes, numbers, strings, `Bool`, `Unit`, `IO`. -/
def ffiProgram1 : String :=
  "import IO\nextern \"strlen\" (header := \"string.h\") strlen : String → Nat\n" ++
  "extern \"strerror\" (header := \"string.h\") strerror : Nat → String\n" ++
  "extern \"isdigit\" (header := \"ctype.h\") isdigit : Nat → Bool\n" ++
  "extern \"puts\" (header := \"stdio.h\") cputs : String → IO Unit\n" ++
  "extern \"labs\" (header := \"stdlib.h\") labs : Nat → Nat\n" ++
  "def show (n : Nat) : IO Unit := IO.println (Nat.toString n)\n" ++
  "def pick (b : Bool) (y n : String) : String := match b with\n  | .true => y\n  | .false => n\n" ++
  "def main : IO Unit := do\n  show (strlen \"hello, ünïcode\");\n  IO.println (strerror 0);\n" ++
  "  IO.println (pick (isdigit 55) \"digit\" \"not\");\n  IO.println (pick (isdigit 65) \"digit\" \"not\");\n" ++
  "  cputs \"from C\";\n  show (labs 42);\n" ++
  "  show (UInt64.toNat (UInt64.mul (UInt64.ofNat 1000000) (UInt64.ofNat 1000000)));\n" ++
  "  let big := UInt64.sub (UInt64.ofNat 0) (UInt64.ofNat 1);\n" ++
  "  IO.println (pick (UInt64.lt (UInt64.ofNat 5) big) \"wraps\" \"no\");\n" ++
  "  IO.println (pick (UInt64.eq (UInt64.add big (UInt64.ofNat 1)) (UInt64.ofNat 0)) \"zero\" \"no\");\n" ++
  "  IO.println (Float64.toString (Float64.div (Float64.ofNat 1) (Float64.ofNat 4)));\n" ++
  "  IO.println (Float64.toString (Float64.sub (Float64.ofNat 1) (Float64.ofNat 3)))\n"

def ffiExpected1 : String :=
  "16\nSuccess\ndigit\nnot\nfrom C\n42\n1000000000000\nwraps\nzero\n0.25\n-2\n"

/-- (21l) A foreign pointer type with a finalizer: `fclose` runs when the last reference
to the `FILE` goes (so the file is complete when it is read back). -/
def ffiProgramFin (flush : Bool) : String :=
  let file := s!"/tmp/wiz_ffi_fin_{flush}.txt"
  "import IO\nforeign_type FILE (finalizer := \"fclose\")\n" ++
  "extern \"fopen\" (header := \"stdio.h\") fopen : String → String → IO FILE\n" ++
  "extern \"fputs\" (header := \"stdio.h\") fputs : String → FILE → IO Nat\n" ++
  "extern \"fflush\" (header := \"stdio.h\") fflush : FILE → IO Nat\n" ++
  "def write (f : FILE) : Nat → IO Unit\n  | .zero => IO.pure ()\n  | .succ k => do\n    n ← fputs \"line\\n\" f;\n    write f k\n" ++
  "def main : IO Unit := do\n  f ← fopen \"" ++ file ++ "\" \"w\";\n  write f 3;\n" ++
  (if flush then "  n ← fflush f;\n" else "") ++
  "  s ← IO.readFile \"" ++ file ++ "\";\n  IO.print s\n"

-- the self-hosted checker's output for a file
def selfhostOutput (file : String) : IO (Option String) := do
  match ← selfhostChecker with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then
      skip "no toolchain"
      pure none
    else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "input.wiz") file
    let out ← IO.Process.output { cmd := "timeout", args := #["900", exe.toString], cwd := dir }
    unless out.exitCode == 0 do throw (IO.userError s!"the checker failed ({out.exitCode}): {out.stderr}")
    pure (some out.stdout)

/-- (D1) The compiled program `main` of `src` doesn't finish within `secs` seconds
(memory capped: a loop in the kernel allocates). -/
def ioDiverges (src : String) (secs : Nat := 5) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else none
  let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  match Build.irProgram s "main" with
  | .error e => throw (IO.userError e)
  | .ok (decls, _) =>
    let dir ← IO.FS.createTempDir
    let exe := dir / "wiz_main"
    match ← Build.compileC (← toolchain) (C.program decls true (Build.extraC s)) exe with
    | .error e =>
      if (e.splitOn "gmp.h").length > 1 then skip "no toolchain" else throw (IO.userError e)
    | .ok () =>
      let out ← IO.Process.output { cmd := "sh", args := #["-c",
        s!"ulimit -v 8000000; exec timeout {secs} \"$0\"", exe.toString] }
      unless out.exitCode == 124 do
        throw (IO.userError s!"expected a timeout, got exit code {out.exitCode}: {(out.stdout ++ out.stderr).take 1500}")

/-- (stages 21i–j) Differential: each declaration after `header` is accepted (`true`) or
rejected by the Lean frontend and by the self-hosted one alike, as `expected` says. -/
def selfhostAgrees (header : String) (decls : List (String × Bool)) : IO Unit := do
  let loader ← preludeLoader
  for (d, ok) in decls do
    let src := "import Prelude\n" ++ header ++ d
    let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
    let leanOk := (s.messages.filter (·.severity == .error)).isEmpty
    unless leanOk == ok do throw (IO.userError s!"the Lean frontend {if leanOk then "accepts" else "rejects"}:\n{d}")
    let some out ← selfhostOutput src | return
    let errs := (out.splitOn "\n").filter (·.startsWith "error")
    unless errs.isEmpty == ok do
      throw (IO.userError s!"the self-hosted frontend {if errs.isEmpty then "accepts" else "rejects"}:\n{d}\n{out}")

/-- (stage 21m) Pinned differences between the frontends: each declaration after `header`
is accepted or rejected by the Lean frontend (`leanOk`) and by the self-hosted one
(`selfOk`) as given, which for the pinned ones differ. -/
def selfhostVerdicts (header : String) (decls : List (String × Bool × Bool)) : IO Unit := do
  let loader ← preludeLoader
  for (d, ok, selfOk) in decls do
    let src := "import Prelude\n" ++ header ++ d
    let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
    let leanOk := (s.messages.filter (·.severity == .error)).isEmpty
    unless leanOk == ok do throw (IO.userError s!"the Lean frontend {if leanOk then "accepts" else "rejects"}:\n{d}")
    let some out ← selfhostOutput src | return
    let errs := (out.splitOn "\n").filter (·.startsWith "error")
    unless errs.isEmpty == selfOk do
      throw (IO.userError s!"the self-hosted frontend {if errs.isEmpty then "accepts" else "rejects"}:\n{d}\n{out}")

/-- (stage 21m) Written quantities (finding K10 of audit 2): the declarations both frontends
accept or reject alike. -/
def quantityHeader : String :=
  "def lin (1 x : Nat) (f : (1 y : Nat) → Nat) : Nat := f x\naxiom lin1 : (1 x : Nat) → Nat\n" ++
  "structure Pt (w : Nat) where\n  x : Nat\n"

def quantityDecls : List (String × Bool) := [
  ("def ok1 (1 x : Nat) : Nat := x\n", true),
  ("def impOk {n : Nat} (x : Nat) : Nat := x\n", true),
  ("def useLin (1 z : Nat) : Nat := lin z (fun y => y)\n", true),
  ("def l1 (x : Nat) : Nat := let 1 y := x; y\n", true),
  ("def fl : (1 y : Nat) → Nat := fun (1 y : Nat) => y\ndef flU : (1 y : Nat) → Nat := fun y => y\n", true),
  ("def useAx (1 y : Nat) : Nat := lin1 y\n", true),
  ("def ptx {w : Nat} (p : Pt w) : Nat := p.x\n", true),
  ("def T1 : Type := (1 x : Nat) → Nat\n", true),
  ("def len {0 A : Type} : List A → Nat\n  | .nil => 0\n  | .cons _ t => Nat.succ (len t)\n", true),
  ("def dup (ω x : Nat) : Nat := Nat.add x x\ndef ax2 (0 A : Type) (1 a : A) : A := a\n", true),
  ("def twice (1 x : Nat) (f : Nat → Nat → Nat) : Nat := f x x\n", false),
  ("def drop (1 x : Nat) : Nat := Nat.zero\n", false),
  ("def m2 (1 x : Nat) : Nat := match x with\n  | .zero => 0\n  | .succ k => k\n", false),
  ("def imp {n : Nat} (x : Nat) : Nat := n\n", false),
  ("def er (0 x : Nat) : Nat := x\n", false),
  ("def bad2 (2 x : Nat) : Nat := x\n", false),
  ("def l1bad (x : Nat) : Nat := let 1 y := x; Nat.add y y\n", false),
  ("def flbad2 : (y : Nat) → Nat := fun (1 y : Nat) => y\n", false),
  ("def useAx2 (1 y : Nat) : Nat := Nat.add (lin1 y) y\n", false),
  ("def mk {w : Nat} : Pt w := Pt.mk w\n", false),
  ("def toW (1 x : Nat) : Nat := Nat.succ x\n", false),
  ("def l0 (x : Nat) : Nat := let 0 y := x; y\n", false),
  ("def linTwice (1 z : Nat) : Nat := lin z (fun y => Nat.add y y)\n", false)]

/-- (stage 21m) The pinned differences, `(declaration, Lean accepts, self-hosted accepts)`
(docs/CoreSpec.md §15): a branch of a `match` is an argument of `T.casesOn` for the Lean
elaborator, so a linear variable used in two branches is used ω times, while the
self-hosted frontend compiles the match to the kernel's case, whose branches are
alternatives (each uses it once; sound); and the self-hosted kernel's descriptions have
no quantities, so a constructor field written with one is an error there. -/
def quantityDiffs : List (String × Bool × Bool) := [
  ("def m1 (1 x : Nat) (b : Bool) : Nat := match b with\n  | .true => x\n  | .false => x\n", false, true),
  ("structure P1 where\n  1 a : Nat\n", true, false),
  ("inductive V0 where\n  | mk (0 n : Nat)\n", true, false)]

/-- (stage 21m) A program with quantities, compiled by the self-hosted compiler: the
0-quantity arguments are erased, a `let 1` runs. -/
def quantityProgram : String :=
  "import Prelude\ninductive Box (w : Nat) where\n  | mk (n : Nat)\nstructure Pt (w : Nat) where\n  x : Nat\n  y : Nat\n" ++
  "def get {w : Nat} : Box w → Nat\n  | .mk n => n\ndef sum {w : Nat} (p : Pt w) : Nat := p.x + p.y\n" ++
  "def b : Box 8 := .mk 3\ndef p : Pt 8 := .mk 1 2\n" ++
  "def lin (1 x : Nat) (f : (1 y : Nat) → Nat) : Nat := f x\n" ++
  "def len {A : Type} : List A → Nat\n  | .nil => 0\n  | .cons _ t => Nat.succ (len t)\n" ++
  "def id1 (1 x : Nat) : Nat := let 1 y := x; y\ndef main : IO Unit := do\n" ++
  "  IO.println (Nat.toString (get b + sum p));\n  IO.println (Nat.toString (Nat.add 1 (lin 4 (fun y => y))));\n" ++
  "  IO.println (Nat.toString (Nat.add (id1 7) (len (List.cons 1 (List.cons 2 .nil)))))\n"

/-- (stage 21o) The files of `linkFiles`-style programs compiled by the self-hosted
compiler: `main.wiz` is its input, the `// wiz-link-c:`/`// wiz-link-lib:` lines of the C
it prints name the C files (relative to the input's directory) and libraries that `cc`
compiles and links with it. Compares the output, or (`fails`) the exit code 3 of a
runtime error and a fragment of its message. -/
def selfhostLinkRun (files : List (String × String)) (expected : String) (flags : Array String := #[])
    (fails : Option String := none) : IO Unit := do
  let tc ← toolchain
  if tc.gcCflags.isEmpty then IO.println "    (skipped: no garbage collector, --gc-cflags)"; return
  match ← selfhostCompiler with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    for (p, text) in files do
      let f := dir / p
      if let some d := f.parent then IO.FS.createDirAll d
      IO.FS.writeFile f text
    IO.FS.writeFile (dir / "input.wiz") (← IO.FS.readFile (dir / "main.wiz"))
    let out ← IO.Process.output { cmd := "timeout", args := #["300", exe.toString] ++ flags, cwd := dir }
    unless out.exitCode == 0 do throw (IO.userError s!"the compiler failed ({out.exitCode}): {out.stderr}")
    IO.FS.writeFile (dir / "out.c") out.stdout
    let lines := out.stdout.splitOn "\n"
    let cs := lines.filterMap fun l => (l.dropPrefix? "// wiz-link-c: ").map (·.toString)
    let libs := lines.filterMap fun l => (l.dropPrefix? "// wiz-link-lib: ").map (s!"-l{·}")
    let rt := (← IO.currentDir) / "selfhost"
    let args := #["-O2", "-w", s!"-I{rt}"] ++ tc.gcCflags.toArray ++ #["out.c"] ++ cs.toArray ++ #["-o", "prog"] ++
      tc.gcLdflags.toArray ++ libs.toArray
    let cc ← IO.Process.output { cmd := tc.cc, args, cwd := dir }
    unless cc.exitCode == 0 do throw (IO.userError s!"cc failed: {cc.stderr.take 2000}")
    let run ← IO.Process.output { cmd := "timeout", args := #["60", (dir / "prog").toString], cwd := dir }
    match fails with
    | none =>
      unless run.exitCode == 0 do throw (IO.userError s!"the program failed ({run.exitCode}): {run.stderr}")
      checkEq expected run.stdout
    | some frag =>
      unless run.exitCode == 3 && (run.stderr.splitOn frag).length > 1 do
        throw (IO.userError s!"expected the runtime error '{frag}', got exit {run.exitCode}: {run.stderr}")
      checkEq expected run.stdout

/-- (stage 21o) C calls Wiz: exports (numbers, strings both ways, `Bool`, `IO`) called from a
`link_c` file, which the program calls through externs, and a `link_lib` library. -/
def exportFiles : List (String × String) :=
  [("main.wiz", "import IO\nlink_c \"c/cb.c\"\nlink_lib \"m\"\n" ++
      "def double (n : Nat) : Nat := n + n\ndef greet (who : String) : String := String.append \"hello, \" who\n" ++
      "def isBig (n : Nat) : Bool := Nat.lt 10 n\ndef tick (n : Nat) : IO Nat := do\n  IO.println \"tick\";\n  IO.pure (n + 1)\n" ++
      "export \"ex_double\" double\nexport \"ex_greet\" greet : String → String\nexport \"ex_is_big\" isBig\nexport \"ex_tick\" tick\n" ++
      "extern \"call_double\" callDouble : Nat → Nat\nextern \"greet_len\" greetLen : String → Nat\n" ++
      "extern \"count_big\" countBig : Nat → Nat\nextern \"run_tick\" runTick : Nat → IO Nat\nextern \"root_of\" rootOf : Nat → Nat\n" ++
      "def show (n : Nat) : IO Unit := IO.println (Nat.toString n)\n" ++
      "def main : IO Unit := do\n  show (callDouble 20);\n  show (greetLen \"you\");\n  show (countBig 20);\n" ++
      "  r ← runTick 41;\n  show r;\n  show (rootOf 1764)\n"),
   ("c/cb.c", "#include <stdint.h>\n#include <stdlib.h>\n#include <string.h>\n#include <math.h>\n" ++
      "uint64_t ex_double(uint64_t);\nchar *ex_greet(const char *);\nint ex_is_big(uint64_t);\nuint64_t ex_tick(uint64_t);\n" ++
      "uint64_t call_double(uint64_t n) { return ex_double(n) + 1; }\n" ++
      "uint64_t greet_len(const char *s) { char *g = ex_greet(s); uint64_t n = strlen(g); free(g); return n; }\n" ++
      "uint64_t count_big(uint64_t n) { uint64_t k = 0; for (uint64_t i = 0; i < n; i++) k += ex_is_big(i) != 0; return k; }\n" ++
      "uint64_t run_tick(uint64_t n) { return ex_tick(ex_tick(n)); }\n" ++
      "uint64_t root_of(uint64_t n) { volatile double d = (double)n; return (uint64_t)sqrt(d); }\n")]

def exportExpected : String := "41\n10\n9\ntick\ntick\n43\n42\n"

/-- (stage 21o) The declarations both frontends reject alike (`export`, `link_lib`). -/
def exportHeader : String :=
  "def f (n : Nat) : Nat := n\ndef g {A : Type} (a : A) : A := a\ndef h (f : Nat → Nat) : Nat := f 1\ndef k (u : Unit) : Nat := 1\n"

def exportDecls : List (String × Bool) := [
  ("export \"ok_f\" f\nexport \"ok_f2\" f : Nat → Nat\n", true),
  ("export \"1x\" f\n", false), ("export \"ok_f\" nope\n", false), ("export \"ok_f\" f : Nat → Bool\n", false),
  ("export \"ok_g\" g\n", false), ("export \"ok_h\" h\n", false), ("export \"ok_k\" k\n", false),
  ("export \"ok_f\" f\nexport \"ok_f\" f\n", false), ("link_lib \"-lm\"\n", false)]

/-- (stage 21n) `private` everywhere the Lean frontend takes it: with one module, the
names are used as usual (privacy is per module). -/
def privateDecls : List (String × Bool) := [
  ("private def secret : Nat := 42\ndef useIt : Nat := secret\nprivate axiom ax : Nat\ndef useAx : Nat := ax\n", true),
  ("inductive Tok where\n  | num (n : Nat)\n  | private hidden (n : Nat)\ndef t : Tok := Tok.hidden 3\n" ++
     "def val : Tok → Nat\n  | .num n => n\n  | .hidden n => n\n", true),
  ("structure Acct where\n  owner : Nat\n  private bal : Nat\ndef b (a : Acct) : Nat := a.bal\n" ++
     "structure Shr (A : Type) where\n  private mk ::\n  val : A\ndef s : Shr Nat := Shr.mk 3\n", true),
  ("private inductive P where\n  | a\ndef pa : P := P.a\nprivate structure S where\n  x : Nat\ndef sx (s : S) : Nat := s.x\n", true),
  ("private mutual\ndef ev : Nat → Bool\n  | .zero => .true\n  | .succ n => od n\ndef od : Nat → Bool\n" ++
     "  | .zero => .false\n  | .succ n => ev n\nend\ndef e2 : Bool := ev 2\n", true),
  ("mutual\nprivate def ev : Nat → Bool\n  | .zero => .true\n  | .succ n => od n\nprivate def od : Nat → Bool\n" ++
     "  | .zero => .false\n  | .succ n => ev n\nend\n", false),
  ("private def dup : Nat := 1\ndef dup : Nat := 2\n", false)]

/-- (stage 21i) Phantom parameters, for both frontends. -/
def phantomHeader : String :=
  "inductive UIntN (w : Nat) where\n  | mk (toNat : Nat)\ninductive Proxy (A : Type) where\n  | mk\n" ++
  "structure S (w : Nat) where\n  x : Nat\ninductive N (w : Nat) where\n  | z\n  | s (n : N w)\n" ++
  "def width (w : Nat) (a : UIntN w) : Nat := w\ndef u8 : UIntN 8 := .mk 3\n"

/-- Finding Y4 (audit 2): the probe (`def T` twice, with `Box T` in between), and the
other ways a command could declare a name again. -/
def dupNames : String :=
  "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive Empty where\ninductive Box (A : Type) where\n  | mk (a : A)\n" ++
  "def unbox {A : Type} (x : Box A) : A := match x with\n  | .mk a => a\n" ++
  "def T : Type := Nat\ndef a : Box T := Box.mk Nat.zero\ndef T : Type := Empty\ndef c : Box Empty := a\n" ++
  "inductive Nat where\n  | zero\ninductive Two where\n  | a\n  | a\ndef Box.mk : Nat := Nat.zero\n" ++
  "inductive Fresh where\n  | mk\ndef Fresh.mk : Nat := Nat.zero\naxiom T : Type\naxiom Ax : Type\ndef Ax : Type := Nat\n" ++
  "partial def loop (n : Nat) : Nat := loop n\npartial def loop (n : Nat) : Nat := loop n\ndef loop : Nat := Nat.zero\n" ++
  "structure P where\n  mk : Nat\nstructure Q where\n  fst : Nat\ndef Q.fst : Nat := Nat.zero\n" ++
  "mutual\ndef ev : Nat → Nat\n  | .zero => .zero\n  | .succ n => ev n\ndef ev : Nat → Nat\n  | .zero => .zero\n  | .succ n => ev n\nend\n" ++
  "def fine : Nat := loop Nat.zero\n"

def dupNamesExpected : String :=
  "Nat : U0\nEmpty : U0\nBox : (x0 : U0) → U0\nunbox : (x0 :0 U0) → (x1 : (Box x0)) → x0\nT : U0\na : (Box T)\n" ++
  "error: 'T' has already been declared\nerror: type mismatch: expected (Box Empty), got (Box T)\n" ++
  "error: 'Nat' has already been declared\nerror: 'Two.a' has already been declared\nerror: 'Box.mk' has already been declared\n" ++
  "Fresh : U0\nerror: 'Fresh.mk' has already been declared\nerror: 'T' has already been declared\nAx : U0\n" ++
  "error: 'Ax' has already been declared\nloop : (x0 : Nat) → Nat\nerror: 'loop' has already been declared\n" ++
  "error: 'loop' has already been declared\nerror: 'P.mk' has already been declared\nQ : U0\nQ.fst : (x0 : Q) → Nat\n" ++
  "error: 'Q.fst' has already been declared\nerror: 'ev' has already been declared\nfine : Nat\n"

def selfHostGroup : Group where
  name := "selfhost"
  exercise := "Stages 12b–14q"
  cases := [
    { name := "the lexer in Wiz agrees with the Lean lexer", run := fun _ => do
        let lexSrc ← IO.FS.readFile "selfhost/Lex.wiz"
        let input := "def f (x : Nat) : Nat := x + 1 -- a comment\n/- a /- nested -/ block -/ #eval f 41\n" ++
          "inductive T where | a | b (t : T)\ndef s : String := \"hi\\n\" -- strings\ndef α₁ : List.cons → Nat.add := λ x => x.1"
        let toks := Builtin.tables.tokens
        let expected := leanTokens toks input
        let table := toks.toList.foldr (fun t acc => s!"(.cons {wizLit t} {acc})") ".nil"
        let prog := lexSrc ++ s!"\ndef main : IO Unit := printAll (List.reverseL (tokenize {table} {wizLit input}) .nil)\n"
        let prog := prog.replace "def printAll" "def List.reverseL : List String → List String → List String\n  | .nil, acc => acc\n  | .cons x xs, acc => List.reverseL xs (.cons x acc)\ndef printAll"
        ioRun prog ("\n".intercalate expected ++ "\n") },
    { name := "the parser in Wiz agrees with the Lean parser", run := fun _ => do
        let lexSrc ← IO.FS.readFile "selfhost/Lex.wiz"
        let parseSrc ← IO.FS.readFile "selfhost/Parse.wiz"
        let t := Builtin.tables
        let cases : List (Name × String) := [
          ("term", "f x y"), ("term", "fun (x : Nat) => x"), ("term", "(x : A) → B x"),
          ("term", "(a, b).1"), ("term", "match n with\n  | .zero => a\n  | .succ m => b"),
          ("term", "let x := 1; x"), ("term", "f (g x"), ("term", "Type 1"),
          ("command", "def f (x : Nat) : Nat := x"),
          ("command", "inductive T where\n  | a\n  | b (t : T)"),
          ("command", "#eval f 41"), ("command", "def f : Nat → Nat\n  | .zero => 0\n  | .succ n => n")]
        let expected := cases.map fun (c, i) => leanParse t c i
        let calls := cases.map fun (c, i) => s!"(parse cats tokens {wizLit c} {wizLit i})"
        let prog := lexSrc ++ "\n" ++ parseSrc ++ "\n" ++ wizTables t ++
          s!"def tokens : List String := {wizList (t.tokens.toList.map wizLit)}\n" ++
          s!"def main : IO Unit := printAll {wizList calls}\n"
        ioRun prog ("\n".intercalate expected ++ "\n") },
    { name := "the type checker in Wiz", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let defs := "def idTy : Tm := .pi (.univ 0) (.pi (.var 0) (.var 1))\n" ++
          "def idTm : Tm := .ann (.lam (.lam (.var 0))) idTy\n" ++
          "def cnat : Tm := .pi (.univ 0) (.pi (.pi (.var 0) (.var 1)) (.pi (.var 1) (.var 2)))\n" ++
          "def two : Tm := .ann (.lam (.lam (.lam (.app (.var 1) (.app (.var 1) (.var 0)))))) cnat\n" ++
          "def add : Tm := .ann (.lam (.lam (.lam (.lam (.lam (.app (.app (.app (.var 4) (.var 2)) (.var 1)) " ++
          "(.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)))))))) (.pi cnat (.pi cnat cnat))\n" ++
          "def viaId : Tm := .ann (.lam (.lam (.app (.app idTm (.var 1)) (.var 0)))) idTy\n"
        let main := "def main : IO Unit := do\n  IO.println (typeOf idTm);\n  IO.println (typeOf viaId);\n" ++
          "  IO.println (typeOf (.app idTm cnat));\n  IO.println (typeOf (.app (.app add two) two));\n" ++
          "  IO.println (normalize (.app (.app add two) two));\n  IO.println (typeOf (.app (.univ 0) (.univ 0)));\n" ++
          -- a variable out of scope is an error (it was `Sort 0`, as a type and as a value: `Prop : Prop`)
          "  IO.println (typeOf (.var 0));\n  IO.println (typeOf (.ann (.lam (.var 3)) (.pi (.unit 0) .prop)))\n"
        ioRun (kernel ++ "\n" ++ defs ++ main) ("(x0 : U0) → (x1 : x0) → x0\n(x0 : U0) → (x1 : x0) → x0\n" ++
          "error: type mismatch: expected U0, got U1\n(x0 : U0) → (x1 : (x1 : x0) → x0) → (x2 : x0) → x0\n" ++
          "λx0. λx1. λx2. (x1 (x1 (x1 (x1 x2))))\nerror: not a function: its type is U1\n" ++
          "error: internal error: a variable out of scope\nerror: internal error: a variable out of scope\n") },
    -- W1 (`wiz-notes/kernel-lint.md`): the structural fast path (`valSame`) compared two
    -- constants by name, without their universe levels, so two stuck cases whose
    -- environments held `d.{0}` and `d.{1}` were convertible: a closed term of type `False`
    { name := "W1: a constant at two universe levels is not the same value (the fast path for stuck cases)", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let probe :=
          "def dVal : Tm := .pi (.sortL (.lparam \"u\")) (.pi (.var 0) (.pi (.var 1) (.pi (.pi (.var 2) .prop)\n" ++
          "  (.pi (.app (.var 0) (.var 2)) (.app (.var 1) (.var 2))))))\n" ++
          "def dAt (l : Lvl) : Tm := .const \"d\" (.cons \"u\" .nil) (.cons l .nil) dVal .prop\n" ++
          "def d0 : Tm := dAt (.lnum 0)\n" ++
          "def d1 : Tm := dAt (.lnum 1)\n" ++
          "def d0Proof : Tm := .ann (.lam (.lam (.lam (.lam (.lam (.var 0)))))) d0\n" ++
          "def fTy : Tm := .pi .prop (.pi (.enum 1) .prop)\n" ++
          "def fVal : Tm := .lam (.lam (.ecase .prop (.var 0) (.tcons (.var 1) .tnil)))\n" ++
          "def fC : Tm := .const \"F\" .nil .nil fVal fTy\n" ++
          "def fAt (a x : Tm) : Tm := .app (.app fC a) x\n" ++
          "def h (a b : Tm) : Tm := .ann (.lam (.lam (.var 0))) (.pi (.enum 1) (.pi (fAt a (.var 0)) (fAt b (.var 1))))\n" ++
          "def isFirst : Tm := .ann (.lam (.ecase .prop (.var 0) (.tcons .ptrue (.tcons .pfalse .tnil)))) (.pi (.enum 2) .prop)\n" ++
          "def refute (p : Tm) : Tm := .app (.app (.app (.app (.app p (.enum 2)) (.tag 2 0)) (.tag 2 1)) isFirst) .star\n" ++
          "def bad (a b : Tm) : Tm := .ann (refute (.app (.app (h a b) (.tag 1 0)) d0Proof)) .pfalse\n" ++
          "def verdict (r : TyRes) : String := match r with\n" ++
          "  | .ok _ _ => \"ok\"\n" ++
          "  | .err _ => \"error\"\n" ++
          "def typeOk (t : Tm) : String := verdict (infer empty t)\n" ++
          "def main : IO Unit := do\n" ++
          "  IO.println (String.append \"d's declaration, at every level: \" (verdict (checkDecl .prop (.some dVal))));\n" ++
          "  IO.println (String.append \"F's declaration: \" (verdict (checkDecl fTy (.some fVal))));\n" ++
          "  IO.println (String.append \"the proof of d.{0}: \" (typeOk d0Proof));\n" ++
          "  IO.println (String.append \"control, d.{0} used as d.{1} directly (want error): \" (typeOk (.ann d0Proof d1)));\n" ++
          "  IO.println (String.append \"control, F d.{0} x → F d.{0} x (want ok): \" (typeOk (h d0 d0)));\n" ++
          "  IO.println (String.append \"F d.{0} x → F d.{1} x (want error): \" (typeOk (h d0 d1)));\n" ++
          "  IO.println (String.append \"a closed term of type False (want error): \" (typeOf (bad d0 d1)))\n"
        ioRun (kernel ++ "\n" ++ probe) ("d's declaration, at every level: ok\nF's declaration: ok\nthe proof of d.{0}: ok\n" ++
          "control, d.{0} used as d.{1} directly (want error): error\ncontrol, F d.{0} x → F d.{0} x (want ok): ok\n" ++
          "F d.{0} x → F d.{1} x (want error): error\n" ++
          "a closed term of type False (want error): error: type mismatch: expected case(Prop, x0, d.{1}), got ((F d.{0}) x0)\n") },
    { name := "the frontend gives the types it builds their sorts (sortTy)", run := fun _ => do
        -- `(True → Unit) = ((True → True) → Unit)` built without sorts waits; with the
        -- sorts `sortTy` fills in, it computes to the domains' equivalence
        let src ← ["selfhost/Lex.wiz", "selfhost/Parse.wiz", "selfhost/Kernel.wiz", "selfhost/Frontend.wiz"].mapM (fun (f : String) => IO.FS.readFile f)
        let body := "\n".intercalate (src.map fun f => "\n".intercalate ((f.splitOn "\n").filter (!·.startsWith "import")))
        let prog := "import IO\nimport Std\n" ++ body ++ "\n" ++
          "def gTy (X : Tm) : Tm := .pi X (.unit 0)\n" ++
          "def eqn (s : Bool) : Tm := match s with\n" ++
          "  | .true => .eqTy (sortTy (gTy .ptrue)) (sortTy (gTy (.pi .ptrue .ptrue)))\n" ++
          "  | .false => .eqTy (gTy .ptrue) (gTy (.pi .ptrue .ptrue))\n" ++
          "def main : IO Unit := do\n  IO.println (normalize (eqn .false));\n  IO.println (normalize (eqn .true));\n" ++
          "  IO.println (typeOf (sortTy (gTy (.pi .ptrue .ptrue))))\n"
        ioRun prog ("EqTy((x0 : True) → Unit0, (x0 : (x0 : True) → True) → Unit0)\n" ++
          "(x0 :0 (x0 :0 (x0 :0 (x0 : True) → True) → True) × (x1 :0 True) → (x2 : True) → True) × " ++
          "(x1 :0 (x1 : True) → True) → True\nU0\n") },
    -- Y4: `Kernel.wiz` compares two constants by name, so a name has one declaration
    { name := "a name is declared once: a second declaration is an error (it proved an empty type inhabited)", run := fun _ =>
        selfhostCheckFile dupNames dupNamesExpected },
    { name := "text to checked term, all in Wiz", run := fun _ => do
        let src ← ["selfhost/Lex.wiz", "selfhost/Parse.wiz", "selfhost/Kernel.wiz", "selfhost/Frontend.wiz"].mapM (fun (f : String) => IO.FS.readFile f)
        let body := "\n".intercalate (src.map fun f => "\n".intercalate ((f.splitOn "\n").filter (!·.startsWith "import")))
        let t := Builtin.tables
        let bad := "(fun (x : Type) => x"
        let cases := ["(fun A x => x : (A : Type) → A → A)", "Type 2", "let T : Type 1 := Type; (fun x => x : T → T)",
          "fun x => x", "y", "(fun f x => f x : (Type → Type) → Type → Type)", bad]
        let calls := cases.map fun c => s!"(checkText cats tokens {wizLit c})"
        let prog := "import IO\nimport Std\n" ++ body ++ "\n" ++ wizTables t ++
          s!"def tokens : List String := {wizList (t.tokens.toList.map wizLit)}\n" ++
          s!"def main : IO Unit := printAll {wizList calls}\n"
        ioRun prog ("(x0 : U0) → (x1 : x0) → x0\nU3\n(x0 : U0) → U0\n" ++
          "error: cannot infer the type of a λ; add a type ascription\nscope error: unknown identifier y\n" ++
          "(x0 : (x0 : U0) → U0) → (x1 : U0) → U0\nparse " ++ leanParse t "term" bad ++ "\n") },
    { name := "a file of definitions, checked in Wiz", run := fun _ =>
        selfhostCheckFile ("def N : Type 1 := (A : Type) → (A → A) → A → A\ndef two : N := fun A s z => s (s z)\n" ++
          "def add (m n : N) : N := fun A s z => m A s (n A s z)\n#reduce add two two\n#check add two\n" ++
          "def bad : Type := Type\n#check bad\n")
          ("N : U1\ntwo : N\nadd : (x0 : N) → (x1 : N) → N\nλx0. λx1. λx2. (x1 (x1 (x1 (x1 x2))))\n" ++
          "(x0 : N) → N\n" ++
          "error: type mismatch: expected U0, got U1\nerror: unknown identifier bad\n") },
    { name := "inductive types, checked in Wiz", run := fun _ => do
        let file := "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef two : Nat := Nat.succ (Nat.succ Nat.zero)\n" ++
          "#check Nat.succ\n#reduce two\ninductive Pair where\n  | mk (a b : Nat)\n#check Pair.mk\n" ++
          "#reduce Pair.mk two Nat.zero\ninductive Bad where\n  | mk (f : Bad → Bad)\ndef bad : Nat := Nat.succ Type\n"
        selfhostCheckFile file ("Nat : U0\ntwo : Nat\n(x0 : Nat) → Nat\n" ++
          "con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\n" ++
          "Pair : U0\n(x0 : Nat) → (x1 : Nat) → Pair\n" ++
          "con((#0, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt)))))\n" ++
          s!"error: unknown identifier Bad\nerror: type mismatch: expected Nat, got U1\n") },
    { name := "pattern matching and structural recursion, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef two : Nat := Nat.succ (Nat.succ Nat.zero)\ndef add (m n : Nat) : Nat := match m with\n  | .zero => n\n  | .succ k => Nat.succ (add k n)\n#reduce add two two\ndef mul (m n : Nat) : Nat := match n with\n  | .zero => Nat.zero\n  | .succ k => add m (mul m k)\n#reduce mul two (Nat.succ (Nat.succ (Nat.succ Nat.zero)))\ndef Code (n : Nat) : Type := match n with\n  | .zero => Nat\n  | _ => Nat → Nat\n#check Code\ndef pred (n : Nat) : Nat := match n with\n  | .succ k => k\n  | x => x\n#reduce pred two\ndef bad (n : Nat) : Nat := match n with\n  | .succ k => k\ndef bad2 (m n : Nat) : Nat := match m with\n  | .zero => n\n  | .succ k => add k (bad2 n k)\n"
          "Nat : U0\ntwo : Nat\nadd : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nmul : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nCode : (x0 : Nat) → U0\n(x0 : Nat) → U0\npred : (x0 : Nat) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nerror: missing case zero\nerror: unknown identifier bad2\n" },
    { name := "parameterised inductive types, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef add (m n : Nat) : Nat := match m with\n  | .zero => n\n  | .succ k => Nat.succ (add k n)\ninductive List (A : Type) where\n  | nil\n  | cons (head : A) (tail : List A)\n#check List.cons\ndef one : Nat := Nat.succ Nat.zero\ndef xs : List Nat := List.cons one (List.cons Nat.zero List.nil)\ndef length (A : Type) (l : List A) : Nat := match l with\n  | .nil => Nat.zero\n  | .cons h t => Nat.succ (length A t)\n#reduce length Nat xs\ndef sum (l : List Nat) : Nat := match l with\n  | .nil => Nat.zero\n  | .cons h t => add h (sum t)\n#reduce sum xs\ndef append (A : Type) (l r : List A) : List A := match l with\n  | .nil => r\n  | .cons h t => List.cons h (append A t r)\n#reduce length Nat (append Nat xs xs)\ninductive Pair (A B : Type) where\n  | mk (a : A) (b : B)\ndef fst (A B : Type) (p : Pair A B) : A := match p with\n  | .mk a b => a\n#reduce fst Nat (List Nat) (Pair.mk one xs)\n"
          "Nat : U0\nadd : (x0 : Nat) → (x1 : Nat) → Nat\nList : (x0 : U0) → U0\n(x0 :0 U0) → (x1 : x0) → (x2 : (List x0)) → (List x0)\none : Nat\nxs : (List Nat)\nlength : (x0 : U0) → (x1 : (List x0)) → Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nsum : (x0 : (List Nat)) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nappend : (x0 : U0) → (x1 : (List x0)) → (x2 : (List x0)) → (List x0)\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nPair : (x0 : U0) → (x1 : U0) → U0\nfst : (x0 : U0) → (x1 : U0) → (x2 : ((Pair x0) x1)) → x0\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\n" },
    { name := "definitions by equations, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive List (A : Type) where\n  | nil\n  | cons (head : A) (tail : List A)\ndef len (A : Type) : List A → Nat\n  | .nil => Nat.zero\n  | .cons h t => Nat.succ (len A t)\n#check len\n#reduce len Nat (List.cons Nat.zero List.nil)\ndef double : (n : Nat) → Nat\n  | .zero => Nat.zero\n  | .succ k => Nat.succ (Nat.succ (double k))\n#reduce double (Nat.succ Nat.zero)\n"
          "Nat : U0\nList : (x0 : U0) → U0\nlen : (x0 : U0) → (x1 : (List x0)) → Nat\n(x0 : U0) → (x1 : (List x0)) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\ndouble : (x0 : Nat) → Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\n" },
    { name := "several scrutinees and nested patterns, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive Bool where\n  | false\n  | true\ndef eq : Nat → Nat → Bool\n  | .zero, .zero => Bool.true\n  | .succ m, .succ n => eq m n\n  | _, _ => Bool.false\ndef one : Nat := Nat.succ Nat.zero\ndef two : Nat := Nat.succ one\n#reduce eq two two\n#reduce eq two one\ninductive List (A : Type) where\n  | nil\n  | cons (head : A) (tail : List A)\ndef zipAdd : List Nat → List Nat → List Nat\n  | .cons a as, .cons b bs => List.cons (Nat.succ a) (zipAdd as bs)\n  | _, _ => List.nil\n#reduce zipAdd (List.cons one (List.cons two List.nil)) (List.cons Nat.zero List.nil)\ndef second (A : Type) (d : A) : List A → A\n  | .cons _ (.cons b _) => b\n  | _ => d\n#reduce second Nat Nat.zero (List.cons one (List.cons two List.nil))\ndef sub : Nat → Nat → Nat\n  | m, .zero => m\n  | .zero, _ => Nat.zero\n  | .succ m, .succ n => sub m n\n#reduce sub two one\ndef g : Nat → Nat\n  | .succ k => g k\n  | x => Nat.succ x\n#reduce g two\n"
          "Nat : U0\nBool : U0\neq : (x0 : Nat) → (x1 : Nat) → Bool\none : Nat\ntwo : Nat\ncon((#1, (tt, tt)))\ncon((#0, (tt, tt)))\nList : (x0 : U0) → U0\nzipAdd : (x0 : (List Nat)) → (x1 : (List Nat)) → (List Nat)\ncon((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt)))))\nsecond : (x0 : U0) → (x1 : x0) → (x2 : (List x0)) → x0\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nsub : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\ng : (x0 : Nat) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\n" },
    { name := "implicit arguments, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef id {A : Type} (x : A) : A := x\n#check id\n#check id Nat.zero\n#reduce id (Nat.succ Nat.zero)\ndef const {A B : Type} (a : A) (b : B) : A := a\n#reduce const Nat.zero (Nat.succ Nat.zero)\ninductive List (A : Type) where\n  | nil\n  | cons (head : A) (tail : List A)\ndef one : List Nat := List.cons Nat.zero List.nil\n#check one\n#reduce one\ndef two : List Nat := List.cons (id Nat.zero) (List.cons (Nat.succ Nat.zero) List.nil)\n#reduce two\ndef twice {A : Type} (f : A → A) (x : A) : A := f (f x)\n#reduce twice Nat.succ Nat.zero\ndef bad : List Nat := List.nil\ndef bad2 : Nat := id List.nil\ndef map {A B : Type} (f : A → B) (l : List A) : List B := match l with\n  | .nil => List.nil\n  | .cons h t => List.cons (f h) (map f t)\n#reduce map Nat.succ (List.cons Nat.zero List.nil)\ndef length {A : Type} : List A → Nat\n  | .nil => Nat.zero\n  | .cons _ t => Nat.succ (length t)\n#reduce length one\n"
          "Nat : U0\nid : (x0 :0 U0) → (x1 : x0) → x0\n(x0 :0 U0) → (x1 : x0) → x0\nNat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nconst : (x0 :0 U0) → (x1 :0 U0) → (x2 : x0) → (x3 : x1) → x0\ncon((#0, (tt, tt)))\nList : (x0 : U0) → U0\none : (List Nat)\n(List Nat)\ncon((#1, (con((#0, (tt, tt))), (con((#0, (tt, tt))), (tt, tt)))))\ntwo : (List Nat)\ncon((#1, (con((#0, (tt, tt))), (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt))))), (tt, tt)))))\ntwice : (x0 :0 U0) → (x1 : (x1 : x0) → x0) → (x2 : x0) → x0\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nbad : (List Nat)\nerror: type mismatch: expected Nat, got (List ?m1)\nmap : (x0 :0 U0) → (x1 :0 U0) → (x2 : (x2 : x0) → x1) → (x3 : (List x0)) → (List x1)\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt)))))\nlength : (x0 :0 U0) → (x1 : (List x0)) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\n" },
    { name := "constructors by their names (.c) and @f, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive List (A : Type) where\n  | nil\n  | cons (head : A) (tail : List A)\ndef two : Nat := .succ (.succ .zero)\n#reduce two\ndef xs : List Nat := .cons .zero (.cons two .nil)\n#reduce xs\ndef id {A : Type} (x : A) : A := x\n#reduce @id Nat .zero\ndef add : Nat → Nat → Nat\n  | .zero, n => n\n  | .succ m, n => .succ (add m n)\n#reduce add two two\ndef map {A B : Type} (f : A → B) : List A → List B\n  | .nil => .nil\n  | .cons h t => .cons (f h) (map f t)\n#reduce map (add two) xs\ndef bad : Nat := .nil\n"
          "Nat : U0\nList : (x0 : U0) → U0\ntwo : Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nxs : (List Nat)\ncon((#1, (con((#0, (tt, tt))), (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt))))), (tt, tt)))))\nid : (x0 :0 U0) → (x1 : x0) → x0\ncon((#0, (tt, tt)))\nadd : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nmap : (x0 :0 U0) → (x1 :0 U0) → (x2 : (x2 : x0) → x1) → (x3 : (List x0)) → (List x1)\ncon((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (con((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt))))), (tt, tt)))))\nerror: unknown identifier Nat.nil\n" },
    { name := "partial definitions and mutual blocks, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive Bool where\n  | false\n  | true\npartial def loop (n : Nat) : Nat := loop (.succ n)\n#check loop\nmutual\ndef isEven : Nat → Bool\n  | .zero => .true\n  | .succ n => isOdd n\ndef isOdd : Nat → Bool\n  | .zero => .false\n  | .succ n => isEven n\nend\n#check isOdd\npartial def bad (n : Nat) : Nat := Type\n"
          "Nat : U0\nBool : U0\nloop : (x0 : Nat) → Nat\n(x0 : Nat) → Nat\nisEven : (x0 : Nat) → Bool\nisOdd : (x0 : Nat) → Bool\n(x0 : Nat) → Bool\nerror: type mismatch: expected Nat, got U1\n" },
    { name := "indexed families, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A Nat.zero\n  | cons (n : Nat) (a : A) (v : Vec A n) : Vec A (Nat.succ n)\n#check Vec.cons\ndef v2 : Vec Nat (.succ (.succ .zero)) := Vec.cons (.succ .zero) .zero (Vec.cons .zero (.succ .zero) Vec.nil)\n#reduce v2\ndef len {A : Type} {n : Nat} (v : Vec A n) : Nat := match v with\n  | .nil => Nat.zero\n  | .cons _ _ t => Nat.succ (len t)\n#reduce len v2\ndef head {A : Type} {n : Nat} (d : A) (v : Vec A n) : A := match v with\n  | .cons _ a _ => a\n  | _ => d\n#reduce head (.succ (.succ .zero)) v2\ndef bad : Vec Nat .zero := Vec.cons .zero .zero Vec.nil\n"
          "Nat : U0\nVec : (x0 : U0) → (x1 : Nat) → U0\n(x0 :0 U0) → (x1 : Nat) → (x2 : x0) → (x3 : ((Vec x0) x1)) → ((Vec x0) (Nat.succ x1))\nv2 : ((Vec Nat) (Nat.succ (Nat.succ Nat.zero)))\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (con((#1, (con((#0, (tt, tt))), (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (refl(Nat, Nat.zero), tt))), (refl(Nat, (Nat.succ con((#0, (tt, tt))))), tt)))))), (refl(Nat, (Nat.succ con((#1, (con((#0, (tt, tt))), (tt, tt)))))), tt))))))\nlen : (x0 :0 U0) → (x1 :0 Nat) → (x2 : ((Vec x0) x1)) → Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nhead : (x0 :0 U0) → (x1 :0 Nat) → (x2 : x0) → (x3 : ((Vec x0) x1)) → x0\ncon((#0, (tt, tt)))\nerror: type mismatch: expected ((Vec Nat) Nat.zero), got ((Vec ?m0) (Nat.succ Nat.zero))\n" },
    { name := "impossible cases ruled out by index equations, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A Nat.zero\n  | cons (n : Nat) (a : A) (v : Vec A n) : Vec A (Nat.succ n)\ndef head1 {A : Type} (v : Vec A (.succ .zero)) : A := match v with\n  | .cons _ a _ => a\n#reduce head1 (Vec.cons .zero (Nat.succ Nat.zero) Vec.nil)\ndef isNil {A : Type} (v : Vec A .zero) : Nat := match v with\n  | .nil => .zero\n#reduce isNil (@Vec.nil Nat)\ndef bad {A : Type} (v : Vec A (.succ .zero)) : A := match v with\n  | .nil => Type\n"
          "Nat : U0\nVec : (x0 : U0) → (x1 : Nat) → U0\nhead1 : (x0 :0 U0) → (x1 : ((Vec x0) (Nat.succ Nat.zero))) → x0\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nisNil : (x0 :0 U0) → (x1 : ((Vec x0) Nat.zero)) → Nat\ncon((#0, (tt, tt)))\nerror: type mismatch: expected A, got U1\n" },
    { name := "mutual inductive types, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\nmutual\ninductive Tm where\n  | var (n : Nat)\n  | app (f : Tm) (args : Tms)\ninductive Tms where\n  | nil\n  | cons (t : Tm) (rest : Tms)\nend\n#check Tm.app\ndef t1 : Tm := .app (.var .zero) (.cons (.var (.succ .zero)) .nil)\n#check t1\ndef head : Tm → Nat\n  | .var n => n\n  | .app f _ => head f\n#reduce head t1\ndef len : Tms → Nat\n  | .nil => .zero\n  | .cons _ r => .succ (len r)\n#reduce len (.cons (.var .zero) (.cons (.var .zero) .nil))\n"
          "Nat : U0\nTm : U0\nTms : U0\n(x0 : Tm) → (x1 : Tms) → Tm\nt1 : Tm\nTm\nhead : (x0 : Tm) → Nat\ncon((#0, (tt, tt)))\nlen : (x0 : Tms) → Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\n" },
    { name := "parameterised mutual inductive types, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\nmutual\ninductive Tree (A : Type) where\n  | leaf (a : A)\n  | node (kids : Forest A)\ninductive Forest (A : Type) where\n  | nil\n  | cons (t : Tree A) (rest : Forest A)\nend\n#check Tree.node\ndef t : Tree Nat := .node (.cons (.leaf .zero) (.cons (.leaf (.succ .zero)) .nil))\ndef size {A : Type} : Forest A → Nat\n  | .nil => .zero\n  | .cons _ r => .succ (size r)\ndef kids {A : Type} (d : Forest A) : Tree A → Forest A\n  | .node k => k\n  | _ => d\n#reduce size (kids .nil t)\n"
          "Nat : U0\nTree : (x0 : U0) → U0\nForest : (x0 : U0) → U0\n(x0 :0 U0) → (x1 : (Forest x0)) → (Tree x0)\nt : (Tree Nat)\nsize : (x0 :0 U0) → (x1 : (Forest x0)) → Nat\nkids : (x0 :0 U0) → (x1 : (Forest x0)) → (x2 : (Tree x0)) → (Forest x0)\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\n" },
    { name := "structures and projections, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\nstructure Pair (A B : Type) where\n  fst : A\n  snd : B\n#check Pair.mk\ndef p : Pair Nat (Pair Nat Nat) := .mk .zero (.mk (.succ .zero) .zero)\n#reduce Pair.fst (Pair.snd p)\ndef swap {A B : Type} (q : Pair A B) : Pair B A := .mk (Pair.snd q) (Pair.fst q)\n#reduce Pair.fst (swap p)\n#reduce p.snd.fst\ndef swap2 {A B : Type} (q : Pair A B) : Pair B A := .mk q.snd q.fst\n#reduce (swap2 p).fst\n"
          "Nat : U0\nPair : (x0 : U0) → (x1 : U0) → U0\nPair.fst : (x0 :0 U0) → (x1 :0 U0) → (x2 : ((Pair x0) x1)) → x0\nPair.snd : (x0 :0 U0) → (x1 :0 U0) → (x2 : ((Pair x0) x1)) → x1\n(x0 :0 U0) → (x1 :0 U0) → (x2 : x0) → (x3 : x1) → ((Pair x0) x1)\np : ((Pair Nat) ((Pair Nat) Nat))\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nswap : (x0 :0 U0) → (x1 :0 U0) → (x2 : ((Pair x0) x1)) → ((Pair x1) x0)\ncon((#0, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt)))))\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nswap2 : (x0 :0 U0) → (x1 :0 U0) → (x2 : ((Pair x0) x1)) → ((Pair x1) x0)\ncon((#0, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt)))))\n" },
    { name := "numerals and match as a term, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef add : Nat → Nat → Nat\n  | 0, n => n\n  | .succ m, n => .succ (add m n)\n#reduce add 2 3\ndef isSmall : Nat → Nat\n  | 0 => 1\n  | 1 => 1\n  | _ => 0\n#reduce isSmall 1\n#reduce isSmall 5\ninductive Bool where\n  | false\n  | true\ndef lt : Nat → Nat → Bool\n  | _, 0 => .false\n  | 0, .succ _ => .true\n  | .succ m, .succ n => lt m n\n#reduce lt 1 3\ndef pick (b : Bool) (x y : Nat) : Nat := add (match b with\n  | .true => x\n  | .false => y) 1\n#reduce pick .false 2 5\ndef both (a b : Bool) : Bool := match a, b with\n  | .true, .true => .true\n  | _, _ => .false\n#reduce both .true .false\n"
          "Nat : U0\nadd : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nisSmall : (x0 : Nat) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\ncon((#0, (tt, tt)))\nBool : U0\nlt : (x0 : Nat) → (x1 : Nat) → Bool\ncon((#1, (tt, tt)))\npick : (x0 : Bool) → (x1 : Nat) → (x2 : Nat) → Nat\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nboth : (x0 : Bool) → (x1 : Bool) → Bool\ncon((#0, (tt, tt)))\n" },
    { name := "the Prelude, if and strings, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\n#check Nat.add\ndef three : Nat := Nat.add 1 2\n#reduce Nat.beq three 3\ndef min (m n : Nat) : Nat := if Nat.lt m n then m else n\n#reduce min 2 1\ndef hi : String := \"hi\"\n#reduce String.length (String.append hi \"!\")\ndef firstCode (s : String) : Nat := match s.data with\n  | .cons c _ => c.code\n  | .nil => 0\n#reduce Nat.beq (firstCode \"A\") 65\n"
          "(x0 : Nat) → (x1 : Nat) → Nat\nthree : Nat\ncon((#1, (tt, tt)))\nmin : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nhi : String\ncon((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nfirstCode : (x0 : String) → Nat\ncon((#1, (tt, tt)))\n" },
    { name := "infix operators, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\n#reduce Nat.beq (2 + 3 * 2) 8\ndef pred2 : Nat → Nat\n  | n + 2 => n\n  | _ => 0\n#reduce Nat.beq (pred2 5) 3\n#reduce Nat.beq (10 - 3 - 2) 5\ninfixr:50 \" ⊕ \" => Bool.or\n#reduce .false ⊕ .false ⊕ .true\ndef len3 : Nat := List.length (List.cons 1 .nil ++ List.cons 2 (List.cons 3 .nil))\n#reduce Nat.beq len3 3\n#reduce Nat.le 3 3\n"
          "con((#1, (tt, tt)))\npred2 : (x0 : Nat) → Nat\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\nlen3 : Nat\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\n" },
    { name := "axioms, Unit, Array, IO and do, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\nforeign_type Secret\nextern \"wiz_peek\" peek : Secret → Nat\ndef unit : Unit := ()\ndef twice (s : String) : IO Unit := do\n  IO.println s;\n  let t := String.append s \"!\";\n  IO.println t\ndef readLen (p : String) : IO Nat := do\n  s ← IO.readFile p;\n  IO.pure (String.length s)\ndef push2 (a : Array Nat) : Array Nat := Array.push (Array.push a 1) 2\ndef size2 : Nat := Array.size (push2 Array.empty)\ndef sum3 (n : Nat) : Nat :=\n  let m := n + n;\n  m + n\n#reduce Nat.beq (sum3 2) 6\n"
          "Secret : U0\npeek : (x0 : Secret) → Nat\nunit : Unit0\ntwice : (x0 : String) → (IO Unit0)\nreadLen : (x0 : String) → (IO Nat)\npush2 : (x0 : (Array Nat)) → (Array Nat)\nsize2 : Nat\nsum3 : (x0 : Nat) → Nat\ncon((#1, (tt, tt)))\n" },
    { name := "Syntax, StrMap and definitions as types, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\ndef leaf : Syntax := .node \"leaf\" (.cons (.atom \"x\") .nil)\ndef kindOf : Syntax → String\n  | .node k _ => k\n  | _ => \"\"\n#reduce String.length (kindOf leaf)\ndef argCount {b : Bool} : SyntaxF b → Nat\n  | .cons _ t => argCount t + 1\n  | .node _ args => argCount args\n  | _ => 0\n#reduce Nat.beq (argCount leaf) 1\ninductive Cat where\n  | mk (name : String) (n : Nat)\ndef find : List Cat → String → Option Cat\n  | .nil, _ => .none\n  | .cons (.mk m n) rest, name => match Nat.beq (String.length m) (String.length name) with\n    | .true => .some (.mk m n)\n    | .false => find rest name\ndef m : StrMap Nat := StrMap.insert StrMap.empty (Str.ofString \"k\") 1\n"
          "leaf : Syntax\nkindOf : (x0 : Syntax) → String\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nargCount : (x0 :0 Bool) → (x1 : (SyntaxF x0)) → Nat\ncon((#1, (tt, tt)))\nCat : U0\nfind : (x0 : (List Cat)) → (x1 : String) → (Option Cat)\nm : (StrMap Nat)\n" },
    { name := "function fields and catch-alls on mutual types, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\nmutual\ninductive Tm where\n  | lit (n : Nat)\n  | app (f : Tm) (a : Tm)\n  | many (ts : Tms)\ninductive Tms where\n  | nil\n  | cons (t : Tm) (ts : Tms)\nend\ndef litOr : Tm → Tm\n  | .lit n => .lit (n + 1)\n  | t => t\n#reduce litOr (.lit 1)\n#reduce litOr (.many .nil)\nmutual\ninductive Val where\n  | vnat (n : Nat)\n  | vlazy (v : Unit → Val)\n  | vbox (b : Box)\ninductive Box where\n  | mk (v : Val)\nend\npartial def force : Val → Val\n  | .vlazy v => force (v ())\n  | v => v\ndef unwrap : Val → Val\n  | .vlazy v => v ()\n  | v => v\n#reduce unwrap (Val.vlazy (fun _ => Val.vnat 3))\ndef big (n : Nat) : Nat := Nat.max n 3\n#reduce Nat.beq (big 1) 3\n"
          "Tm : U0\nTms : U0\nlitOr : (x0 : Tm) → Tm\ncon((#0, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (refl(Enum2, #0), tt))))\ncon((#2, (con((#3, (refl(Enum2, #1), tt))), (refl(Enum2, #0), tt))))\nVal : U0\nBox : U0\nforce : (x0 : Val) → Val\nunwrap : (x0 : Val) → Val\ncon((#0, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (refl(Enum2, #0), tt))))\nbig : (x0 : Nat) → Nat\ncon((#1, (tt, tt)))\n" },
    { name := "recursion through function fields, reordered parameters, big numerals, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\nmutual\ninductive Val where\n  | vnat (n : Nat)\n  | vsuc (v : Val)\n  | vlazy (v : Unit → Val)\n  | vbox (b : Box)\ninductive Box where\n  | mk (v : Val)\nend\ndef whnf : Val → Val\n  | .vlazy v => whnf (v ())\n  | v => v\ndef depth : Val → Nat\n  | .vsuc v => depth v + 1\n  | .vlazy v => depth (v ())\n  | _ => 0\n#reduce Nat.beq (depth (whnf (Val.vlazy (fun _ => Val.vlazy (fun _ => Val.vnat 3))))) 0\n#reduce Nat.beq (depth (Val.vsuc (Val.vlazy (fun _ => Val.vsuc (Val.vnat 0))))) 2\ndef apps : Nat → List Nat → Nat\n  | f, .nil => f\n  | f, .cons a rest => apps (f + a) rest\n#reduce Nat.beq (apps 1 (List.cons 2 (List.cons 3 .nil))) 6\ndef big : Nat := 100000\n#check big\ndef bigger : Nat := 1000000000\n#reduce Nat.beq (Nat.sub 1000 999) 1\n"
          "Val : U0\nBox : U0\nwhnf : (x0 : Val) → Val\ndepth : (x0 : Val) → Nat\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\napps : (x0 : Nat) → (x1 : (List Nat)) → Nat\ncon((#1, (tt, tt)))\nbig : Nat\nNat\nbigger : Nat\ncon((#1, (tt, tt)))\n" },
    { name := "postponed and inferred matches, pruning, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\ndef h1 : List Syntax → List String\n  | .nil => .nil\n  | .cons s rest => .cons (match s with\n      | .ident n => n\n      | _ => \"_\") .nil\ndef h2 (s : Syntax) : List String := .cons (match s with\n      | .ident n => n\n      | _ => \"_\") .nil\ndef h3 (s : List Nat) : List Nat := .cons (match s with\n      | .nil => 0\n      | _ => 1) .nil\ndef h4 (s : List Nat) : List Nat := List.cons (match s with\n      | .nil => 0\n      | _ => 1) .nil\ndef k1 (s : List Nat) : Nat :=\n  let x := match s with\n    | .nil => 0\n    | _ => 1;\n  x + 1\ndef k2 (b : Bool) : Nat :=\n  let y := if b then 2 else 3;\n  y\n#reduce Nat.beq (k1 .nil) 1\n#reduce Nat.beq (k2 .false) 3\ndef genTys (p base : Nat) : Nat → List Nat → List Nat\n  | _, .nil => .nil\n  | m, .cons t rest => .cons (t + m + p) (genTys p base (m + 1) rest)\n#reduce Nat.beq (List.length (genTys 1 2 0 (List.cons 1 (List.cons 2 .nil)))) 2\ndef kw (stx : Syntax) (p : Nat) : String :=\n  let kw := match stx with\n    | .atom v => v\n    | _ => \"infix\";\n  kw\ndef g2 (xs : List Nat) : Nat := match xs with\n    | .cons _ t => match List.append t t with\n      | .nil => 0\n      | later => List.length later\n    | .nil => 0\n#reduce Nat.beq (g2 (List.cons 1 (List.cons 2 .nil))) 2\ndef takeL {A : Type} : Nat → List A → List A\n  | .zero, _ => .nil\n  | .succ n, xs => match xs with\n    | .nil => .nil\n    | .cons x rest => .cons x (takeL n rest)\ndef sp (k : Nat) : List (List Nat) → List (List Nat)\n  | .nil => .nil\n  | .cons pats rest =>\n    let before := takeL k pats;\n    match List.length pats with\n    | .zero => .cons (List.append before .nil) (sp k rest)\n    | .succ _ => sp k rest\ndef sp2 (k : Nat) (pats : List Nat) : List (List Nat) :=\n    let before := takeL k pats;\n    .cons (List.append before .nil) .nil\ninductive Cl where\n  | mk (pats : List Nat) (binds : List Nat) (rhs : Nat)\ndef sp3 (k : Nat) : List Cl → List Cl\n  | .nil => .nil\n  | .cons (.mk pats binds rhs) rest =>\n    let before := takeL k pats;\n    let after := takeL k pats;\n    match List.length pats with\n    | .zero => .cons (.mk (List.append before (List.append pats after)) binds rhs) (sp3 k rest)\n    | .succ _ => sp3 k rest\ndef sp4 (T : String) (k : Nat) : List Cl → List Cl\n  | .nil => .nil\n  | .cons (.mk pats binds rhs) rest =>\n    let before := takeL k pats;\n    match List.length pats with\n    | .zero => .cons (.mk (List.append before pats) binds rhs) (sp4 T k rest)\n    | .succ _ =>\n      let binds' := match Nat.beq k 0 with\n        | .true => binds\n        | .false => List.append binds (.cons k .nil);\n      .cons (.mk before binds' rhs) (sp4 T k rest)\n"
          "h1 : (x0 : (List Syntax)) → (List String)\nh2 : (x0 : Syntax) → (List String)\nh3 : (x0 : (List Nat)) → (List Nat)\nh4 : (x0 : (List Nat)) → (List Nat)\nk1 : (x0 : (List Nat)) → Nat\nk2 : (x0 : Bool) → Nat\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ngenTys : (x0 : Nat) → (x1 : Nat) → (x2 : Nat) → (x3 : (List Nat)) → (List Nat)\ncon((#1, (tt, tt)))\nkw : (x0 : Syntax) → (x1 : Nat) → String\ng2 : (x0 : (List Nat)) → Nat\ncon((#1, (tt, tt)))\ntakeL : (x0 :0 U0) → (x1 : Nat) → (x2 : (List x0)) → (List x0)\nsp : (x0 : Nat) → (x1 : (List (List Nat))) → (List (List Nat))\nsp2 : (x0 : Nat) → (x1 : (List Nat)) → (List (List Nat))\nCl : U0\nsp3 : (x0 : Nat) → (x1 : (List Cl)) → (List Cl)\nsp4 : (x0 : String) → (x1 : Nat) → (x2 : (List Cl)) → (List Cl)\n" },
    { name := "the self-hosted frontend: a lambda waits for the arguments that fix its domains", run := fun _ =>
        selfhostCheckFile ("import Prelude\n" ++
          "def zip3 {A B C D : Type} (f : A → B → C → D) : List A → List B → List C → List D\n" ++
          "  | .cons a as, .cons b bs, .cons c cs => .cons (f a b c) (zip3 f as bs cs)\n  | _, _, _ => .nil\n" ++
          "def sel (c : List Bool) (t e : List Nat) : List Nat := zip3 (fun b x y => if b then x else y) c t e\n" ++
          "#reduce Nat.beq (List.length (sel (List.cons .true .nil) (List.cons 1 .nil) (List.cons 2 .nil))) 1\n")
          ("zip3 : (x0 :0 U0) → (x1 :0 U0) → (x2 :0 U0) → (x3 :0 U0) → (x4 : (x4 : x0) → (x5 : x1) → (x6 : x2) → x3) → (x5 : (List x0)) → (x6 : (List x1)) → (x7 : (List x2)) → (List x3)\n" ++
          "sel : (x0 : (List Bool)) → (x1 : (List Nat)) → (x2 : (List Nat)) → (List Nat)\ncon((#1, (tt, tt)))\n") },
    { name := "the self-hosted backend compiles and runs a program", run := fun _ =>
        selfhostCompileRun selfhostProgram1
          "6765\n5050\n1989\n2\nyes, ünïcode\n2\n5\n" },
    { name := "the self-hosted backend compiles and runs a program with reference counting (no leaks)", run := fun _ =>
        selfhostCompileRun selfhostProgram1 "6765\n5050\n1989\n2\nyes, ünïcode\n2\n5\n" (flags := #["--rc"]) },
    { name := "reference counting: deep lists, unused parameters and hypotheses, shared arrays, closures", run := fun _ =>
        selfhostCompileRun selfhostProgram2 "1000000\n0\n6\n15\n5\n3\n" (flags := #["--rc"]) },
    { name := "the first-line pragma `-- wiz: rc` still selects reference counting (a fallback, 21k)", run := fun _ =>
        selfhostCompileRun ("-- wiz: rc\n" ++ selfhostProgram2) "1000000\n0\n6\n15\n5\n3\n" },
    { name := "self tail calls are loops: 10M iterations on a 1 MB stack, at -O0, with the GC and with RC (15f)", run := fun _ => do
        -- (in a branch of a match on a parameter: in the GC mode a call under a match on a
        -- computed value is still inside a suspended `let`'s closure)
        let prog := "import Prelude\npartial def count (n acc : Nat) : Nat := match n with\n  | .zero => acc\n" ++
          "  | .succ m => count m (acc + 1)\ndef main : IO Unit := IO.println (Nat.toString (count 10000000 0))\n"
        selfhostCompileRun prog "10000000\n" (opt := "-O0") (smallStack := true)
        selfhostCompileRun prog "10000000\n" (flags := #["--rc"]) (opt := "-O0") (smallStack := true)
        selfhostCompileRun prog "10000000\n" (flags := #["--rc-owned"]) (opt := "-O0") (smallStack := true)
        -- under reference counting lets are strict: a call under a match on a computed value loops too
        let nested := "import Prelude\npartial def count (n acc : Nat) : Nat := match n with\n  | .zero => acc\n" ++
          "  | .succ m => match Nat.beq (Nat.mod m 3) 0 with\n    | .true => count m (acc + 2)\n    | .false => count m acc\n" ++
          "def main : IO Unit := IO.println (Nat.toString (count 10000000 0))\n"
        selfhostCompileRun nested "6666668\n" (flags := #["--rc"]) (opt := "-O0") (smallStack := true) },
    { name := "big numerals with the self-hosted compiler: no deep recursion, 63-bit words (15g)", run := fun _ => do
        selfhostCompileRun selfhostBigLits selfhostBigLitsExpected
        selfhostCompileRun selfhostBigLits selfhostBigLitsExpected (flags := #["--rc"]) },
    { name := "the self-hosted compiler stops at a frontend error: exit code 1, the errors on stderr, no C (15g)", run := fun _ =>
        selfhostCompileFails ("import Prelude\ndef a : Nat := 9223372036854775808\ndef b : Nat := nope\n" ++
          "def main : IO Unit := IO.println (Nat.toString 1)\n")
          ("error: the numeral does not fit in 63 bits (numbers are 63-bit words here)\nerror: unknown identifier nope\n") },
    { name := "a numeral from 2^63 is an error in the self-hosted frontend, not a wrapped number (15g)", run := fun _ =>
        selfhostCheckFile ("import Prelude\ndef a : Nat := 9223372036854775807\ndef b : Nat := 9223372036854775808\n" ++
          "def c : Nat := 18446744073709551616\ndef d : Nat := 18446744073709551617\ndef e : Nat := 1000000000000000000000000000000\n" ++
          "def f : Nat := 0009223372036854775807\n")
          ("a : Nat\n" ++ "error: the numeral does not fit in 63 bits (numbers are 63-bit words here)\n" ++ "error: the numeral does not fit in 63 bits (numbers are 63-bit words here)\n" ++
            "error: the numeral does not fit in 63 bits (numbers are 63-bit words here)\n" ++ "error: the numeral does not fit in 63 bits (numbers are 63-bit words here)\n" ++ "f : Nat\n") },
    { name := "dead lets without effects are not computed (15e)", run := fun _ =>
        selfhostCompileRun ("import Prelude\ndef f (n : Nat) : Nat :=\n  let unused := List.cons n (List.cons 2 .nil);\n" ++
          "  let alsoUnused := List.cons unused .nil;\n  n + 1\ndef main : IO Unit := IO.println (Nat.toString (f 41))\n") "42\n" (flags := #["--rc"]) },
    { name := "reference counting: cells reused (shared and unique lists, trees, pairs)", run := fun _ =>
        selfhostCompileRun selfhostProgram3 "1000000\n9900\n18\n4\n" (flags := #["--rc"]) },
    { name := "reference counting: lets strict, dropped, moved into a branch or suspended by their demand", run := fun _ => do
        selfhostCompileRun selfhostProgram4 "110\n0\n7\n23\n13\n" (flags := #["--rc"])
        selfhostCompileRun selfhostProgram4 "110\n0\n7\n23\n13\n" },
    { name := "reference counting: hypotheses read once or as functions are not memoised (and a reused partial recursion stays linear per call)", run := fun _ => do
        selfhostCompileRun selfhostProgram5 "4498500\n3000\n1099511627775\n65536\n" (flags := #["--rc"]) },
    { name := "self-hosted programs read their command-line arguments (IO.args, 21k), with either collector", run := fun _ => do
        let prog := "import Prelude\ndef printAll : List String → IO Unit\n  | .nil => IO.pure ()\n  | .cons s rest => do\n    IO.println s;\n    printAll rest\n" ++
          "def main : IO Unit := do\n  n ← IO.argCount;\n  IO.println (Nat.toString n);\n  args ← IO.args;\n  printAll args\n"
        selfhostCompileRun prog "0\n"
        selfhostCompileRun prog "2\n--rc\nünï code\n" (progArgs := #["--rc", "ünï code"])
        selfhostCompileRun prog "1\nx\n" (flags := #["--rc"]) (progArgs := #["x"]) },
    { name := "the self-hosted backend: division, powers and bits", run := fun _ =>
        selfhostCompileRun ("import Prelude\ndef show (n : Nat) : IO Unit := IO.println (Nat.toString n)\n" ++
          "def main : IO Unit := do\n  show (100 / 7);\n  show (Nat.mod 100 7);\n  show (Nat.div 5 0);\n  show (Nat.mod 5 0);\n" ++
          "  show (Nat.pow 3 20);\n  show (Nat.land 12 10);\n  show (Nat.lor 12 10);\n  show (Nat.xor 12 10);\n" ++
          "  show (Nat.shiftLeft 3 20);\n  show (Nat.shiftRight 1000 3);\n  show (Nat.log2 1025);\n" ++
          "  IO.println (if Nat.testBit 5 2 then \"set\" else \"clear\")\n")
          "14\n2\n0\n5\n3486784401\n8\n14\n6\n3145728\n125\n10\nset\n" },
    { name := "foreign functions: the Lean and the self-hosted compilers agree (21l)", run := fun _ =>
        ffiAgrees ffiProgram1 ffiExpected1 },
    { name := "foreign pointers: the finalizer runs with the last reference, in both compilers (21l)", run := fun _ =>
        ffiAgrees (ffiProgramFin false) "line\nline\nline\n" (gc := false) },
    { name := "foreign pointers passed around and flushed, with either collector (21l)", run := fun _ =>
        ffiAgrees (ffiProgramFin true) "line\nline\nline\n" },
    { name := "the self-hosted frontend: foreign types are checked (21l)", run := fun _ =>
        selfhostCheckFile "import Prelude\nextern \"f\" f : (Nat → Nat) → Nat\nforeign_type T\nextern \"g\" g : {A : Type} → A → T → IO A\n"
          "error: a foreign function's arguments and result must be Nat, UInt64, Float64, String, Bool, Unit or a Wiz data type (the result may be in IO)\nT : U0\ng : (x0 :0 U0) → (x1 : x0) → (x2 : T) → (IO x0)\n" },
    { name := "the self-hosted frontend: the Prelude's division and bits compute", run := fun _ =>
        selfhostCheckFile "import Prelude\n#reduce Nat.beq (Nat.mod 17 5) 2\n#reduce Nat.beq (Nat.xor 6 3) 5\n#reduce Nat.beq (Nat.log2 9) 3\n"
          "con((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\n" },
    { name := "the self-hosted frontend: phantom parameters count, as in the Lean frontend (21i)", run := fun _ =>
        selfhostAgrees phantomHeader [
          ("def same (x : UIntN 8) : UIntN 8 := x\n", true),
          ("def bad (x : UIntN 8) : UIntN 16 := x\n", false),
          ("def badP (x : Proxy Nat) : Proxy Bool := x\n", false),
          ("def badS (x : S 8) : S 16 := x\n", false),
          ("def badN (x : N 1) : N 2 := x\n", false),
          ("def w8 : Nat := width _ u8\ndef get {w : Nat} : UIntN w → Nat\n  | .mk n => n\ndef sx {w : Nat} (a : S w) : Nat := a.x\n" ++
            "def N.add {w : Nat} : N w → N w → N w\n  | .z, m => m\n  | .s n, m => .s (N.add n m)\n", true)] },
    { name := "the self-hosted frontend: phantom parameters are inferred, and computation is unchanged (21i)", run := fun _ =>
        selfhostCheckFile ("import Prelude\n" ++ phantomHeader ++
          "#reduce Nat.beq (width _ u8) 8\n#reduce Nat.beq (S.x (S.mk 5 : S 16)) 5\n" ++
          "def N.toNat {w : Nat} : N w → Nat\n  | .z => 0\n  | .s n => N.toNat n + 1\n#reduce Nat.beq (N.toNat (.s (.s .z) : N 3)) 2\n" ++
          "inductive V (w : Nat) (A : Type) : Nat → Type where\n  | nil : V w A .zero\n")
          ("UIntN : (x0 : Nat) → U0\nProxy : (x0 : U0) → U0\nS : (x0 : Nat) → U0\nS.x : (x0 :0 Nat) → (x1 : (S x0)) → Nat\nN : (x0 : Nat) → U0\n" ++
          "width : (x0 : Nat) → (x1 : (UIntN x0)) → Nat\nu8 : (UIntN (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))\n" ++
          "con((#1, (tt, tt)))\ncon((#1, (tt, tt)))\nN.toNat : (x0 :0 Nat) → (x1 : (N x0)) → Nat\ncon((#1, (tt, tt)))\n" ++
          "error: a parameter that no constructor mentions (a phantom parameter) of an indexed family is not supported by the self-hosted frontend\n") },
    { name := "the self-hosted backend: phantom parameters are erased (21i)", run := fun _ =>
        selfhostCompileRun ("import Prelude\ninductive Box (w : Nat) where\n  | mk (n : Nat)\nstructure Pt (w : Nat) where\n  x : Nat\n  y : Nat\n" ++
          "def get {w : Nat} : Box w → Nat\n  | .mk n => n\ndef sum {w : Nat} (p : Pt w) : Nat := p.x + p.y\n" ++
          "def b : Box 8 := .mk 3\ndef p : Pt 8 := .mk 1 2\n" ++
          "def main : IO Unit := IO.println (Nat.toString (get b + sum p))\n") "6\n" },
    { name := "the self-hosted frontend: written quantities, as in the Lean frontend (21m, K10)", run := fun _ =>
        selfhostAgrees quantityHeader quantityDecls },
    { name := "the self-hosted frontend: quantities, the pinned differences (21m)", run := fun _ =>
        selfhostVerdicts quantityHeader quantityDiffs },
    { name := "the self-hosted backend: quantities erase and run, with either collector (21m)", run := fun _ => do
        selfhostCompileRun quantityProgram "6\n5\n9\n"
        selfhostCompileRun quantityProgram "6\n5\n9\n" (flags := #["--rc"]) },
    { name := "the self-hosted frontend: private declarations, constructors and fields, as in one Lean module (21n)", run := fun _ =>
        selfhostAgrees "" privateDecls },
    { name := "the self-hosted frontend: an unknown command is an error naming it (21n)", run := fun _ =>
        selfhostCheckFile "import Prelude\ndef f : Nat := 1\n#eval f\nattribute [inline] f\ndef g : Nat := f\n"
          "f : Nat\nerror: unsupported command command.eval\nerror: unsupported command command.attrInline\ng : Nat\n" },
    { name := "the self-hosted frontend: export and link_lib are checked as in the Lean frontend (21o)", run := fun _ =>
        selfhostAgrees exportHeader exportDecls },
    { name := "export, link_c and link_lib: the Lean and the self-hosted compilers agree (21o)", run := fun _ => do
        linkRun exportFiles exportExpected
        selfhostLinkRun exportFiles exportExpected
        selfhostLinkRun exportFiles exportExpected (flags := #["--rc"]) },
    { name := "a C Nat that does not fit the self-hosted runtime's 63 bits is an error, not cut (21p)", run := fun _ => do
        let prog := "import IO\ndef main : IO Unit := do\n  IO.println (Nat.toString (UInt64.toNat (UInt64.ofNat 1000000)));\n" ++
          "  IO.println (Nat.toString (UInt64.toNat (UInt64.sub (UInt64.ofNat 0) (UInt64.ofNat 1))))\n"
        ioRun prog "1000000\n18446744073709551615\n"
        selfhostLinkRun [("main.wiz", prog)] "1000000\n" (fails := some "does not fit in 63 bits")
        selfhostLinkRun [("main.wiz", prog)] "1000000\n" (flags := #["--rc"]) (fails := some "does not fit in 63 bits") },
    { name := "the self-hosted frontend: a sealed type has no look-alikes, as in the Lean frontend (22k)", run := fun _ =>
        selfhostAgrees sealHeader [
          ("def same (x : W 8) : W 8 := x\ndef get {w : Nat} : W w → Nat\n  | .mk n => n\ndef five : Nat := get (W.mk 5 : W 8)\n", true),
          ("def bad (x : L 8) : W 8 := x\n", false),
          ("def bad (x : W 8) : L 8 := x\n", false),
          ("def bad (x : V 8) : W 8 := x\n", false),
          ("def bad (x : W 8) : W 16 := x\n", false),
          ("sealed structure P where\n  x : Nat\n", false)] },
    { name := "the self-hosted frontend: constructor parameters from the expected type (21j)", run := fun _ =>
        selfhostAgrees ("def Code : Bool → Type\n  | .true => Nat\n  | .false => Bool\n" ++
          "structure Tagged (b : Bool) where\n  val : Code b\n")
          [("def t : Tagged .true := Tagged.mk 3\ndef f : Tagged .false := Tagged.mk .true\n" ++
              "def g (x : Nat) : Tagged .true := Tagged.mk (Nat.succ x)\n", true),
           ("def bad : Tagged .false := Tagged.mk 3\n", false)] },
    { name := "both kernels compare propositions by equivalence (and agree on it below)", run := fun _ => do
        -- the domains' equation is an equivalence, not `False`
        match MTm.propShapes.map leanVerdict with
        | ["error", ok] => unless ok != "error" do throw (IO.userError "the equivalence was rejected")
        | vs => throw (IO.userError s!"unexpected verdicts {vs}") },
    { name := "Size = Size is stuck, not False (and both kernels agree on it below)", run := fun _ => do
        match MTm.sizeEq.map leanVerdict with
        | ["error", "error", "error", a, b] =>
          unless a == "EqTy(Size, Size)" && b == "EqTy(Size<(∞), Size<(∞))" do
            throw (IO.userError s!"unexpected types {a}, {b}")
        | vs => throw (IO.userError s!"unexpected verdicts {vs}") },
    { name := "projections need an unrestricted pair; positions at 0 are erased; eliminators use their scrutinee ω times (R1; and both kernels agree on it below)", run := fun _ => do
        for (t, ok) in MTm.projRule ++ MTm.elimRule ++ MTm.usageRule do
          let v := leanVerdict t
          unless (v != "error") == ok do
            throw (IO.userError s!"expected {if ok then "accepted" else "rejected"}, got {v}: {MTm.pretty 0 t}") },
    { name := "the size of μ and ν is checked (and both kernels agree on it below)", run := fun _ => do
        let vs := MTm.sizeArgs.map leanVerdict
        unless vs.take 2 == ["error", "error"] && (vs.drop 2).all (· != "error") do
          throw (IO.userError s!"unexpected verdicts {vs}") },
    { name := "∞ is not below itself (and both kernels agree on it below)", run := fun _ => do
        let vs := MTm.sizeInf.map leanVerdict
        unless vs.take 5 == List.replicate 5 "error" && (vs.drop 5).all (· != "error") do
          throw (IO.userError s!"unexpected verdicts {vs}") },
    { name := "F6: literal quantities that differ make types unequal (and both kernels agree on it below)", run := fun _ => do
        let vs := MTm.qtyApart.map leanVerdict
        unless vs.take 2 |>.all (· != "error") do throw (IO.userError s!"unexpected verdicts {vs}")
        unless vs[2]? == some "error" && vs[3]? != some "error" do throw (IO.userError s!"unexpected verdicts {vs}") },
    { name := "F3 (audit): the eliminators check the index type's level (and both kernels agree on it below)", run := fun _ => do
        let vs := MTm.elimLevels.map leanVerdict
        let names := ["ind", "sfix", "scase", "coit", "scofix"]
        for n in names, k in [0:5] do
          unless vs[k]? == some "error" do
            throw (IO.userError s!"{n} with an index type one level too high was accepted: {vs[k]?}")
          unless vs[5 + k]? == some "error" do
            throw (IO.userError s!"{n} with an index type one level too low was accepted: {vs[5 + k]?}")
          unless vs[10 + k]? != some "error" && vs[15 + k]? != some "error" do
            throw (IO.userError s!"{n} with a well-levelled index type was rejected: {vs[10 + k]?}, {vs[15 + k]?}")
        unless vs.drop 20 == ["error", "error"] do throw (IO.userError s!"unexpected verdicts {vs.drop 20}") },
    { name := "transp is rejected at a proposition, as eq and refl are (and both kernels agree on it below)", run := fun _ => do
        let vs := MTm.transpProp.map leanVerdict
        unless vs.take 2 == ["error", "error"] && (vs.drop 2).all (· != "error") && vs.length == 4 do
          throw (IO.userError s!"unexpected verdicts {vs}") },
    { name := "Q4: a small description field is rejected, a lifted one works (and both kernels agree on it below)", run := fun _ => do
        let vs := MTm.smallField.map leanVerdict
        let body := (vs.drop 4).dropLast
        unless vs.take 4 == List.replicate 4 "error" && body.all (· != "error") && vs.getLast? == some "error" do
          throw (IO.userError s!"unexpected verdicts {vs}")
        -- `getS D'` is a type (it computes to `ULift True`), and a boxed proof unboxes to `True`
        unless vs[5]? == some "U0" && vs[9]? == some "True" do
          throw (IO.userError s!"unexpected types {vs}") },
    { name := "the self-hosted frontend checks itself (Lex, Parse, Kernel and Frontend.wiz)", run := fun _ => do
        let src := (← IO.FS.readFile "selfhost/Lex.wiz") ++ "\n" ++ (← IO.FS.readFile "selfhost/Parse.wiz") ++ "\n" ++
          (← IO.FS.readFile "selfhost/Kernel.wiz") ++ "\n" ++ (← IO.FS.readFile "selfhost/Frontend.wiz")
        let body := "\n".intercalate ((src.splitOn "\n").filter (!·.startsWith "import"))
        -- every declaration is reported, none with an error
        let decls := (src.splitOn "\n").filter fun l =>
          ["def ", "partial def ", "inductive ", "structure "].any (fun (p : String) => l.startsWith p)
        let some out ← selfhostOutput ("import Prelude\n" ++ body) | pure ()
        let lines := (out.splitOn "\n").filter (· != "")
        for l in lines do
          if l.startsWith "error" || l.startsWith "parse error" then throw (IO.userError l)
        unless lines.length == decls.length do
          throw (IO.userError s!"{lines.length} lines for {decls.length} declarations") },
    { name := "the Wiz kernel agrees with the Lean kernel (400 random terms)", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let mut terms : Array MTm := MTm.samples.toArray
        let mut seed := 42
        for i in [0:400] do
          let (t, s) := MTm.gen seed (2 + i % 3) 0
          terms := terms.push t
          seed := s
        let expected := terms.toList.map leanVerdict
        let verdict := "def verdict (t : Tm) : String := match infer empty t with\n  | .ok ty _ => show .nil 0 (quote 0 ty)\n  | .err _ => \"error\"\n"
        let calls := terms.toList.map fun t => s!"(verdict {t.toWiz})"
        let main := s!"def main : IO Unit := printAll {wizList calls}\n"
        let printAll := "def printAll : List String → IO Unit\n  | .nil => IO.pure ()\n  | .cons s ss => do\n    IO.println s;\n    printAll ss\n"
        unless (expected.filter (· != "error")).length ≥ 30 do throw (IO.userError "too few well-typed terms")
        ioRun (kernel ++ "\n" ++ verdict ++ printAll ++ main) ("\n".intercalate expected ++ "\n") },
    -- P2 (soundness review of PR #61). A suspended proof never reaches these positions from
    -- a checked term (it only sits in the proof positions of `cast` and `transp`), so the
    -- values are built by hand, in both kernels.
    { name := "P2: comparing types erases suspended proofs, but not what follows an absurd (both kernels)", run := fun _ => do
        let g : Globals ZeroOneMany := {}
        let ls : List Name := ["a", "b"]
        let E : Val ZeroOneMany := .enum ls
        let pf (sp : Array (Elim ZeroOneMany)) : Val ZeroOneMany :=
          .neutral (.prf (Thunk.mk fun _ => .empty 0) [] .tt (Thunk.mk fun _ => .tt)) sp
        -- two proofs are equal, whatever was projected
        checkEq "true" (toString (sameVal g (pf #[.fst]) (pf #[.snd])))
        -- `absurd E p` is a value of `E`, not a proof: what is done with it is compared
        checkEq "false" (toString (sameVal g (pf #[.absurd E, .app (.tag ls 0)]) (pf #[.absurd E, .app (.tag ls 1)])))
        -- and what was done before the `absurd` is not
        checkEq "true" (toString (sameVal g (pf #[.fst, .absurd E, .app (.tag ls 0)]) (pf #[.snd, .absurd E, .app (.tag ls 0)])))
        -- conversion, a suspended proof against a `refl`, both under `absurd`: the Lean kernel
        -- takes any two proof heads as equal, the Wiz kernel only two of the same kind (it
        -- is the stricter one: CoreSpec §15)
        let refl : Val ZeroOneMany := .neutral (.refl E (.tag ls 0)) #[.absurd E]
        checkEq "true" (toString (conv g #[] E (pf #[.absurd E]) refl))
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let main := "def b2s : Bool → String\n  | .true => \"true\"\n  | .false => \"false\"\n" ++
          "def pf : Head := .hprf (fun _ => .vempty 0) .nil .star\n" ++
          "def ab (sp : Spine) : Spine := .sabsurd sp (.venum 2)\n" ++
          "def main : IO Unit := do\n" ++
          "  IO.println (b2s (sameVal (.vne pf (.sfst .snil)) (.vne pf (.ssnd .snil))));\n" ++
          "  IO.println (b2s (sameVal (.vne pf (.sapp (ab .snil) (.vtag 2 0))) (.vne pf (.sapp (ab .snil) (.vtag 2 1)))));\n" ++
          "  IO.println (b2s (sameVal (.vne pf (.sapp (ab (.sfst .snil)) (.vtag 2 0))) (.vne pf (.sapp (ab (.ssnd .snil)) (.vtag 2 0)))));\n" ++
          "  IO.println (b2s (conv empty (.venum 2) (.vne pf (ab .snil)) (.vne (.hrefl (.venum 2) (.vtag 2 0)) (ab .snil))))\n"
        ioRun (kernel ++ "\n" ++ main) "true\nfalse\ntrue\nfalse\n" },
    { name := "the Wiz kernel checks declarations at symbolic levels like the Lean kernel", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let decls := MTm.declSamples ++ MTm.levelPuzzles 200
        let expected := decls.map leanDeclVerdict
        unless (expected.filter (· == "ok")).length ≥ 60 do throw (IO.userError "too few valid declarations")
        unless (expected.filter (· == "error")).length ≥ 30 do throw (IO.userError "too few invalid declarations")
        let decl := "def declVerdict (ty : Tm) (v : Option Tm) : String := match checkDecl ty v with\n  | .ok _ _ => \"ok\"\n  | .err _ => \"error\"\n"
        let calls := decls.map fun (_, v, ty) =>
          s!"(declVerdict {ty.toWiz} {match v with | some v => s!"(.some {v.toWiz})" | none => ".none"})"
        let main := s!"def main : IO Unit := printAll {wizList calls}\n"
        let printAll := "def printAll : List String → IO Unit\n  | .nil => IO.pure ()\n  | .cons s ss => do\n    IO.println s;\n    printAll ss\n"
        ioRun (kernel ++ "\n" ++ decl ++ printAll ++ main) ("\n".intercalate expected ++ "\n") },
    -- D1: regularity is off in both kernels; with it on, the Wiz kernel loops too
    -- (L-2) the kernel checks the value of a `let` at 0 as an erased position, so the
    -- backend must not compile it (the frontend doesn't produce `letq` today)
    { name := "Backend.wiz erases the value of a let at 0, and keeps it at 1 and ω", run := fun _ => do
        let src ← Selfhost.compilerFiles.mapM (fun (f : String) => IO.FS.readFile f)
        let show1 (q : String) := s!"(match eraseCheck empty (.letq {q} (.enum 2) (.tag 2 0) (.tag 2 1)) (.venum 2) with\n    | .ok e => showE e\n    | .err m => String.append \"error: \" m)"
        let prog := "import IO\nimport Std\n" ++ "\n".intercalate (src.map Selfhost.strip) ++ "\n" ++
          s!"def main : IO Unit := do\n  IO.println {show1 ".qz"};\n  IO.println {show1 ".qo"};\n  IO.println {show1 ".qw"}\n"
        let kept := "(let " ++ "#0" ++ "; "
        ioRunWith prog fun out => do
          match out.splitOn "\n" with
          | z :: o :: w :: _ =>
            unless z.startsWith "(let ◾; " do throw (IO.userError s!"a let at 0 keeps its value: {z}")
            unless !o.startsWith "(let ◾; " && o.startsWith "(let " && o == w do
              throw (IO.userError s!"unexpected erasure at 1 / ω: {o} / {w} (expected like {kept}…)")
          | _ => throw (IO.userError s!"unexpected output: {out}") },
    { name := "D1 (Abel–Coquand): the Wiz kernel checks the program (and does not terminate with regularity on: its proofs are let-bound)", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let verdict := "def verdict (t : Tm) : String := match infer empty t with\n  | .ok ty _ => show .nil 0 (quote 0 ty)\n  | .err _ => \"error\"\n"
        let control := MTm.abelCoquand false
        if let .error e := infer (R := ZeroOneMany) { globals := leanGlobals () } control.toTerm then
          throw (IO.userError s!"the Lean kernel rejects the control: {e}")
        ioRun (kernel ++ "\n" ++ verdict ++ s!"def main : IO Unit := IO.println (verdict {control.toWiz})\n")
          (leanVerdict control ++ "\n")
        let loop := MTm.abelCoquand true
        -- without regularity (the default) both kernels check it
        let expected ← match infer (R := ZeroOneMany) { globals := leanGlobals () } loop.toTerm with
          | .ok (ty, _) => pure ((MTm.ofTerm (quote (leanGlobals ()) 0 ty)).map (·.pretty 0) |>.getD "?")
          | .error e => throw (IO.userError s!"the Lean kernel without regularity rejects it: {e}")
        ioRun (kernel ++ "\n" ++ verdict ++ s!"def main : IO Unit := IO.println (verdict {loop.toWiz})\n") (expected ++ "\n")
        -- with regularity (`kernelRegularity`) the Wiz kernel loops. Proofs in `cast` and
        -- `transp` are never evaluated (P2), but this program binds its proofs with `let`,
        -- and a `let`-bound proof is still evaluated (Status.md, D1: the remaining gap)
        let off := "def kernelRegularity : Bool := .false"
        unless (kernel.splitOn off).length == 2 do throw (IO.userError "kernelRegularity not found")
        let withReg := kernel.replace off "def kernelRegularity : Bool := .true"
        ioDiverges (withReg ++ "\n" ++ verdict ++ s!"def main : IO Unit := IO.println (verdict {loop.toWiz})\n") }
  ]

builtin_initialize registerGroup selfHostGroup

end Tests.Elab
