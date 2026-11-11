import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ### Stage 9g: callbacks and exported functions -/

/-- The frontend's state for a test program (with the libraries `ioRun` has). -/
def ffiState (src : String) : IO (CommandState ZeroOneMany) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else none
  let s := runFrontend (R := ZeroOneMany) src { loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure s

/-- Run `main` linked with a C file `csrc`, through both backends. -/
def ioRunC (src csrc expected : String) (fails : Option String := none) : IO Unit := do
  let s ← ffiState src
  for llvm in [false, true] do
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "helper.c") csrc
    let tc ← toolchain
    let tc := { tc with libs := tc.libs ++ [(dir / "helper.c").toString] }
    match ← Build.runGlobal tc s "main" dir llvm (timeout := some 120) with
    | .ok v => if fails.isSome then throw (IO.userError s!"expected a failure, got {v}") else checkEq expected v
    | .error e =>
      if ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1 then
        skip "no toolchain"
      else match fails with
        | some frag => unless (e.splitOn frag).length > 1 do throw (IO.userError s!"error does not mention '{frag}':\n{e}")
        | none => throw (IO.userError s!"{if llvm then "(llvm) " else ""}{e}")

/-- Build the exports of `src` as a library (`wiz build --lib`), link it with the C
program `csrc` (which includes `lib.h`), run it. Both backends. -/
def libRunC (src csrc expected : String) : IO Unit := do
  let s ← ffiState src
  for llvm in [false, true] do
    let dir ← IO.FS.createTempDir
    let tc ← toolchain
    match ← Build.build tc s "main" (dir / "lib.o") llvm true with
    | .error e =>
      if ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1 then
        skip "no toolchain"
      else throw (IO.userError s!"{if llvm then "(llvm) " else ""}{e}")
    | .ok _ =>
      IO.FS.writeFile (dir / "main.c") csrc
      let exe := (dir / "prog").toString
      let out ← IO.Process.output { cmd := tc.cc, args := #["-w", "-I", dir.toString, "-o", exe, (dir / "main.c").toString,
        (dir / "lib.o").toString] ++ tc.cflags.toArray ++ tc.gmp.toArray ++ tc.ldflags.toArray ++ tc.libs.toArray }
      unless out.exitCode == 0 do throw (IO.userError s!"cc failed: {out.stderr}")
      let r ← IO.Process.output { cmd := exe }
      unless r.exitCode == 0 do throw (IO.userError s!"the program failed ({r.exitCode}): {r.stderr}")
      checkEq expected r.stdout

def sortHelper : String := "#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef int (*cmp_fn)(void *, uint64_t, uint64_t);
static cmp_fn g_fn; static void *g_ctx;
static int cmp(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return g_fn(g_ctx, x, y) ? -1 : g_fn(g_ctx, y, x) ? 1 : 0;
}
/* sort some numbers with qsort and a Wiz comparator; the result as text */
const char *sort_some(cmp_fn lt, void *ctx) {
  static char buf[64];
  uint64_t a[] = {5, 3, 9, 1, 7, 4};
  g_fn = lt; g_ctx = ctx;
  qsort(a, 6, sizeof a[0], cmp);
  buf[0] = 0;
  for (int i = 0; i < 6; i++) sprintf(buf + strlen(buf), i ? \" %llu\" : \"%llu\", (unsigned long long)a[i]);
  return buf;
}
"

def tickHelper : String := "#include <stdint.h>
void wiz_release(void *v);
typedef void (*tick_fn)(void *, uint64_t);
static tick_fn s_fn; static void *s_ctx;
/* keep a callback (and its reference) for later */
void on_tick(tick_fn f, void *ctx) { if (s_ctx) wiz_release(s_ctx); s_fn = f; s_ctx = ctx; }
void tick(uint64_t n) { for (uint64_t i = 0; i < n; i++) if (s_ctx) s_fn(s_ctx, i); }
void forget(void) { if (s_ctx) wiz_release(s_ctx); s_ctx = 0; }
"

def tickSrc (release : Bool) : String :=
  "import IO\nextern \"on_tick\" onTick : Callback (Nat → IO Unit) → IO Unit\n" ++
  "extern \"tick\" tick : Nat → IO Unit\nextern \"forget\" forget : IO Unit\n" ++
  "def say (p : String) (n : Nat) : IO Unit := IO.println (String.append p (Nat.toString n))\n" ++
  "def main : IO Unit := do\n  onTick (say (String.append \"tick \" \"#\"));\n  IO.println \"registered\";\n" ++
  "  tick 2;\n  onTick (fun n => say \"tock \" (n + 10));\n  tick 1" ++ (if release then ";\n  forget" else "")

def callbacksGroup : Group where
  name := "callbacks"
  exercise := "Stage 9g"
  cases := [
    { name := "qsort with a Wiz comparator (a closure, borrowed for the call)", run := fun _ =>
        ioRunC ("import IO\nextern \"sort_some\" sortSome : (Nat → Nat → Bool) → String\n" ++
          "def byShift (k : Nat) (a b : Nat) : Bool := Nat.lt (Nat.mod (a + k) 10) (Nat.mod (b + k) 10)\n" ++
          "def main : IO Unit := do\n  IO.println (sortSome (fun a b => Nat.lt a b));\n" ++
          "  IO.println (sortSome (fun a b => Nat.lt b a));\n  IO.println (sortSome (byShift 3))")
          sortHelper "1 3 4 5 7 9\n9 7 5 4 3 1\n7 9 1 3 4 5\n" },
    { name := "a callback kept by C and called later, in IO, released by C", run := fun _ =>
        ioRunC (tickSrc true) tickHelper "registered\ntick #0\ntick #1\ntock 10\n" },
    { name := "a kept callback that C never releases is a leak", run := fun _ =>
        ioRunC (tickSrc false) tickHelper "" (fails := some "leaked") },
    { name := "a C function calls an exported Wiz function", run := fun _ =>
        ioRunC ("import IO\nextern \"sum_squares\" sumSquares : Nat → Nat\n" ++
          "def square (n : Nat) : Nat := n * n\nexport \"wiz_square\" square : Nat → Nat\n" ++
          "def main : IO Unit := IO.println (Nat.toString (sumSquares 10))")
          "#include <stdint.h>\nuint64_t wiz_square(uint64_t);\nuint64_t sum_squares(uint64_t n) { uint64_t s = 0; for (uint64_t i = 1; i <= n; i++) s += wiz_square(i); return s; }\n"
          "385\n" },
    { name := "a C program uses a Wiz library (wiz build --lib)", run := fun _ =>
        libRunC ("import IO\ndef fact : Nat → Nat\n  | .zero => 1\n  | .succ n => (n + 1) * fact n\n" ++
          "export \"wiz_fact\" fact\n" ++
          "def greet (who : String) : String := String.append \"hello, \" who\nexport \"wiz_greet\" greet : String → String\n" ++
          "def shout (s : String) : IO Unit := IO.println (String.append s \"!\")\nexport \"wiz_shout\" shout\n" ++
          "structure Counter where\n  total : Nat\n  steps : Nat\n" ++
          "def Counter.zero : Counter := Counter.mk 0 0\ndef Counter.add (c : Counter) (n : Nat) : Counter := Counter.mk (c.total + n) (c.steps + 1)\n" ++
          "def Counter.get (c : Counter) : Nat := c.total * 100 + c.steps\n" ++
          "export \"wiz_counter_new\" Counter.zero\nexport \"wiz_counter_add\" Counter.add\nexport \"wiz_counter_get\" Counter.get\n")
          ("#include <stdio.h>\n#include <stdlib.h>\n#include \"lib.h\"\nint main(void) {\n" ++
           "  printf(\"%llu\\n\", (unsigned long long)wiz_fact(20));\n" ++
           "  char *s = wiz_greet(\"C\"); printf(\"%s\\n\", s); free(s);\n  wiz_shout(\"from Wiz\");\n" ++
           "  wiz_val c = wiz_counter_new();\n  for (int i = 1; i <= 4; i++) c = wiz_counter_add(c, i);\n" ++
           "  wiz_retain((void *)c); printf(\"%llu\\n\", (unsigned long long)wiz_counter_get(c));\n" ++
           "  wiz_release((void *)c);\n  printf(\"live %ld\\n\", wiz_live_objects());\n  return 0;\n}\n")
          "2432902008176640000\nhello, C\nfrom Wiz!\n1004\nlive 0\n" },
    { name := "a callback in IO needs a foreign function in IO", run := fun _ =>
        ioFails "import IO\nextern \"f\" f : (Nat → IO Unit) → Nat" "must be in IO" },
    { name := "only closed, marshallable functions are exported", run := fun _ =>
        ioFails "import IO\ndef app (f : Nat → Nat) : Nat := f 1\nexport \"wiz_app\" app" "exported function" },
    { name := "an export's type is the definition's", run := fun _ =>
        ioFails "import IO\ndef two : Nat := 2\nexport \"wiz_two\" two : String" "not String" }
  ]

initialize registerGroup callbacksGroup

end Tests.Elab
