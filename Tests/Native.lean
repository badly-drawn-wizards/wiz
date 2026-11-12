import Wiz
import Tests.Harness
import Tests.Elab
import Grail

/-!
# `native_refl` and `--trust-native` (stage 27a)

The group `native`: closed equations decided by running them, only with the flag, with
an axiom per use that `#print axioms` lists together with the native implementations
the run can reach; never in the library; and cache entries that never cross the flag.
-/

open Wiz

set_option compiler.extract_closed false

namespace Tests.Native

/-- Every message of `input` (`severity: text`), with `lib/`'s Prelude, Word, Logic, …
importable, with or without `--trust-native`. -/
def msgs (input : String) (trust : Bool := true) : IO (List String) := do
  let loader ← Elab.preludeLoader
  let s := runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule, trustNative := trust }
  pure (s.messages.toList.map fun m =>
    s!"{match m.severity with | .error => "error" | .warning => "warning" | .info => "info"}: {m.text}")

def has (ms : List String) (fragment : String) : Bool := ms.any fun m => (m.splitOn fragment).length > 1

def expect (ms : List String) (fragment : String) : IO Unit :=
  unless has ms fragment do throw (IO.userError s!"no message mentions '{fragment}':\n{"\n".intercalate ms}")

def noErrors (ms : List String) : IO Unit := do
  let errs := ms.filter (·.startsWith "error")
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs}")

def sumTo : String :=
  "import Prelude\ndef sumTo : Nat → Nat\n  | .zero => 0\n  | .succ n => Nat.add (Nat.succ n) (sumTo n)\n"

/-- A 16-bit linear congruential generator, iterated: `n` steps of word arithmetic. The
kernel takes seconds for this many steps (it unfolds `UIntN`'s model on every step);
the interpreter a fraction of one. -/
def lcg : String :=
  "import Prelude\nimport Word\n" ++
  "def step (x : UIntN 16) : UIntN 16 := UIntN.add (UIntN.mul x (UIntN.ofNat 16 25173)) (UIntN.ofNat 16 13849)\n" ++
  "def iter : Nat → UIntN 16 → UIntN 16\n  | .zero, x => x\n  | .succ k, x => iter k (step x)\n"

/-- The value `iter n 1` computes, by Lean's arithmetic. -/
def lcgValue (n : Nat) : Nat := Id.run do
  let mut x := 1
  for _ in [0:n] do x := (x * 25173 + 13849) % 65536
  pure x

/-- Elaborate `input` with `M` importable as `modSrc`, through `store`. -/
def viaStore (store : Cache.Store ZeroOneMany) (modSrc input : String) (trust : Bool) : IO (List String) := do
  let pre ← Elab.preludeLoader
  let loader (m : Name) := if m == "M" then some modSrc else pre m
  let (s, _) ← Cache.elaborateWith store input { loader, trustedModule := fun m => m != "" && m != "M", trustNative := trust } 0
  pure (s.messages.toList.map fun m =>
    s!"{match m.severity with | .error => "error" | .warning => "warning" | .info => "info"}: {m.text}")

/-- Every `.wiz` file under `dir`. -/
partial def wizFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let mut out := []
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← wizFiles e.path)
    else if e.path.extension == some "wiz" then out := e.path :: out
  pure out

def group : Group where
  name := "native"
  exercise := "—"
  cases := [
    { name := "accepted with --trust-native: numbers, lists, a declaration that uses it", run := fun _ => do
        let ms ← msgs (sumTo ++
          "def s100 : sumTo 100 = 5050 := native_refl\n" ++
          "def l : List.cons (sumTo 3) List.nil = List.cons 6 List.nil := native_refl\n" ++
          "def both : sumTo 20 = Nat.add (sumTo 19) 20 := native_refl\n" ++
          "def use : sumTo 100 = 5050 := s100\n")
        noErrors ms
        expect ms "s100 is accepted on the strength of native evaluation" },
    { name := "word arithmetic, many steps (slow for the kernel, fast natively)", run := fun _ => do
        let ms ← msgs (lcg ++ s!"def it : iter 20000 (UIntN.ofNat 16 1) = UIntN.ofNat 16 {lcgValue 20000} := native_refl\n#print axioms it\n")
        noErrors ms
        expect ms "'it' depends on axioms: [it.native✝" },
    { name := "V1: the OLED demo's units at full width (examples/hdl-verified-native.wiz)", run := fun _ => do
        let ms ← msgs (← IO.FS.readFile "examples/hdl-verified-native.wiz")
        noErrors ms
        expect ms "root_full is accepted on the strength of native evaluation"
        expect ms "smin_full is accepted on the strength of native evaluation"
        expect ms "'smin_full' depends on axioms: [smin_full.native✝" },
    { name := "rejected without --trust-native", run := fun _ => do
        let ms ← msgs (sumTo ++ "def s : sumTo 4 = 10 := native_refl\n") (trust := false)
        expect ms "error: native evaluation is not enabled"
        expect ms "--trust-native" },
    { name := "a false equation is refuted", run := fun _ => do
        let ms ← msgs (sumTo ++ "def bad : sumTo 10 = 54 := native_refl\n")
        expect ms "error: native_refl: native evaluation refutes it: the left-hand side is 55, the right-hand side 54"
        let ms ← msgs (lcg ++ s!"def bad : iter 1000 (UIntN.ofNat 16 1) = UIntN.ofNat 16 {lcgValue 1000 + 1} := native_refl\n")
        expect ms "error: native_refl: native evaluation refutes it" },
    { name := "only first-order data: functions and types are refused", run := fun _ => do
        let ms ← msgs (sumTo ++ "def f : (fun (x : Nat) => x) = (fun (x : Nat) => sumTo x) := native_refl\n")
        expect ms "error: native_refl: native_refl compares first-order data; Nat → Nat is not"
        let ms ← msgs (sumTo ++ "def t : Nat = Nat := native_refl\n")
        expect ms "is not (a function, codata or a type)"
        -- a field of quantity 0 is not there at run time: it can't be compared
        let ms ← msgs (sumTo ++ "inductive E where\n  | mk (0 n : Nat)\ndef e : E.mk 1 = E.mk 1 := native_refl\n")
        expect ms "quantity 0" },
    { name := "only as the whole body of a closed definition", run := fun _ => do
        expect (← msgs (sumTo ++ "def p (n : Nat) : sumTo n = sumTo n := native_refl\n")) "native_refl proves a closed equation"
        expect (← msgs (sumTo ++ "def q : sumTo 3 = 6 := (native_refl : sumTo 3 = 6)\n")) "native_refl can only be the whole body of a definition"
        expect (← msgs (sumTo ++ "def r : Nat := native_refl\n")) "native_refl proves an equation `a = b`" },
    { name := "#print axioms: the native axiom, also of what uses it", run := fun _ => do
        let ms ← msgs (sumTo ++ "def s100 : sumTo 100 = 5050 := native_refl\ndef use : sumTo 100 = 5050 := s100\n" ++
          "#print axioms s100\n#print axioms use\n#print axioms sumTo\n")
        noErrors ms
        expect ms "info: 's100' depends on axioms: [s100.native✝]"
        expect ms "info: 'use' depends on axioms: [s100.native✝]"
        expect ms "native_refl, --trust-native"
        expect ms "info: 'sumTo' does not depend on any axioms" },
    { name := "a wrong implemented_by proves a false equation, and #print axioms names it", run := fun _ => do
        -- the adversary: `f`'s compiled code is `g`, which disagrees with it. The kernel
        -- refutes `f 1 = 3` (`refl` fails); native evaluation runs `g` and accepts it.
        -- That is what `--trust-native` trusts, and `#print axioms` says so.
        let src := sumTo ++ "def f (n : Nat) : Nat := Nat.succ n\ndef g (n : Nat) : Nat := Nat.add n 2\n" ++
          "attribute [implemented_by g] f\n" ++
          "def lie : f 1 = 3 := native_refl\n#print axioms lie\n"
        let ms ← msgs src
        noErrors ms
        expect ms "info: 'lie' depends on axioms: [lie.native✝, native f := g]"
        -- the kernel alone refutes it
        let ms ← msgs (sumTo ++ "def f (n : Nat) : Nat := Nat.succ n\ndef g (n : Nat) : Nat := Nat.add n 2\n" ++
          "attribute [implemented_by g] f\ndef lie : f 1 = 3 := refl 3\n")
        check (has ms "error") s!"the kernel accepted f 1 = 3: {ms}"
        -- and what the implementation's code reaches is listed too: here `g` is itself
        -- implemented by `h` (the run executes `h`)
        let ms ← msgs (sumTo ++ "def f (n : Nat) : Nat := Nat.succ n\ndef g (n : Nat) : Nat := Nat.succ n\n" ++
          "def h (n : Nat) : Nat := Nat.add n 2\nattribute [implemented_by h] g\nattribute [implemented_by g] f\n" ++
          "def lie : f 1 = 3 := native_refl\n#print axioms lie\n")
        noErrors ms
        expect ms "native g := h"
        -- (t1-review L2) a three-link chain a1 → a2 → a3 → a4, and what the last one uses
        let ms ← msgs (sumTo ++ "axiom k : Nat\ndef a1 (n : Nat) : Nat := n\ndef a2 (n : Nat) : Nat := n\n" ++
          "def a3 (n : Nat) : Nat := n\ndef a4 (n : Nat) : Nat := Nat.add n k\n" ++
          "attribute [implemented_by a4] a3\nattribute [implemented_by a3] a2\nattribute [implemented_by a2] a1\n" ++
          "def u : Nat := a1 2\n#print axioms u\n")
        noErrors ms
        expect ms "native a1 := a2"
        expect ms "native a2 := a3"
        expect ms "native a3 := a4"
        check (has ms ", k]" || has ms ", k," || has ms "[k,") s!"the last link's axiom k is not listed: {ms}" },
    { name := "a foreign constant has no value here (trust-review N1)", run := fun _ => do
        -- `getpid` is not 0: reading a foreign constant as 0 would prove `pid = 0`
        let ms ← msgs (sumTo ++ "extern \"getpid\" pid : Nat\ndef pidIsZero : pid = 0 := native_refl\n")
        expect ms "error: native_refl: native evaluation failed: pid is a foreign constant"
        let ms ← msgs (sumTo ++ "extern \"wiz_flag\" flag : Bool\ndef f : flag = Bool.false := native_refl\n")
        expect ms "is a foreign constant" },
    { name := "a huge power is an error, not a panic (trust-review N2)", run := fun _ => do
        let ms ← msgs (sumTo ++ "def huge : Nat.beq (Nat.pow 2 (Nat.pow 2 40)) 0 = Bool.false := native_refl\n")
        expect ms "nat.pow: the result would have more than" },
    { name := "an erased proof field is built and checked; an erased data field is refused (AB1)", run := fun _ => do
        -- the shape of a word with its range proof (PR #145)
        let small := sumTo ++ "inductive Small where\n  | mk (n : Nat) (0 h : Nat.lt n 10 = .true)\n" ++
          "def three : Small := Small.mk 3 (refl Bool.true)\n"
        let ms ← msgs (small ++ "def s : three = Small.mk (sumTo 2) (refl Bool.true) := native_refl\n" ++
          "def l : List.cons three List.nil = List.cons three List.nil := native_refl\n")
        noErrors ms
        let ms ← msgs (small ++ "def s : three = Small.mk 4 (refl Bool.true) := native_refl\n")
        expect ms "native evaluation refutes it"
        -- an erased field that is data: the two sides could differ there
        let ms ← msgs (sumTo ++ "inductive E where\n  | mk (m : Nat) (0 n : Nat)\ndef e : E.mk 1 2 = E.mk 1 3 := native_refl\n")
        expect ms "quantity 0" },
    { name := "a partial definition's implementation is not run", run := fun _ => do
        let ms ← msgs (sumTo ++ "partial def loop (n : Nat) : Nat := loop n\ndef l : loop 0 = 0 := native_refl\n")
        expect ms "reaches the partial definition loop" },
    { name := "the step limit (--native-fuel) ends a long run with a message", run := fun _ => do
        let loader ← Elab.preludeLoader
        let s := runFrontend (R := ZeroOneMany) (sumTo ++ "def s : sumTo 100000 = 5000050000 := native_refl\n")
          { loader, trustedModule := Tests.libModule, trustNative := true, nativeFuel := 1000 }
        let ms := s.messages.toList.map (·.text)
        expect ms "native evaluation did not finish within 1000 steps (raise the limit with --native-fuel N)" },
    { name := "the flags: wiz's and grail's toolchain take and pass on --trust-native", run := fun _ => do
        let (t, rest) := ({} : Toolchain).parseFlags ["--trust-native", "--native-fuel", "77", "check", "f.wiz"]
        check t.trustNative "--trust-native not taken"
        checkEq (some 77) t.nativeFuel
        checkEq ["check", "f.wiz"] rest
        check (t.toFlags.contains "--trust-native") "toFlags drops --trust-native"
        let (t', _) := ({} : Toolchain).parseFlags t.toFlags
        check (t'.trustNative && t'.nativeFuel == some 77) "toFlags does not round-trip"
        let (u, _) := ({} : Toolchain).parseFlags ["check", "f.wiz"]
        check (!u.trustNative && !(u.toFlags.contains "--trust-native")) "--trust-native is on by default"
        -- grail: a check with the flag is another job than one without
        let src := sumTo ++ "def s : sumTo 4 = 10 := native_refl\n"
        let a ← Grail.load {} ["lib"] 0 src
        let b ← Grail.load { trustNative := true } ["lib"] 0 src
        check (a.key != b.key) "grail's check key ignores --trust-native"
        check (b.init.trustNative && !a.init.trustNative) "grail does not pass --trust-native to the elaborator" },
    { name := "the cache: never replayed across the flag, re-decided when what it ran changes", run := fun _ => do
        let store ← Cache.Store.memory (R := ZeroOneMany)
        let modOk := "import Prelude\ndef f (n : Nat) : Nat := Nat.add n n\n"
        let modBad := "import Prelude\ndef f (n : Nat) : Nat := Nat.add n 1\n"
        let main := "import M\ndef x : f 2 = 4 := native_refl\n#print axioms x\n"
        noErrors (← viaStore store modOk main true)
        -- the same text without the flag: the acceptance is not replayed
        expect (← viaStore store modOk main false) "error: native evaluation is not enabled"
        -- and with it again: the error is not replayed either
        noErrors (← viaStore store modOk main true)
        -- the imported definition changed (so the code that ran): decided again
        expect (← viaStore store modBad main true) "native evaluation refutes it" },
    { name := "lib/ never uses native_refl", run := fun _ => do
        -- (lib/ is checked without --trust-native everywhere, so a use would be an error;
        -- the grep also catches a macro or deriver that would build one)
        for f in ← wizFiles "lib" do
          let src ← IO.FS.readFile f
          check ((src.splitOn "native_refl").length == 1 && (src.splitOn "nativeRefl").length == 1)
            s!"{f} mentions native_refl" },
    { name := "no library declaration depends on a native axiom", run := fun _ => do
        let files ← wizFiles "lib"
        let mods := files.filterMap fun f => do
          let cs := (f.toString.toList.drop 4)
          pure ((String.ofList (cs.take (cs.length - 4))).replace "/" ".")
        let input := String.join (mods.map (s!"import {·}\n"))
        let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := ← Elab.libLoader }
        let errs := s.messages.filter (·.severity == .error)
        unless errs.isEmpty do throw (IO.userError s!"the library has errors: {errs.toList.map (·.text)}")
        check (s.globals.order.size > 1000) s!"only {s.globals.order.size} library declarations"
        for n in s.globals.order do
          if (s.globals.axiomsOf n).any (·.endsWith ".native✝") then
            throw (IO.userError s!"{n} depends on a native_refl axiom") }
  ]

def groups : List Group := [group]

end Tests.Native
