import Tests.Elab

/-!
# Elaborator bug fixes (agent/elab-bugs)

Regression tests for elaborator bugs that other work ran into and worked around: each
case is a minimal reproducer.
-/

open Wiz

set_option compiler.extract_closed false

namespace Tests.ElabFix

open Tests.Elab

/-- The peak resident set size of this process, in MB (Linux: `VmHWM` in
`/proc/self/status`); the cases run in a child process each, so this is the case's. -/
def peakMB : IO Nat := do
  let s ← IO.FS.readFile "/proc/self/status"
  for l in s.splitOn "\n" do
    if l.startsWith "VmHWM:" then
      let kb := ((l.drop 6).trimAscii.toString.takeWhile Char.isDigit).toNat!
      return kb / 1024
  throw (IO.userError "no VmHWM in /proc/self/status")

/-- `okLib`, and the case stays under `mb` megabytes. -/
def okLibBounded (mb : Nat) (input : String) (infos : List String := []) : IO Unit := do
  okLib input infos
  let peak ← peakMB
  unless peak ≤ mb do throw (IO.userError s!"used {peak} MB (bound: {mb} MB)")

/-- (13b) The messages of `input`, with `lib/Prelude.wiz` and the module `Priv` (`priv`)
importable: privacy is per module. -/
def runPriv (priv input : String) : IO (Array String × Array String) := do
  let lib ← preludeLoader
  let s := runFrontend (R := ZeroOneMany) input { loader := fun m => if m == "Priv" then some priv else lib m }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  pure (errs, (s.messages.filter (·.severity != .error)).map (·.text))

def okPriv (priv input : String) (infos : List String := []) : IO Unit := do
  let (errs, msgs) ← runPriv priv input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr msgs.toList).pretty

def failsPriv (priv input fragment : String) : IO Unit := do
  let (errs, _) ← runPriv priv input
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

/-- A module with private names: a definition, a structure with a private constructor
(and a smart constructor), a private structure. -/
def privMod : String :=
  "import Prelude\nprivate def secret : Nat := 42\ndef reveal : Nat := secret\n" ++
  "structure Pos (A : Type) where\n  private mk ::\n  val : A\n" ++
  "def Pos.one : Pos Nat := Pos.mk 1\ndef Pos.dbl (p : Pos Nat) : Pos Nat := Pos.mk (Nat.add p.val p.val)\n" ++
  "def Pos.pair (p : Pos Nat) : Nat × Nat := (p.val, p.1)\n" ++
  "private structure Hidden where\n  x : Nat\n"

def group : Group where
  name := "elabfix"
  exercise := "elaborator bugs"
  cases := [
    { name := "x - 55296 with x stuck doesn't unfold the numeral (memory bound)", run := fun _ =>
        okLibBounded 1000 ("import Prelude\ndef f (hi : Nat) : Nat := (hi - 55296) * 2 + 1\n" ++
          "def s (hi lo : Nat) : Nat := 65536 + (hi - 55296) * 1024 + (lo - 56320)\n" ++
          "#eval f 55300\n#eval s 55296 56320") ["9", "65536"] },
    { name := "x - n with x stuck still computes once x is known", run := fun _ =>
        okLib ("import Prelude\ndef f (hi : Nat) : Nat := (hi - 55296) * 2 + 1\n" ++
          "def t : f 55300 = 9 := refl 9\n" ++
          "def u (n : Nat) : Nat.succ (Nat.succ n) - 1 = Nat.succ n := refl (Nat.succ n)\n" ++
          "def v (n : Nat) : n - 3 = n - 3 := refl (n - 3)") },
    { name := "holes in an equation-style definition's parameter types are solved", run := fun _ =>
        okLib ("import Prelude\ndef g {A : Type} (x : A) : A := x\n" ++
          "def f (n : Nat) (h : (x : Nat) → g x = x) : Bool → Nat\n  | .true => n\n  | .false => n\n" ++
          "def f2 (n : Nat) (h : (x : Nat) → g x = x) : (b : Bool) → g n = n → Nat\n" ++
          "  | .true, e => n\n  | .false, e => n") },
    { name := "@f on the recursive call of an equation-style definition", run := fun _ =>
        okLib ("import Prelude\ndef len {A : Type} : List A → Nat\n  | .nil => 0\n" ++
          "  | .cons _ xs => @len A xs + 1\n" ++
          "def len2 {A : Type} : List A → Nat\n  | .nil => 0\n  | .cons _ xs => @len2 _ xs + 1\n" ++
          "#eval len2 (List.cons 1 (List.cons 2 List.nil))") ["2"] },
    { name := "@f on a recursive call must pass the implicit parameters unchanged", run := fun _ =>
        failsLib ("import Prelude\ndef len {A : Type} : List A → Nat\n  | .nil => 0\n" ++
          "  | .cons _ xs => @len Nat xs + 1") "must pass the parameter A unchanged" },
    { name := ".c constructors inside tuple components get the expected type", run := fun _ =>
        okLib ("import Prelude\ndef p : Option (List Nat × Nat) := .some (.nil, 3)\n" ++
          "def q : Option (Nat × Bool × List Nat) := .some (1, .true, .cons 2 .nil)") },
    { name := "match on an expression generalises the hypotheses about it", run := fun _ =>
        okLib ("import Prelude\ndef t (n : Nat) (h : Nat.pred n = 0) : Nat :=\n" ++
          "  match Nat.pred n, h with\n  | .zero, _ => 0\n  | .succ m, h' => absurd h'.1") },
    { name := "(x).f y is a field access, like x.f y", run := fun _ =>
        okLib ("import Prelude\ndef a (x y : Nat) : Nat := x.sub y\ndef b (x y : Nat) : Nat := (x).sub y\n" ++
          "def c (x y : Nat) : Nat := Nat.add (x).succ y\n#eval b 5 2\n#eval c 1 1") ["3", "3"] },
    { name := "an equation whose sides have holes solved later (eq-pending-metas)", run := fun _ =>
        okLib ("import Word\n" ++
          "def wraps : (UIntN.add (U8.ofNat 250) (U8.ofNat 10)).toNat = 4 := refl 4\n" ++
          "def w {ω n : Nat} (a : UIntN n) : Nat := n\n" ++
          "def t : w (U8.ofNat 3) = 8 := refl 8\n" ++
          "def t' : w (U8.ofNat 3) = 8 := rfl") },
    { name := "an instance problem in a definition's type is solved before its body", run := fun _ =>
        okLib ("import Prelude\nclass C (A : Type) where\n  f : A → Nat\n" ++
          "instance : C Bool := C.mk (fun _ => 3)\ndef t5 : C.f Bool.true = 3 := refl 3") },
    { name := "a definition's implicit widths are solved before its body (elab-solve-type-before-body)", run := fun _ =>
        okLibs "import BitVec\ndef t : (BitVec.add (BitVec.ofNat 8 200) (BitVec.ofNat 8 100)).toNat = 44 := refl 44" },
    { name := "the unifier meets an equation with its computed form (unify-computed-equations)", run := fun _ =>
        okOptic ("import Optic\n" ++
          "def t3 (x : Nat) (xs ys : List Nat) (h : xs = ys) : List.cons x xs = List.cons x ys :=\n" ++
          "  Optic.congrArg (List.cons x) h\n" ++
          "def t4 (a b : Nat) (h : a = b) : Nat.succ a = Nat.succ b := Optic.congrArg Nat.succ h") },
    -- agent/elab-stretch
    { name := "numerals and notation in class field types (numerals-in-class-decls)", run := fun _ =>
        okLib ("import Prelude\ninductive HwTy where\n  | bits (n : Nat)\nclass Hw (r : HwTy → Type) where\n" ++
          "  eq : {n : Nat} → r (HwTy.bits n) → r (HwTy.bits n) → r (HwTy.bits 1)\n" ++
          "  cat : {m n : Nat} → r (HwTy.bits m) → r (HwTy.bits n) → r (HwTy.bits (m + n))") },
    { name := "structure projections as functions (projection-functions)", run := fun _ =>
        okLib ("import Prelude\nstructure BV (n : Nat) where\n  toNat : Nat\n  0 ok : Nat.lt toNat 100 = .true\n" ++
          "structure P (A : Type) where\n  x : A\n  y : List A\n" ++
          "def lm {A B : Type} (f : A → B) : List A → List B\n  | .nil => .nil\n  | .cons x xs => .cons (f x) (lm f xs)\n" ++
          "def m (vs : List (BV 8)) : List Nat := lm BV.toNat vs\n" ++
          "structure Sg where\n  n : Nat\n  v : BV n\ndef h (s : Sg) : BV (Sg.n s) := Sg.v s\n" ++
          "def f (v : BV 8) : Nat := v.toNat\n" ++
          "#eval P.y (P.mk 1 (List.cons 2 List.nil))\n#eval lm P.x (List.cons (P.mk 3 List.nil) List.nil)")
          [".cons 2 .nil", ".cons 3 .nil"] },
    { name := "erased fields get no projection function", run := fun _ =>
        failsLib ("import Prelude\nstructure BV (n : Nat) where\n  toNat : Nat\n  0 ok : Nat.lt toNat 100 = .true\n" ++
          "def g := BV.ok") "no field" },
    { name := "trailing instance arguments are inserted (trailing-instance-args)", run := fun _ =>
        okLib ("import Prelude\nclass BitPack (A : Type) where\n  width : Nat\ninstance : BitPack Bool := BitPack.mk 1\n" ++
          "def bitWidth (0 A : Type) [BitPack A] : Nat := @BitPack.width A _\n" ++
          "def two : Nat := bitWidth Bool + bitWidth Bool\ndef w3 := bitWidth Bool\n" ++
          "#eval two\n#eval @BitPack.width Bool _\n#eval w3") ["2", "1", "1"] },
    { name := "constructor parameters from the expected type (ctor-params-from-expected-type)", run := fun _ =>
        okLib ("import Prelude\ninductive Fin (n : Nat) where\n  | mk (val : Nat) (0 isLt : Nat.lt val n = .true)\n" ++
          "def Fin.succ {0 n : Nat} : Fin n → Fin (Nat.succ n)\n  | .mk i h => .mk (Nat.succ i) h\n" ++
          "def three : Fin 5 := Fin.mk 3 rfl\ndef four : Fin 5 := .mk 4 rfl") },
    { name := "lambda arguments wait for the arguments that fix their domains (elab-postpone-lambdas)", run := fun _ =>
        okLib ("import Prelude\n" ++
          "def zipWith3 {A B C D : Type} (f : A → B → C → D) : List A → List B → List C → List D\n" ++
          "  | .cons a as, .cons b bs, .cons c cs => .cons (f a b c) (zipWith3 f as bs cs)\n  | _, _, _ => .nil\n" ++
          "def sel (c : List Bool) (t e : List Nat) : List Nat := zipWith3 (fun b x y => match b with | .true => x | .false => y) c t e\n" ++
          "def sel2 (c : List Bool) (t e : List Nat) := zipWith3 (fun b x y => match b with | .true => x | .false => y) c t e\n" ++
          "def mealy {S I O : Type} (f : S → I → S × O) : S → List I → List O\n  | _, .nil => .nil\n" ++
          "  | s, .cons i is => .cons (f s i).2 (mealy f (f s i).1 is)\n" ++
          "def cnt (inp : List Bool) : List Nat := mealy (fun s i => match i with | .true => (Nat.succ s, s) | .false => (s, s)) 0 inp\n" ++
          "#eval sel2 (List.cons .true (List.cons .false .nil)) (List.cons 1 (List.cons 2 .nil)) (List.cons 3 (List.cons 4 .nil))\n" ++
          "#eval cnt (List.cons .true (List.cons .true .nil))")
          [".cons 1 (.cons 4 .nil)", ".cons 0 (.cons 1 .nil)"] },
    { name := "a constructor with a pair argument in a match branch (placeholders solved directly)", run := fun _ =>
        okLib ("import Prelude\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A .zero\n" ++
          "  | cons {0 n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)\n" ++
          "def zip {A B : Type} {n : Nat} : Vec A n → Vec B n → Vec (A × B) n\n" ++
          "  | .nil, .nil => .nil\n  | .cons a as, .cons b bs => .cons (a, b) (zip as bs)") },
    { name := "an argument naming a tuple pattern's component, before a postponed lambda (no scope escape)", run := fun _ =>
        okLib ("import Prelude\nstructure P where\n  a : Nat\n  b : Nat\n" ++
          "def app {S B : Type} (s : S) (k : S → B) : B := k s\n" ++
          "def f (p : P) : Nat := match p with\n  | (x, y, _) => app x (fun x => Nat.add x y)\n" ++
          "#eval f (P.mk 2 3)") ["5"] },
    { name := "named arguments: explicit, implicit and instance parameters (13a)", run := fun _ =>
        okLib ("import Prelude\nclass BitPack (A : Type) where\n  width : Nat\ninstance : BitPack Bool := BitPack.mk 1\n" ++
          "def bitWidth (0 A : Type) [BitPack A] : Nat := BitPack.width (A := A)\n" ++
          "def sub (a b : Nat) : Nat := Nat.sub a b\ndef ident {A : Type} (x : A) : A := x\n" ++
          "def pick {A : Type} (x y : A) (b : Bool) : A := match b with\n  | .true => x\n  | .false => y\n" ++
          "#eval bitWidth Bool\n#eval sub (b := 1) 5\n#eval sub (a := 7) (b := 2)\n#eval ident (A := Nat) 3\n" ++
          "#eval @ident (A := Nat) 4\n#eval @ident (x := 5) Nat\n#eval pick (b := .false) 1 2\n" ++
          "#eval BitPack.width (A := Bool)\n#eval @BitPack.width (A := Bool) _\ndef n : Nat := sub (b := 1) (Nat.succ 5)\n#eval n")
          ["1", "4", "5", "3", "4", "5", "2", "1", "1", "5"] },
    { name := "named arguments: errors (13a)", run := fun _ => do
        failsLib "import Prelude\ndef sub (a b : Nat) : Nat := Nat.sub a b\ndef x := sub (c := 1) 2" "no parameter named 'c'"
        failsLib "import Prelude\ndef sub (a b : Nat) : Nat := Nat.sub a b\ndef x := sub (b := 1) (b := 2)" "already given"
        failsLib "import Prelude\ndef sub (a b : Nat) : Nat := Nat.sub a b\ndef x : Nat := sub (b := 1)" "has no argument"
        failsLib "import Prelude\ndef x : Nat := (b := 1)" "only allowed as an argument" },
    { name := "private names are visible only in their module (13b)", run := fun _ => do
        okPriv privMod "import Priv\n#eval reveal\n#eval Pos.dbl Pos.one\n#eval (Pos.dbl Pos.one).val\n#eval Pos.val Pos.one\n#eval Pos.pair Pos.one"
          ["42", "(2, ())", "2", "1", "(1, 1)"]
        failsPriv privMod "import Priv\ndef x : Nat := secret" "'secret' is private to module Priv"
        failsPriv privMod "import Priv\ndef x : Nat := Hidden.mk 1" "private to module Priv"
        -- in their own module (the main file) private names are ordinary
        okPriv "" (privMod ++ "#eval secret\n#eval (Pos.mk 3 : Pos Nat).val\ndef h : Hidden := Hidden.mk 2\n#eval h.x") ["42", "3", "2"] },
    { name := "a private constructor: no forging from another module (13b)", run := fun _ => do
        failsPriv privMod "import Priv\ndef x : Pos Nat := Pos.mk 5" "'Pos.mk' is private to module Priv"
        failsPriv privMod "import Priv\ndef x : Pos Nat := @Pos.mk Nat 5" "private"
        -- the type is opaque here: no tuple, no look-alike structure
        failsPriv privMod "import Priv\ndef x : Pos Nat := (5, ())" "Pos"
        failsPriv privMod "import Priv\nstructure Fake (A : Type) where\n  val : A\ndef x : Pos Nat := Fake.mk 5" "mismatch"
        failsPriv privMod "import Priv\ndef x (p : Pos Nat) : Nat := p.1" "cannot project" },
    { name := "`private def` right after a structure (13b)", run := fun _ =>
        okLib "import Prelude\nstructure P where\n  x : Nat\nprivate def q : P := P.mk 1\n#eval q.x" ["1"] }
  ]

end Tests.ElabFix
