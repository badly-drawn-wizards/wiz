import Wiz
import Tests.Harness

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def run (input : String) : Array String :=
  let s := runFrontend (R := ZeroOneMany) input
  s.messages.map fun m => m.render input

def errors (input : String) : Array String :=
  let s := runFrontend (R := ZeroOneMany) input
  (s.messages.filter (·.severity == .error)).map fun m => m.render input

/-- No errors, and the info messages (from `#check`/`#reduce`) are exactly `infos`,
without their positions. -/
def ok (input : String) (infos : List String := []) : IO Unit := do
  let errs := errors input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let got := (runFrontend (R := ZeroOneMany) input).messages.toList.map (·.text)
  checkEq (repr infos).pretty (repr got).pretty

/-- Exactly one error, mentioning `fragment`. -/
def fails (input : String) (fragment : String) : IO Unit := do
  let errs := errors input
  unless errs.size == 1 do
    throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

def prelude : String := "
def id {A : Type} (x : A) : A := x
def const {A B : Type} (x : A) (y : B) : A := x
def comp {A B C : Type} (g : B → C) (f : A → B) (x : A) : C := g (f x)
"

def church : String := "
def Nat : Type 1 := (A : Type) → (A → A) → A → A
def zero : Nat := fun A s z => z
def succ (n : Nat) : Nat := fun A s z => s (n A s z)
def add (m n : Nat) : Nat := fun A s z => m A s (n A s z)
def two : Nat := succ (succ zero)
def four : Nat := add two two
def Leibniz {A : Type 1} (x y : A) : Type 2 := (P : A → Type 1) → P x → P y
def lrefl {A : Type 1} (x : A) : Leibniz x x := fun P px => px
"

def group : Group where
  name := "elab"
  exercise := "Exercises 3.1–3.9"
  cases := [
    { name := "implicit arguments are inserted", run := fun _ =>
        ok (prelude ++ "def t (A : Type) (a : A) : A := id a") },
    { name := "#check shows implicit binders", run := fun _ =>
        ok (prelude ++ "#check id") ["id : {A : Type} → A → A"] },
    { name := "@ makes implicits explicit", run := fun _ =>
        ok (prelude ++ "def t (A : Type) (a : A) : A := @id A a") },
    { name := "implicit lambda insertion", run := fun _ =>
        ok "def id2 : {A : Type} → A → A := fun x => x" },
    { name := "explicit implicit lambda", run := fun _ =>
        ok "def id3 : {A : Type} → A → A := fun {A} x => x" },
    { name := "return type inferred", run := fun _ =>
        ok "def ap (A B : Type) (f : A → B) (a : A) := f a\n#check ap"
          ["ap : (A : Type) → (B : Type) → (A → B) → A → B"] },
    { name := "fun binder types inferred from use", run := fun _ =>
        ok (prelude ++ "def k (A : Type) := comp (fun (x : A) => x) (fun y => y)\n#check k")
          ["k : (A : Type) → A → A"] },
    { name := "holes solved by unification", run := fun _ =>
        ok (prelude ++ "def t (A : Type) (a : A) : A := @id _ a") },
    { name := "unsolvable hole is reported", run := fun _ =>
        fails "def x : Type := _" "could not infer" },
    { name := "Church numerals and #reduce", run := fun _ =>
        ok (church ++ "#reduce add two two") ["fun A s z => s (s (s (s z)))"] },
    { name := "2 + 2 = 4 by refl, with implicit A", run := fun _ =>
        ok (church ++ "def p : Leibniz (add two two) four := lrefl four") },
    { name := "2 + 2 = 2 is a type mismatch", run := fun _ =>
        fails (church ++ "def p : Leibniz (add two two) two := lrefl two") "type mismatch" },
    { name := "type mismatch message", run := fun _ =>
        fails "def bad (A : Type) (a : A) : Type := a" "type mismatch" },
    { name := "unknown identifier", run := fun _ =>
        fails "def bad : Type := Nope" "unknown identifier 'Nope'" },
    { name := "no recursion yet", run := fun _ =>
        fails "def loop (A : Type) : A := loop A" "unknown identifier 'loop'" },
    { name := "linearity is checked by the kernel", run := fun _ =>
        fails "def dup {A : Type} (f : A → A → A) (1 x : A) : A := f x x" "quantity" },
    { name := "erased implicit used at runtime", run := fun _ =>
        fails "def leak {A : Type} (x : A) : Type := A" "quantity" },
    { name := "binder quantity must match the expected type", run := fun _ =>
        fails "def f : (1 x : Type) → Type := fun (ω x) => x" "quantity" },
    { name := "linear identity checks", run := fun _ =>
        ok "def lid {A : Type} (1 x : A) : A := x" },
    { name := "self-application escapes the hole's scope", run := fun _ =>
        fails "def w (A : Type) := fun f => f f" "scope" },
    { name := "occurs check", run := fun _ =>
        fails "def o (A : Type) (g : _ → A) := g g" "occurs" },
    { name := "not a function", run := fun _ =>
        fails "def bad (A : Type) (a : A) : A := a a" "function expected" },
    { name := "let", run := fun _ =>
        ok (prelude ++ "def t (A : Type) (a : A) : A :=\n  let b := id a\n  id b") },
    { name := "a parse error doesn't stop later commands", run := fun _ => do
        let msgs := run "def a : Type := (\ndef b : Type 1 := Type\n#check b"
        checkEq 2 msgs.size
        check ((msgs[1]!.splitOn "b : Type 1").length > 1) s!"{msgs}" },
    { name := "user syntax without an elaborator is reported", run := fun _ =>
        fails "syntax \"magic\" : term\ndef x : Type := magic" "no elaborator" },
    { name := "duplicate definition", run := fun _ =>
        fails "def a : Type 1 := Type\ndef a : Type 1 := Type" "already been declared" }
  ]

end Tests.Elab

namespace Tests.Elab

def levelGroup : Group where
  name := "universes"
  exercise := "Exercises 4.1–4.2 (and 1.7 for imax)"
  cases := [
    { name := "level normal forms (given)", run := fun _ => do
        let u : Level := .param "u"
        check (Level.equiv (.max u (.succ u)) (.succ u)) "max u (u+1) = u+1"
        check (Level.equiv (.max 1 (.succ u)) (.succ u)) "max 1 (u+1) = u+1"
        check (!Level.equiv (.max 1 u) u) "max 1 u ≠ u"
        check (Level.equiv (.imax u 0) 0) "imax u 0 = 0"
        check (Level.equiv (.imax u (.succ u)) (.succ u)) "imax u (u+1) = u+1"
        check (Level.equiv (.max u (.param "v")) (.max (.param "v") u)) "max is commutative" },
    { name := "universe polymorphic identity", run := fun _ =>
        ok "def id.{u} {A : Sort u} (x : A) : A := x\n#check id Type\n#check id.{3} Type"
          ["id (Type 1) Type : Type 1", "id (Type 1) Type : Type 1"] },
    { name := "explicit level too small", run := fun _ =>
        fails "def id.{u} {A : Sort u} (x : A) : A := x\n#check id.{2} Type" "2:8: error: universe level mismatch" },
    { name := "Prop is impredicative", run := fun _ =>
        ok "def True : Prop := (P : Prop) → P → P\ndef trivial : True := fun P p => p\n#check True"
          ["True : Prop"] },
    { name := "Π into Type is not impredicative", run := fun _ =>
        fails "def T : Type := (A : Type) → A" "type mismatch" },
    { name := "levels in types", run := fun _ =>
        ok "def Pred.{u} (A : Type u) : Type (u+1) := A → Type u\n#check Pred.{1}"
          ["Pred : Type 1 → Type 2"] },
    { name := "level metavariables solved by unification", run := fun _ =>
        ok "def id.{u} {A : Sort u} (x : A) : A := x\ndef t (A : Type 3) (a : A) : A := id a" },
    { name := "unknown level parameter", run := fun _ =>
        fails "def f (A : Type u) : Type u := A" "unknown universe level 'u'" },
    { name := "wrong number of explicit levels", run := fun _ =>
        fails "def id.{u} {A : Sort u} (x : A) : A := x\ndef t := id.{0, 1}" "universe parameters" },
    { name := "level mismatch", run := fun _ =>
        fails "def bad.{u} (A : Type u) : Type := A" "mismatch" },
    { name := "unsolved universe level", run := fun _ =>
        fails "def id.{u} {A : Sort u} (x : A) : A := x\ndef t := @id" "universe level" }
  ]

end Tests.Elab

namespace Tests.Elab

def structGroup : Group where
  name := "elab: structural types"
  exercise := "Exercise 4.9 (and 4.3–4.8)"
  cases := [
    { name := "pairs and projections", run := fun _ =>
        ok "def swap {A B : Type} (p : A × B) : B × A := (p.2, p.1)\n#check swap" ["swap : {A : Type} → {B : Type} → A × B → B × A"] },
    { name := "tuples nest to the right", run := fun _ =>
        ok "def t (A : Type) (a : A) : A × A × A := (a, a, a)\n#reduce fun (A : Type) (a : A) => (t A a).2.1"
          ["fun A a => a"] },
    { name := "dependent pair", run := fun _ =>
        ok "def T : Type 1 := (A : Type) × (A → A)\ndef idT : T := (Unit, fun x => x)" },
    { name := "field access by name", run := fun _ =>
        ok ("def Point : Type := (x : Unit) × (y : Unit) × Unit\n" ++
            "def getY (p : Point) : Unit := p.y\n#reduce fun (p : Point) => p.y") ["fun p => p.2.1"] },
    { name := "unknown field", run := fun _ =>
        fails "def P : Type := (x : Unit) × Unit\ndef g (p : P) : Unit := p.z" "no field 'z'" },
    { name := "unit value and η", run := fun _ =>
        ok "def u : Unit := ()\ndef eta (x : Unit) (P : Unit → Type) (h : P ()) : P x := h" },
    { name := "linear swap with let-pattern", run := fun _ =>
        ok "def swap {A B : Type} (1 p : (1 x : A) × B) : (1 y : B) × A :=\n  let 1 (x, y) := p\n  (y, x)" },
    { name := "linear pair used twice is rejected", run := fun _ =>
        fails "def swap {A B : Type} (1 p : (1 x : A) × B) : (1 y : B) × A := (p.2, p.1)" "quantity" },
    { name := "ex falso", run := fun _ =>
        ok "def efq {A : Type} (e : Empty) : A := absurd e\ndef efq' {P : Prop} (e : False) : P := absurd e" },
    { name := "True is a proposition", run := fun _ =>
        ok "#check True\n#check Unit" ["True : Prop", "Unit : Type"] }
  ]

end Tests.Elab

namespace Tests.Elab

def substDef : String :=
  "def subst {A : Type} (P : A → Type) {a b : A} (e : a = b) (pa : P a) : P b :=\n" ++
  "  cast (transp (fun b _ => P a = P b) (refl (P a)) e) pa\n"

/-- (D1) Abel–Coquand's counterexample to normalisation (LMCS 2020, the propext version),
in Wiz. Their `cast` is between propositions, where Wiz applies the equivalence instead of
regularity, so it goes through a box type: a `μ` type, where `cast` falls back to
regularity (`vCast`: equal types ⇒ `t`). `Omega` has no normal form, and the cast
between Σ types in `loopy` projects its proof, so checking `loopy` evaluates it. See
`wiz-notes/d1-experiment.md`. -/
def abelCoquand (omega : String := "Omega") : String :=
  "def Top : Prop := (A : Prop) → A → A\n" ++
  "def T2 : Prop := Top → Top\n" ++
  "def id2 : T2 := fun x => x\n" ++
  "def delta : T2 := fun z => z T2 id2 z\n" ++
  "def BoxD (P : Prop) : Desc Unit := Desc.arg 1 ((_ : Enum [u]) × P) (fun _ => Desc.ret ())\n" ++
  "def Box (P : Prop) : Type := μ (BoxD P) ()\n" ++
  "def mk {P : Prop} (p : P) : Box P := con (('u, p), (), ())\n" ++
  "def unbox {P : Prop} (b : Box P) : P := ind (fun _ _ => P) (fun i xs ih => xs.1.2) b\n" ++
  "def tautext (A B : Prop) (a : A) (b : B) : A = B := ((fun _ => b), (fun _ => a))\n" ++
  "def apTy (A : Type) (F : A → Type) (a b : A) (e : a = b) : F a = F b :=\n" ++
  "  transp (fun b _ => F a = F b) (refl (F a)) e\n" ++
  "def omega : Top := fun A a => unbox (cast (apTy Prop Box T2 A (tautext T2 A id2 a)) (mk delta))\n" ++
  "def Omega : Top := delta omega\n" ++
  "def B2 : Type := Enum [a, b]\n" ++
  "def P2 : Type := B2 × B2\n" ++
  "def ab : P2 := ('a, 'b)\n" ++
  "def a0 : B2 := 'a\n" ++
  s!"def loopy : (cast ({omega} (P2 = P2) (refl P2)) ab : P2).1 = a0 := refl a0\n"

/-- The same program with the box inside a second box (`Box2 P` has a field of type
`Box P`): the outer box's field is not inert (it has a `Prop` field inside), so the cast
at `Box2` stays structural, and the program checks without regularity. -/
def abelCoquandNested : String :=
  ((abelCoquand).replace
    "def omega : Top := fun A a => unbox (cast (apTy Prop Box T2 A (tautext T2 A id2 a)) (mk delta))\n"
    ("def Box2D (P : Prop) : Desc Unit := Desc.arg 1 ((_ : Enum [u]) × Box P) (fun _ => Desc.ret ())\n" ++
     "def Box2 (P : Prop) : Type := μ (Box2D P) ()\n" ++
     "def mk2 {P : Prop} (b : Box P) : Box2 P := con (('u, b), (), ())\n" ++
     "def unbox2 {P : Prop} (b : Box2 P) : Box P := ind (fun _ _ => Box P) (fun i xs ih => xs.1.2) b\n" ++
     "def omega : Top := fun A a => unbox (unbox2 (cast (apTy Prop Box2 T2 A (tautext T2 A id2 a)) (mk2 (mk delta))))\n"))

/-- Abel–Coquand's own step `cast T2 T2 e δ ▷ δ` (a cast between propositions): Wiz
applies the equivalence `e` instead, here `fun _ => id2`, so the step gives `id2`. (Their
term itself can't be written: `cast` to a variable proposition `A` needs a proof of a
type equation `T2 = A`, which stays stuck while `A` is a variable.) -/
def abelCoquandLiteral : String :=
  "def Top : Prop := (A : Prop) → A → A\n" ++
  "def T2 : Prop := Top → Top\n" ++
  "def id2 : T2 := fun x => x\n" ++
  "def delta : T2 := fun z => z T2 id2 z\n" ++
  "def tautext (A B : Prop) (a : A) (b : B) : A = B := ((fun _ => b), (fun _ => a))\n" ++
  "#reduce (cast (tautext T2 T2 id2 id2) delta : T2)\n"

/-- `--regularity` modes, as on the command line. -/
def regularityMode : String → Regularity
  | "nonprop" => .nonProp
  | "refl" => .refl
  | "off" => .off
  | _ => .full

/-- No errors under the given regularity mode. -/
def okWith (r : Regularity) (input : String) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) input { globals := { regularity := r } }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")

/-- (P2) Checking `input` under `mode` (`full+lazy`: with `lazyProofs`) finishes, without
errors, within `secs` seconds (in a child process, as `checkDiverges`). -/
def checkTerminates (input mode : String) (secs : Nat := 20) : IO Unit := do
  let dir ← IO.FS.createTempDir
  IO.FS.writeFile (dir / "input.wiz") input
  let self ← IO.appPath
  let out ← IO.Process.output { cmd := "sh", cwd := dir, args := #["-c",
    s!"ulimit -v 8000000; exec timeout {secs} \"$0\" --check {mode} input.wiz", self.toString] }
  unless out.exitCode == 0 do
    throw (IO.userError s!"expected success, got exit code {out.exitCode}: {out.stderr.take 1000}")

/-- Checking `input` (with the Lean kernel, in a child process: `tests --check`) doesn't
finish within `secs` seconds. Memory is capped, as the loop allocates. -/
def checkDiverges (input mode : String) (secs : Nat := 3) : IO Unit := do
  let dir ← IO.FS.createTempDir
  IO.FS.writeFile (dir / "input.wiz") input
  let self ← IO.appPath
  let out ← IO.Process.output { cmd := "sh", cwd := dir, args := #["-c",
    s!"ulimit -v 8000000; exec timeout {secs} \"$0\" --check {mode} input.wiz", self.toString] }
  unless out.exitCode == 124 do
    throw (IO.userError s!"expected a timeout, got exit code {out.exitCode}: {out.stderr.take 1000}")

/-- `TyOf a` is `a`'s type (as the elaborator built it) -/
def tyOfDef : String := "def TyOf {ω A : Type} (a : A) : Type := A\n"

def ottGroup : Group where
  name := "observational equality"
  exercise := "Exercises 4.10–4.14"
  cases := [
    { name := "function extensionality is definitional", run := fun _ =>
        ok "def funext {A B : Type} (f g : A → B) (h : (x : A) → f x = g x) : f = g := h" },
    { name := "propositional extensionality", run := fun _ =>
        ok "def propext (P Q : Prop) (pq : P → Q) (qp : Q → P) : P = Q := (pq, qp)" },
    { name := "proof irrelevance", run := fun _ =>
        ok "def irr (P : Prop) (p q : P) (C : P → Type) (c : C p) : C q := c" },
    { name := "equality at Unit is True", run := fun _ =>
        ok "def uu (u v : Unit) : u = v := rfl" },
    { name := "η for pairs, via refl", run := fun _ =>
        ok "def peq {A B : Type} (p : A × B) : p = (p.1, p.2) := refl p" },
    { name := "different type formers are unequal", run := fun _ =>
        ok "def noconf (e : Unit = Empty) : False := e" },
    -- D1: no regularity by default: a cast at a variable type stays a cast
    { name := "cast along a variable `A = A` is not the identity (no regularity; it is with --regularity full)", run := fun _ => do
        let reg := "def reg (A : Type) (e : A = A) (a : A) : cast e a = a := rfl"
        fails reg "type mismatch"
        okWith .full reg },
    { name := "J from transp and cast", run := fun _ =>
        ok substDef },
    { name := "J computes on refl at a data type, not at a variable family (no regularity)", run := fun _ => do
        let substRefl := substDef ++ "def substRefl {A : Type} (P : A → Type) (a : A) (pa : P a) : subst P (refl a) pa = pa := rfl"
        fails substRefl "type mismatch"
        okWith .full substRefl
        ok (substDef ++ "inductive N where\n  | z\n  | s (n : N)\n" ++
          "def substN {A : Type} (a : A) : subst (fun _ => N) (refl a) (N.s N.z) = N.s N.z := rfl") },
    { name := "cast computes on function types (and stays stuck at a variable type)", run := fun _ =>
        ok "#reduce fun (A : Type) (e : (A → A) = (A → A)) (f : A → A) => (cast e f : A → A)"
          ["fun A e f x => cast (e.2 x) (f (cast e.1 x))"] },
    { name := "cast computes on data, constructor by constructor (D1)", run := fun _ =>
        ok ("inductive N where\n  | z\n  | s (n : N)\n" ++
          "inductive V (A : Type) : N → Type where\n  | nil : V A .z\n  | cons {0 n : N} (x : A) (xs : V A n) : V A (.s n)\n" ++
          "#reduce fun (e : N = N) => (cast e (N.s N.z) : N)\n" ++
          "#reduce N.s N.z = N.s N.z\n" ++
          "#reduce fun (n m : N) => (V N n = V N m)\n" ++
          "#reduce fun (e : V N (.s .z) = V N (.s .z)) => (cast e (V.cons N.z V.nil : V N (.s .z)) : V N (.s .z))")
          ["fun e => .s .z", "True", "fun n m => (0 e : n = m) × True",
           "fun e => .cons .z .z .nil"] },
    { name := "type equality", run := fun _ =>
        ok "def t : Type = Type := refl Type" },
    { name := "propositions in a function type's domain compare by equivalence", run := fun _ =>
        ok "#reduce (True → Unit) = ((True → True) → Unit)"
          ["(0 e : (0 _ : (0 x : True → True) → True) × ((0 x : True) → True → True)) × ((0 x : True → True) → True)"] },
    { name := "equivalent propositions of different shapes don't prove False", run := fun _ =>
        -- `True = (True → True)` at `Prop`, carried into `Type` by congruence; comparing
        -- the domains by shape made the equation `False`
        fails ("def apTy (A : Type) (F : A → Type) (a b : A) (e : a = b) : F a = F b :=\n" ++
          "  transp (fun b _ => F a = F b) (refl (F a)) e\n" ++
          "def G : Prop → Type := fun X => X → Unit\n" ++
          "def e : True = (True → True) := ((fun u => fun v => v), (fun f => ()))\n" ++
          "def bad : G True = G (True → True) := apTy Prop G True (True → True) e\n" ++
          "def anyType (A : Type) : A := let (x, y) := bad; absurd x") "absurd expects" },
    -- the types the elaborator builds (a definition's telescope, constructor types)
    -- carry their sorts too, so equations between them compute instead of waiting
    { name := "a definition's type carries its sort: propositions in the domain", run := fun _ =>
        ok (tyOfDef ++ "def f (x : True) : Unit := ()\ndef g (x : True → True) : Unit := ()\n" ++
          "#reduce TyOf f = TyOf g")
          ["(0 e : (0 _ : (0 x : True → True) → True) × ((0 x : True) → True → True)) × ((0 x : True → True) → True)"] },
    { name := "a definition's type carries its sort: other types", run := fun _ =>
        ok (tyOfDef ++ "inductive N where\n  | z\n  | s (n : N)\ndef h (x : N) : N := x\n" ++
          "#reduce TyOf h = (N → N)\n" ++
          "#reduce fun (e : TyOf h = (N → N)) (u : TyOf h) => (cast e u : N → N)")
          ["(0 e : True) × ((0 x : N) → True)", "fun e u x => u x"] },
    { name := "a constructor's type carries its sort", run := fun _ =>
        ok (tyOfDef ++ "inductive Box (A : Type) where\n  | mk (a : A)\n" ++
          "#reduce TyOf (@Box.mk Unit) = (Unit → Box Unit)")
          ["(0 e : True) × ((0 x : Unit) → True)"] },
    { name := "a match on several scrutinees whose types mention a variable", run := fun _ =>
        ok "def pick (A : Type) (x y : A) : A := match x, y with\n  | a, b => b" },
    { name := "equality of proofs is rejected", run := fun _ =>
        fails "def bad (P : Prop) (p q : P) : p = q := rfl" "equality is for types" },
    { name := "wrong equation", run := fun _ =>
        fails "def bad (A : Type) (a b : A) : a = b := rfl" "type mismatch" },
    -- D1: regularity is off by default, and the program checks; with `--regularity full`
    -- (or `nonprop`) checking it does not terminate
    { name := "D1 (Abel–Coquand): the program checks (no regularity: the box's cast casts its proof field)", run := fun _ => do
        ok (abelCoquand "omega")
        ok (abelCoquand) },
    { name := "D1 (Abel–Coquand): with regularity, checking the program does not terminate", run := fun _ =>
        checkDiverges (abelCoquand) "full" },
    { name := "D1 (Abel–Coquand): a box in a box is not inert either (checks; loops with regularity)", run := fun _ => do
        unless (abelCoquandNested.splitOn "unbox2").length > 2 do throw (IO.userError "variant not built")
        ok abelCoquandNested
        checkDiverges abelCoquandNested "full" },
    { name := "regularity at inert types: an indexed recursor computes at a data motive (Vec.length)", run := fun _ =>
        ok ("inductive N where\n  | z\n  | s (n : N)\n" ++
          "inductive V (A : Type) : N → Type where\n  | nil : V A .z\n  | cons {0 n : N} (x : A) (xs : V A n) : V A (.s n)\n" ++
          "def len {A : Type} {0 n : N} : V A n → N\n  | .nil => .z\n  | .cons _ xs => .s (len xs)\n" ++
          "def lenCons {A : Type} {0 n : N} (x : A) (xs : V A n) : len (V.cons x xs) = N.s (len xs) := rfl\n" ++
          "def castN (e : N = N) (n : N) : (cast e n : N) = n := rfl\n") },
    { name := "no regularity at a type with a variable parameter", run := fun _ =>
        fails ("inductive L (A : Type) where\n  | nil\n  | cons (x : A) (xs : L A)\n" ++
          "def castL (A : Type) (e : L A = L A) (l : L A) : (cast e l : L A) = l := rfl\n") "type mismatch" },
    { name := "D1: a cast between propositions applies the equivalence, not regularity", run := fun _ =>
        ok abelCoquandLiteral ["fun x => x"] },
    { name := "D1 (R1): regularity only at non-propositions doesn't help (the box is a type)", run := fun _ =>
        checkDiverges (abelCoquand) "nonprop" },
    { name := "D1 (R2, off): regularity only along refl, or none, checks the program", run := fun _ => do
        okWith .refl (abelCoquand)
        okWith .off (abelCoquand) },
    -- P2 (`--lazy-proofs`, off by default): proofs are never evaluated, so the loop, which
    -- lives in a proof, is never run, even with full regularity
    { name := "P2: with lazy proofs, Abel–Coquand checks even with full regularity (and nested)", run := fun _ => do
        checkTerminates (abelCoquand) "full+lazy"
        checkTerminates abelCoquandNested "full+lazy"
        checkTerminates (abelCoquand) "off+lazy" },
    { name := "P2: with lazy proofs, a cast between propositions is stuck, not the equivalence", run := fun _ => do
        let s := runFrontend (R := ZeroOneMany) abelCoquandLiteral { globals := { lazyProofs := true } }
        let out := (s.messages.map (·.render abelCoquandLiteral)).toList
        unless out.any (·.contains "cast") do throw (IO.userError s!"expected a stuck cast, got {out}") }
  ]

end Tests.Elab

namespace Tests.Elab

def appDef : String :=
  "def app {A B : Type} {q : Qty} (f : (%q x : A) → B) (%q a : A) : B := f a\n"

def qtyGroup : Group where
  name := "quantity polymorphism"
  exercise := "Exercise 4.15"
  cases := [
    { name := "application at any quantity", run := fun _ => ok appDef },
    { name := "#check shows the quantity variable", run := fun _ =>
        ok (appDef ++ "#check app") ["app : {A : Type} → {B : Type} → {q : Qty} → ((%q x : A) → B) → (%q a : A) → B"] },
    { name := "the quantity is inferred from a linear function", run := fun _ =>
        ok (appDef ++ "def lid (1 x : Unit) : Unit := x\ndef t (1 u : Unit) : Unit := app lid u") },
    { name := "... and checked: passing an ω variable linearly is fine, using it twice is not", run := fun _ =>
        fails (appDef ++ "def lid (1 x : Unit) : Unit := x\ndef t (1 u : Unit) : Unit × Unit := (app lid u, u)") "quantity" },
    { name := "duplicating a %q variable fails (q could be 1)", run := fun _ =>
        fails "def dup {A : Type} {q : Qty} (%q x : A) : A × A := (x, x)" "quantity" },
    { name := "dropping a %q variable fails (q could be 1)", run := fun _ =>
        fails "def drop {A : Type} {q : Qty} (%q x : A) : Unit := ()" "quantity" },
    { name := "even the identity fails: q could be 0", run := fun _ =>
        fails "def keep {A : Type} {q : Qty} (%q x : A) : A := x" "quantity" },
    { name := "products of quantity variables", run := fun _ =>
        ok ("def twice {A B : Type} {q r : Qty} (f : (%q x : A) → B) (g : (%r y : B) → B) (%(r) a : B) : B := g a\n") },
    { name := "quantity literals as terms", run := fun _ =>
        ok "def one : Qty := 1\ndef many : Qty := ω\ndef f {A : Type} (%one x : A) : A := x" },
    -- F6: `(%q x : A) → B = (1 x : A) → B` computed to `False` (the quantities differ as
    -- polynomials), and `q := 1` made it provable: a closed proof of `False`
    { name := "F6: types whose quantities differ only by a variable are not unequal (it proved False)", run := fun _ => do
        fails ("inductive N where\n  | z\n  | s (n : N)\n" ++
          -- (then `def boom : False := flip (q := 1) rfl` was a closed proof of False)
          "def flip {q : Qty} (e : ((%q x : N) → N) = ((1 x : N) → N)) : False := e\n") "mismatch"
        -- (then `bad 1 (refl …)`)
        fails "def bad (q : Qty) (e : ((%q x : Unit) → Unit) = ((1 x : Unit) → Unit)) : False := e\n" "mismatch"
        fails "def bad (q : Qty) (e : ((%q x : Unit) × Unit) = ((1 x : Unit) × Unit)) : False := e\n" "mismatch" },
    { name := "F6: types with two different literal quantities are unequal", run := fun _ =>
        ok ("def apart (e : ((0 x : Unit) → Unit) = ((1 x : Unit) → Unit)) : False := e\n" ++
          "def apart2 (e : ((ω x : Unit) × Unit) = ((1 x : Unit) × Unit)) : False := e\n") }
  ]

end Tests.Elab

namespace Tests.Elab

def dataPrelude : String := "\ndef BoolD : Desc Unit := Desc.arg 1 (Enum [false, true]) (fun _ => Desc.ret ())\ndef Bool : Type := μ BoolD ()\ndef true : Bool := con ('true, (), ())\ndef false : Bool := con ('false, (), ())\n\ndef NatD : Desc Unit :=\n  Desc.arg 1 (Enum [zero, succ]) (fun t => ecase t [Desc.ret (), Desc.rec 1 () (Desc.ret ())])\ndef Nat : Type := μ NatD ()\ndef zero : Nat := con ('zero, (), ())\ndef succ (n : Nat) : Nat := con ('succ, n, (), ())\n\ndef isZero (n : Nat) : Bool := ind (fun _ _ => Bool) (fun i xs ih => ecase xs.1 [true, false]) n\n\ndef add (m n : Nat) : Nat :=\n  ind (fun _ _ => Nat) (fun i xs ih =>\n    (ecase xs.1 [fun _ _ => n, fun rest h => succ h.1]\n      : (rest : Desc.interp (ecase xs.1 [Desc.ret (), Desc.rec 1 () (Desc.ret ())] : Desc Unit) (fun j => μ NatD j) i)\n        → Desc.All (ecase xs.1 [Desc.ret (), Desc.rec 1 () (Desc.ret ())] : Desc Unit) (fun j => μ NatD j) (fun _ _ => Nat) i rest\n        → Nat) xs.2 ih) m\ndef twoPlusOne : add (succ (succ zero)) (succ zero) = succ (succ (succ zero)) := refl (succ (succ (succ zero)))\n\ndef not (b : Bool) : Bool := ind (fun _ _ => Bool) (fun i xs ih => ecase xs.1 [true, false]) b\n\ndef StreamD : Desc Unit := Desc.arg 1 Bool (fun _ => Desc.rec 1 () (Desc.ret ()))\ndef Stream : Type := ν StreamD ()\ndef alternate (b : Bool) : Stream :=\n  coit (fun _ => Bool) (fun i s => (s, not s, (), ())) b\n\n"

def dataGroup : Group where
  name := "data"
  exercise := "Exercises 4.17–4.20"
  cases := [
    { name := "Bool, Nat, add, streams", run := fun _ => ok dataPrelude },
    { name := "ind computes: isZero 1", run := fun _ =>
        ok (dataPrelude ++ "#reduce isZero (succ zero)") [".false"] },
    { name := "ind with hypotheses: 1 + 1", run := fun _ =>
        ok (dataPrelude ++ "#reduce add (succ zero) (succ zero)")
          [".succ (.succ .zero)"] },
    { name := "coinduction: the third element of alternate true", run := fun _ =>
        ok (dataPrelude ++ "#reduce (out (out (out (alternate true)).2.1).2.1).1") [".true"] },
    { name := "Desc.elim computes on a closed description", run := fun _ =>
        ok (dataPrelude ++ "def isRet (D : Desc Unit) : Bool :=\n" ++
            "  Desc.elim (fun _ => Bool) (fun i => true) (fun q S E ih => false) (fun q j E ih => false) (fun q H j E ih => false) D\n" ++
            "#reduce isRet (Desc.ret ())\n#reduce isRet NatD") [".true", ".false"] },
    { name := "a constructor with the wrong fields is rejected", run := fun _ =>
        fails (dataPrelude ++ "def bad : Nat := con ('succ, (), ())") "type mismatch" },
    { name := "unknown tag", run := fun _ =>
        fails (dataPrelude ++ "def bad : Nat := con ('three, (), ())") "not one of the tags" },
    { name := "an erased field drops a linear variable", run := fun _ =>
        fails ("def BoxD : Desc Unit := Desc.arg 0 Unit (fun _ => Desc.ret ())\n" ++
               "def box (1 u : Unit) : μ BoxD () := con (u, (), ())") "quantity" },
    { name := "a linear field keeps it", run := fun _ =>
        ok ("def BoxD : Desc Unit := Desc.arg 1 Unit (fun _ => Desc.ret ())\n" ++
            "def box (1 u : Unit) : μ BoxD () := con (u, (), ())") },
    { name := "case branches must agree on linear variables", run := fun _ =>
        fails "def f (1 u : Unit) (t : Enum [a, b]) : Unit := ecase t [u, ()]" "quantity" },
    { name := "... but may differ on unrestricted ones", run := fun _ =>
        ok "def f (u : Unit) (t : Enum [a, b]) : Unit := ecase t [u, ()]" }
  ]

end Tests.Elab

namespace Tests.Elab

def indPrelude : String := "\ninductive Nat where\n  | zero\n  | succ (n : Nat)\n\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A .zero\n  | cons {0 n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)\n\n\ndef two : Vec Nat (.succ (.succ .zero)) := .cons .zero (.cons (.succ .zero) .nil)\n\nstructure Point where\n  x : Nat\n  y : Nat\n\ndef p : Point := Point.mk .zero (.succ .zero)\n\n"

def inductiveGroup : Group where
  name := "inductive"
  exercise := "Exercise 4.21"
  cases := [
    { name := "Nat, Vec, Point", run := fun _ => ok indPrelude },
    { name := "constructor types print nominally", run := fun _ =>
        ok (indPrelude ++ "#check Vec.cons")
          ["Vec.cons : {A : Type} → {n : Nat} → A → Vec A n → Vec A (.succ n)"] },
    { name := "values print with constructor names", run := fun _ =>
        ok (indPrelude ++ "#reduce two") [".cons (.succ .zero) .zero (.cons .zero (.succ .zero) .nil)"] },
    { name := "structure fields by name", run := fun _ =>
        ok (indPrelude ++ "#reduce p.y") [".succ .zero"] },
    { name := "wrong index is a type mismatch", run := fun _ =>
        fails (indPrelude ++ "def bad : Vec Nat (.succ .zero) := .nil") "type mismatch" },
    { name := "non-uniform parameters are rejected", run := fun _ =>
        fails "inductive T (A : Type) where\n  | mk (x : T Unit)" "parameters" },
    { name := "negative occurrences are rejected", run := fun _ =>
        fails "inductive Bad where\n  | mk (f : Bad → Unit)" "may only occur" },
    { name := "fields may not depend on recursive fields", run := fun _ =>
        fails "inductive T : Type where\n  | mk (x : T) (y : (x, x).1 = x)" "may not depend" },
    { name := "Nat.rec computes", run := fun _ =>
        ok (indPrelude ++ "def add (m n : Nat) : Nat := Nat.rec (fun _ => Nat) n (fun _ ih => .succ ih) m\n" ++
            "#reduce add (.succ .zero) (.succ (.succ .zero))") [".succ (.succ (.succ .zero))"] },
    { name := "Vec.rec has Lean's shape", run := fun _ =>
        ok (indPrelude ++ "#check Vec.rec")
          ["Vec.rec : {A : Type} → (0 motive : (x : Nat) → Vec A x → Sort ?u0) → motive .zero .nil → ({n : Nat} → (x : A) → (xs : Vec A n) → motive n xs → motive (.succ n) (.cons n x xs)) → {x : Nat} → (x' : Vec A x) → motive x x'"] },
    { name := "Vec.rec computes through indices", run := fun _ =>
        ok (indPrelude ++ "def len {A : Type} {n : Nat} (v : Vec A n) : Nat := Vec.rec (fun _ _ => Nat) .zero (fun _ _ ih => .succ ih) v\n" ++
            "#reduce len two") [".succ (.succ .zero)"] },
    { name := "casesOn: predecessor", run := fun _ =>
        ok (indPrelude ++ "def pred (n : Nat) : Nat := Nat.casesOn (fun _ => Nat) .zero (fun m => m) n\n#reduce pred (.succ (.succ .zero))") [".succ .zero"] },
    { name := "unknown constructor via dot", run := fun _ =>
        fails (indPrelude ++ "def bad : Nat := .three") "no constructor three" }
  ]

end Tests.Elab

namespace Tests.Elab

def matchPrelude : String := "inductive Nat where\n  | zero\n  | succ (n : Nat)\n\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A .zero\n  | cons {0 n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)\n\ndef pred (n : Nat) : Nat := match n with\n  | .zero => .zero\n  | .succ m => m\n\ndef add : Nat → Nat → Nat\n  | .zero, n => n\n  | .succ m, n => .succ (add m n)\n\ndef head {A : Type} {n : Nat} : Vec A (.succ n) → A\n  | .cons x _ => x\n\ndef map {A B : Type} (f : A → B) {n : Nat} : Vec A n → Vec B n\n  | .nil => .nil\n  | .cons x xs => .cons (f x) (map xs)\n\n"

def matchGroup : Group where
  name := "match"
  exercise := "stage 4e"
  cases := [
    { name := "pred, add, head, map", run := fun _ => ok matchPrelude },
    { name := "match expression", run := fun _ =>
        ok (matchPrelude ++ "#reduce pred (.succ (.succ .zero))") [".succ .zero"] },
    { name := "structural recursion with a varying argument", run := fun _ =>
        ok (matchPrelude ++ "#reduce add (.succ .zero) (.succ (.succ .zero))") [".succ (.succ (.succ .zero))"] },
    { name := "impossible cases may be omitted (head)", run := fun _ =>
        ok (matchPrelude ++ "#reduce head (Vec.cons Nat.zero Vec.nil)") [".zero"] },
    { name := "recursion over an indexed family (map)", run := fun _ =>
        ok (matchPrelude ++ "#reduce map (fun _ => Nat.zero) (Vec.cons (Nat.succ Nat.zero) Vec.nil)")
          [".cons .zero .zero .nil"] },
    { name := "nested patterns and wildcards", run := fun _ =>
        ok (matchPrelude ++ "def isTwo : Nat → Nat\n  | .succ (.succ .zero) => .succ .zero\n  | _ => .zero\n" ++
            "#reduce isTwo (.succ (.succ .zero))\n#reduce isTwo (.succ .zero)") [".succ .zero", ".zero"] },
    { name := "recursion through two columns", run := fun _ =>
        ok (matchPrelude ++ "def eqb : Nat → Nat → Nat\n  | .zero, .zero => .succ .zero\n" ++
            "  | .succ m, .succ n => eqb m n\n  | _, _ => .zero\n#reduce eqb (.succ .zero) (.succ .zero)") [".succ .zero"] },
    { name := "index unification by substitution (tail)", run := fun _ =>
        ok (matchPrelude ++ "def tail {A : Type} {n : Nat} : Vec A (.succ n) → Vec A n\n  | .cons _ xs => xs\n" ++
            "#reduce tail (Vec.cons Nat.zero (Vec.cons (Nat.succ Nat.zero) Vec.nil))") [".cons .zero (.succ .zero) .nil"] },
    { name := "zip: impossible pairs omitted, lengths unified", run := fun _ =>
        ok (matchPrelude ++ "def zip {A B : Type} {n : Nat} : Vec A n → Vec B n → Vec (A × B) n\n" ++
            "  | .nil, .nil => .nil\n  | .cons a as, .cons b bs => .cons (a, b) (zip as bs)\n" ++
            "#reduce zip (Vec.cons Nat.zero Vec.nil) (Vec.cons (Nat.succ Nat.zero) Vec.nil)")
          [".cons .zero (.zero, .succ .zero) .nil"] },
    { name := "tuples of variables infer their type", run := fun _ =>
        ok (matchPrelude ++ "def t1 (A B : Type) (n : Nat) (a : A) (b : B) (r : Vec (A × B) n) : Vec (A × B) (.succ n) := Vec.cons (a, b) r") },
    { name := "missing cases are reported", run := fun _ =>
        fails (matchPrelude ++ "def missing : Nat → Nat\n  | .zero => .zero") "missing case" },
    { name := "non-structural recursion is rejected", run := fun _ =>
        fails (matchPrelude ++ "def bad : Nat → Nat\n  | .zero => .zero\n  | .succ m => bad (.succ m)") "recursive call" }
  ]

end Tests.Elab

namespace Tests.Elab

def streamPrelude : String := "inductive Nat where\n  | zero\n  | succ (n : Nat)\n\ncoinductive Stream (A : Type) where\n  head : A\n  tail : Stream A\n\ndef nats (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => nats (.succ n)\n\n\ndef repeat {A : Type} (a : A) : Stream A\n  | .head => a\n  | .tail => repeat a\n\n"

/-- `register` (no corecursive observation: `cocon`) and `mealy` (corecursive: `coit`). -/
def registerSrc : String :=
  "def register {A : Type} (init : A) (s : Stream A) : Stream A\n  | .head => init\n  | .tail => s\n" ++
  "def mealy {S I O : Type} (f : S → I → S × O) (st : S) (i : Stream I) : Stream O\n" ++
  "  | .head => (f st i.head).2\n  | .tail => mealy f (f st i.head).1 i.tail\n"

def coinductiveGroup : Group where
  name := "copatterns"
  exercise := "stage 4e, Exercise 4.24"
  cases := [
    { name := "Stream, nats, repeat", run := fun _ => ok streamPrelude },
    { name := "observations unfold lazily", run := fun _ =>
        ok (streamPrelude ++ "#reduce (nats .zero).tail.tail.head") [".succ (.succ .zero)"] },
    { name := "parameters stay fixed, explicit arguments are the state", run := fun _ =>
        ok (streamPrelude ++ "#reduce (repeat Nat.zero).tail.tail.head") [".zero"] },
    { name := "guardedness: a recursive observation must be a corecursive call", run := fun _ =>
        fails (streamPrelude ++ "def bad (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => (bad n).tail") "guardedness" },
    { name := "every observation must be defined", run := fun _ =>
        fails (streamPrelude ++ "def bad (n : Nat) : Stream Nat\n  | .head => n") "missing copattern" },
    { name := "no corecursive observation: a cocon cell (register)", run := fun _ =>
        ok (streamPrelude ++ registerSrc ++ "#reduce (register Nat.zero (nats (.succ .zero))).tail.head")
          [".succ .zero"] },
    { name := "a copattern definition without arguments", run := fun _ =>
        ok (streamPrelude ++ "def s : Stream Nat\n  | .head => .zero\n  | .tail => nats .zero\n#reduce s.tail.tail.head")
          [".succ .zero"] },
    { name := "guardedness: no unguarded call in a cocon definition", run := fun _ =>
        fails (streamPrelude ++ "def bad (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => repeat (bad n).head") "guardedness" },
    { name := "guardedness: corecursive and plain recursive observations don't mix", run := fun _ =>
        fails ("coinductive Tree (A : Type) where\n  label : A\n  left : Tree A\n  right : Tree A\n" ++
          "def bad {A : Type} (a : A) (t : Tree A) : Tree A\n  | .label => a\n  | .left => bad a t\n  | .right => t") "guardedness" },
    { name := "the coconstructor T.mk and .mk", run := fun _ =>
        ok (streamPrelude ++ "#check @Stream.mk\ndef s : Stream Nat := .mk .zero (Stream.mk (.succ .zero) (nats .zero))\n#reduce s.tail.tail.head")
          ["Stream.mk : {A : Type} → A → Stream A → Stream A", ".zero"] },
    { name := "cocon, the kernel primitive", run := fun _ =>
        ok (streamPrelude ++ "def s : Stream Nat := cocon (.zero, nats (.succ .zero), (), ())\n#reduce s.tail.head")
          [".succ .zero"] },
    { name := "cocon needs a coinductive expected type", run := fun _ =>
        fails (streamPrelude ++ "def bad : Nat := cocon (.zero, ())") "cocon builds a coinductive value" },
    { name := "cocon at a variable size is rejected", run := fun _ =>
        fails (streamPrelude ++ "def bad (i : Size) (s : (Stream Nat)^i) : (Stream Nat)^i := cocon (.zero, s, (), ())") "size ↑s" },
    { name := "a sized register: the tail one size down", run := fun _ =>
        ok (streamPrelude ++ "def register {i : Size} (a : Nat) (s : (Stream Nat)^i) : (Stream Nat)^(↑i)\n  | .head => a\n  | .tail => s") },
    { name := "a sized register can't keep the size", run := fun _ =>
        fails (streamPrelude ++ "def bad {i : Size} (a : Nat) (s : (Stream Nat)^i) : (Stream Nat)^i\n  | .head => a\n  | .tail => s") "size ↑s or ∞" },
    { name := "cocon bumps the size", run := fun _ =>
        ok (streamPrelude ++ "def delay (i : Size) (s : (Stream Nat)^i) : (Stream Nat)^(↑i) := cocon (.zero, s, (), ())") },
    { name := "mealy machines by copatterns (coit, state = the arguments)", run := fun _ =>
        ok (streamPrelude ++ registerSrc ++ "#reduce (mealy (fun (n : Nat) (x : Nat) => (.succ n, n)) .zero (nats .zero)).tail.tail.head")
          [".succ (.succ .zero)"] },
    { name := "generalised field notation on inductives too", run := fun _ =>
        ok (matchPrelude ++ "def Vec.tail {A : Type} {n : Nat} : Vec A (.succ n) → Vec A n\n  | .cons _ xs => xs\n" ++
            "def tl {A : Type} {n : Nat} (v : Vec A (.succ (.succ n))) : Vec A n := v.tail.tail") }
  ]

end Tests.Elab

namespace Tests.Elab

def sizedPrelude : String := "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef add : Nat → Nat → Nat\n  | .zero, n => n\n  | .succ m, n => .succ (add m n)\ndef fib {i : Size} : Nat^i → Nat\n  | .zero => .succ .zero\n  | .succ .zero => .succ .zero\n  | .succ (.succ n) => add (fib n) (fib (.succ n))\n\n"

def sizedGroup : Group where
  name := "sized types"
  exercise := "Exercises 4.22–4.23"
  cases := [
    { name := "subtyping: smaller sizes fit bigger ones", run := fun _ =>
        ok (sizedPrelude ++ "#check fun (i : Size) (j : Size< i) (x : Nat^j) => (x : Nat^i)")
          ["fun i j x => (x : Nat^i) : (i : Size) → (j : Size< i) → Nat^j → Nat^i"] },
    { name := "but not the other way round", run := fun _ =>
        fails (sizedPrelude ++ "#check fun (i : Size) (j : Size< i) (x : Nat^i) => (x : Nat^j)") "mismatch" },
    { name := "sized case analysis keeps field sizes", run := fun _ =>
        ok (sizedPrelude ++ "#check @Nat.scasesOn")
          ["Nat.scasesOn : {s : Size} → (0 motive : Nat → Sort ?u0) → ((0 j : Size< s) → motive .zero) → ((0 j : Size< s) → (n : Nat^j) → motive (.succ n)) → (x : Nat^s) → motive x"] },
    { name := "course-of-values recursion (fib)", run := fun _ =>
        ok (sizedPrelude ++ "#reduce fib (.succ (.succ (.succ (.succ .zero))))")
          [".succ (.succ (.succ (.succ (.succ .zero))))"] },
    { name := "a call at the same size is rejected", run := fun _ =>
        fails (sizedPrelude ++ "def bad {i : Size} : Nat^i → Nat\n  | n => bad n") "mismatch" },
    { name := "a call on a rebuilt value is rejected", run := fun _ =>
        fails (sizedPrelude ++ "def bad {i : Size} : Nat^i → Nat\n  | .zero => .zero\n  | .succ n => bad (.succ n)") "not below" },
    { name := "∞ is not a size below ∞", run := fun _ =>
        fails (sizedPrelude ++ "def bad : Size< ∞ := ∞") "mismatch" }
  ]

end Tests.Elab

namespace Tests.Elab

def runPrelude : String := "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef add : Nat → Nat → Nat\n  | .zero, n => n\n  | .succ m, n => .succ (add m n)\ndef fib {i : Size} : Nat^i → Nat\n  | .zero => .succ .zero\n  | .succ .zero => .succ .zero\n  | .succ (.succ n) => add (fib n) (fib (.succ n))\ncoinductive Stream (A : Type) where\n  head : A\n  tail : Stream A\ndef nats (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => nats (.succ n)\ndef swap {A B : Type} (p : A × B) : B × A := (p.2, p.1)\n\n"

def runGroup : Group where
  name := "eval"
  exercise := "Exercises 5.1–5.3"
  cases := [
    { name := "structural recursion runs", run := fun _ =>
        ok (runPrelude ++ "#eval add (.succ .zero) (.succ (.succ .zero))") [".succ (.succ (.succ .zero))"] },
    { name := "sized recursion runs (fib 5 = 8)", run := fun _ =>
        ok (runPrelude ++ "#eval fib (.succ (.succ (.succ (.succ (.succ .zero)))))")
          [".succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))"] },
    { name := "codata is lazy and observed with out", run := fun _ =>
        ok (runPrelude ++ "#eval (nats .zero).tail.tail.head") [".succ (.succ .zero)"] },
    { name := "pairs", run := fun _ =>
        ok (runPrelude ++ "#eval swap (Nat.zero, Nat.succ Nat.zero)") ["(.succ .zero, .zero)"] },
    { name := "types and proofs erase to ◾", run := fun _ =>
        ok "def id {A : Type} (x : A) : A := x\n#erase id" ["id := (λA. (λx. #0))"] },
    { name := "erased fields are gone at runtime", run := fun _ =>
        ok (runPrelude ++ "inductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A .zero\n" ++
            "  | cons {0 n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)\n#erase Vec.cons")
          ["Vec.cons := (λA. (λn. (λx. (λxs. ⟨1 ◾ #1 #0⟩))))"] }
  ]

end Tests.Elab

namespace Tests.Elab

def macroPrelude : String := "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef add : Nat → Nat → Nat\n  | .zero, n => n\n  | .succ m, n => .succ (add m n)\ndef mul : Nat → Nat → Nat\n  | .zero, _ => .zero\n  | .succ m, n => add n (mul m n)\ninfixl:65 \" + \" => add\ninfixl:70 \" * \" => mul\nnotation \"two\" => Nat.succ (Nat.succ Nat.zero)\ninductive Bool where\n  | false\n  | true\nsyntax \"if\" term \"then\" term \"else\" term : term\nmacro_rules\n  | `(term| if $c then $t else $e) => `(term| match $c with | .true => $t | .false => $e)\nsyntax \"const_x\" term : term\nmacro_rules\n  | `(term| const_x $e) => `(term| (fun x => $e) Nat.zero)\ndef h (x : Nat) : Nat := const_x x\n\n"

def macroGroup : Group where
  name := "macros"
  exercise := "Exercise 6.1"
  cases := [
    { name := "infixl with precedence", run := fun _ =>
        ok (macroPrelude ++ "#eval two + two * two")
          [".succ (.succ (.succ (.succ (.succ (.succ .zero)))))"] },
    { name := "macro_rules with quotations", run := fun _ =>
        ok (macroPrelude ++ "#eval (if Bool.false then two else Nat.zero : Nat)") [".zero"] },
    { name := "hygiene: a template binder does not capture user variables", run := fun _ =>
        ok (macroPrelude ++ "#eval h two") [".succ (.succ .zero)"] },
    { name := "a user command defined by a macro", run := fun _ =>
        ok (macroPrelude ++ "syntax \"def_two\" ident : command\n" ++
            "macro_rules\n  | `(command| def_two $n) => `(command| def $n : Nat := two)\n" ++
            "def_two myTwo\n#eval myTwo") [".succ (.succ .zero)"] },
    { name := "a user syntax category with macros", run := fun _ =>
        ok (macroPrelude ++ "declare_syntax_cat digit\nsyntax \"I\" : digit\nsyntax \"digits\" digit* : term\n" ++
            "macro_rules\n  | `(term| digits) => `(term| Nat.zero)\n#eval (digits : Nat)") [".zero"] }
  ]

/-- Exactly one error (with `lib/` importable), mentioning `fragment`. -/
def failsLib (input : String) (fragment : String) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let s := runFrontend (R := ZeroOneMany) input { loader := fun m => if m == "Prelude" then some prelude else none }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

def treePrelude : String := "import Prelude
inductive Tree where
  | leaf
  | node (k : Nat → Tree)
def Tree.depthAt : Tree → Nat → Nat
  | .leaf, _ => 1
  | .node k, n => Tree.depthAt (k n) n + 1
"

def procPrelude : String := "import Prelude
syntax (name := twice) \"twice!\" term : term
def twiceMacro : Macro := fun stx => do
  e ← MacroM.pure (Syntax.getArg stx 1);
  MacroM.pure `(term| let y := $e; Nat.add y y)
attribute [macro term.twice] twiceMacro
"

/-- `import Prelude` and `import Word`. -/
def preludeLoader : IO (Name → Option String) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let word ← IO.FS.readFile "lib/Word.wiz"
  pure fun m => if m == "Prelude" then some prelude else if m == "Word" then some word else none

/-- `ok`, with `lib/` available to `import` (the tests run from the package root). -/

def okLib (input : String) (infos : List String := []) : IO Unit := do
  let loader ← preludeLoader
  let s := runFrontend (R := ZeroOneMany) input { loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr (s.messages.toList.map (·.text))).pretty

def tacticGroup : Group where
  name := "tactics"
  exercise := "Exercises 6.4–6.6"
  cases := [
    { name := "intro and exact", run := fun _ =>
        okLib "import Prelude\ndef id' : (A : Type) → A → A := by\n  intro A\n  intro x\n  exact x\n#check id'"
          ["id' : (A : Type) → A → A"] },
    { name := "tactics separated by ;", run := fun _ =>
        okLib "import Prelude\ndef k : Nat → Bool → Nat := by intro n; intro b; exact n" },
    { name := "assumption (Exercise 6.6)", run := fun _ =>
        okLib "import Prelude\ndef k : Nat → Bool → Nat := by intro n; intro b; assumption" },
    { name := "rfl is a tactic macro", run := fun _ =>
        okLib "import Prelude\ndef two : 1 + 1 = 2 := by rfl" },
    { name := "apply makes goals for the arguments", run := fun _ =>
        okLib "import Prelude\ndef ap : (A B : Type) → (A → B) → A → B := by\n  intro A; intro B; intro f; intro a\n  apply f\n  assumption" },
    { name := "first and try", run := fun _ =>
        okLib "import Prelude\ndef t : Nat := by try exact Bool.true; first | exact Bool.true | exact 3" },
    { name := "unsolved goals are reported with their context", run := fun _ =>
        failsLib "import Prelude\ndef bad : Nat → Bool := by intro n" "unsolved goals:\nn : Nat\n⊢ Bool" },
    { name := "a failing tactic is an error at the tactic", run := fun _ =>
        failsLib "import Prelude\ndef bad : Nat := by assumption" "assumption: no hypothesis matches the goal" },
    { name := "the proof term is checked by the kernel", run := fun _ =>
        okLib "import Prelude\ndef k : Nat → Nat := by intro n; exact (n + 1)\n#eval k 41" ["42"] },
    { name := "a user-defined tactic, written in Wiz", run := fun _ =>
        okLib ("import Prelude\nsyntax (name := intros2) \"intros2\" : tactic\n" ++
          "def myIntros : Tactic := fun _ => do\n  g ← TacticM.mainGoal;\n  g1 ← TacticM.intro g \"a\";\n  g2 ← TacticM.intro g1 \"b\";\n" ++
          "  TacticM.replaceMainGoal (.cons g2 .nil)\nattribute [tactic tactic.intros2] myIntros\n" ++
          "def k : Nat → Nat → Nat := by intros2; exact b") }
  ]

def classPrelude : String := "import Prelude
class Inhabited (A : Type) where
  default : A
instance : Inhabited Nat := Inhabited.mk 0
instance : Inhabited Bool where
  default := Bool.true
instance {A : Type} [Inhabited A] : Inhabited (List A) where
  default := List.cons Inhabited.default List.nil
"

def classGroup : Group where
  name := "classes"
  exercise := "Exercise 7.1"
  cases := [
    { name := "methods take the instance as an instance-implicit argument", run := fun _ =>
        okLib (classPrelude ++ "#check Inhabited.default") ["Inhabited.default : {A : Type} → [self : Inhabited A] → A"] },
    { name := "an instance is found", run := fun _ =>
        okLib (classPrelude ++ "#eval (Inhabited.default : Bool)") [".true"] },
    { name := "instances with instance arguments chain", run := fun _ =>
        okLib (classPrelude ++ "#eval (Inhabited.default : List (List Nat))") [".cons (.cons 0 .nil) .nil"] },
    { name := "local instances", run := fun _ =>
        okLib (classPrelude ++ "def orDefault {A : Type} [Inhabited A] : Option A → A\n  | .some a => a\n  | .none => Inhabited.default\n" ++
          "#eval orDefault (Option.none : Option Bool)") [".true"] },
    { name := "a missing instance is an error", run := fun _ =>
        failsLib (classPrelude ++ "#eval (Inhabited.default : String)") "failed to synthesize an instance of Inhabited String" },
    { name := "output parameters are determined by the instance", run := fun _ =>
        okLib ("import Prelude\nclass HAdd (A B : Type) (C : outParam Type) where\n  hadd : A → B → C\n" ++
          "instance : HAdd Nat Bool Nat where\n  hadd := fun n b => n\n#check HAdd.hadd (3 : Nat) Bool.true")
          ["HAdd.hadd Nat Bool Nat instHAddNatBoolNat (3 : Nat) Bool.true : Nat"] },
    { name := "later instances win", run := fun _ =>
        okLib (classPrelude ++ "instance : Inhabited Nat := Inhabited.mk 7\n#eval (Inhabited.default : Nat)") ["7"] },
    { name := "priorities", run := fun _ =>
        okLib (classPrelude ++ "instance (priority := 2000) : Inhabited Nat := Inhabited.mk 5\n" ++
          "instance : Inhabited Nat := Inhabited.mk 7\n#eval (Inhabited.default : Nat)") ["5"] },
    { name := "tabling: a cyclic instance fails instead of looping", run := fun _ =>
        failsLib ("import Prelude\nclass Loop (A : Type) where\n  x : A\ninstance {A : Type} [Loop A] : Loop A := Loop.mk Loop.x\n" ++
          "#eval (Loop.x : Nat)") "failed to synthesize an instance of Loop Nat" },
    { name := "do notation for any Monad", run := fun _ =>
        okLib ("import Prelude\ninstance : Monad Option where\n  pure := fun a => Option.some a\n" ++
          "  bind := fun x f => match x with\n    | .none => Option.none\n    | .some a => f a\n" ++
          "def addOpt (x y : Option Nat) : Option Nat := do\n  a ← x;\n  b ← y;\n  Monad.pure (a + b)\n" ++
          "#eval addOpt (.some 1) (.some 2)\n#eval addOpt (.some 1) .none") [".some 3", ".none"] },
    { name := "a class's universe is inferred from its fields", run := fun _ =>
        okLib "import Prelude\nclass Functor (f : Type → Type) where\n  map : {A B : Type} → (A → B) → f A → f B\n#check Functor" ["Functor : (Type → Type) → Type 1"] }
  ]

/-- Memoised streams, observed twice and dropped part-way (no leaks, `#run` and native). -/
def memoStreamSrc : String :=
  "import Prelude\ncoinductive Stream (A : Type) where\n  head : A\n  tail : Stream A\n" ++
  "def nats (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => nats (n + 1)\n" ++
  "def sumN : Nat → Stream Nat → Nat\n  | .zero, _ => 0\n  | .succ k, s => s.head + sumN k s.tail\n" ++
  "def twice (s : Stream Nat) : Nat := sumN 100 s + sumN 100 s\n" ++
  "def partly (s : Stream Nat) : Nat := sumN 100 s + sumN 10 s + s.tail.head\n" ++
  "def walk : Nat → Stream Nat → Stream Nat\n  | .zero, s => s\n  | .succ k, s => walk k s.tail\n" ++
  "def main : Nat := twice (nats 0) + partly (nats 0) + (walk 50 (nats 0)).head\n"

def backendGroup : Group where
  name := "backend"
  exercise := "Exercise 8.1"
  cases := [
    { name := "numbers through the IR", run := fun _ =>
        okLib "import Prelude\n#run 100 * 100 + 1" ["10001"] },
    { name := "recursion, without leaks", run := fun _ =>
        okLib "import Prelude\ndef fact : Nat → Nat\n  | .zero => 1\n  | .succ n => (.succ n) * fact n\n#run fact 10" ["3628800"] },
    { name := "lists and strings", run := fun _ =>
        okLib "import Prelude\n#run List.append (.cons (1 : Nat) .nil) (.cons 2 .nil)\n#run String.append \"ab\" \"cd\""
          [".cons 1 (.cons 2 .nil)", "\"abcd\""] },
    { name := "closures capture their variables", run := fun _ =>
        okLib "import Prelude\ndef adder (n : Nat) : Nat → Nat := fun x => x + n\ndef twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)\n#run twice (adder 10) 1"
          ["21"] },
    { name := "codata is lazy", run := fun _ =>
        okLib (streamPrelude ++ "#run (nats .zero).tail.tail.head") [".succ (.succ .zero)"] },
    { name := "codata built by cocon (register) and coit (mealy)", run := fun _ =>
        okLib (streamPrelude ++ registerSrc ++ "#run (register Nat.zero (mealy (fun (n : Nat) (x : Nat) => (.succ n, n)) .zero (nats .zero))).tail.tail.head")
          [".succ .zero"] },
    { name := "sized recursion", run := fun _ =>
        okLib (runPrelude ++ "#run fib (.succ (.succ (.succ (.succ (.succ .zero)))))")
          [".succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))"] },
    { name := "memoised codata, without leaks (also dropped part-way)", run := fun _ =>
        okLib (memoStreamSrc ++ "#run main") ["14946"] },
    { name := "infinitary data", run := fun _ =>
        okLib (treePrelude ++ "#run Tree.depthAt (.node (fun i => .node (fun j => .leaf))) 3") ["3"] },
    { name := "type class dictionaries", run := fun _ =>
        okLib (classPrelude ++ "#run (Inhabited.default : List (List Nat))") [".cons (.cons 0 .nil) .nil"] },
    { name := "the IR, with reference counting (Exercise 8.1)", run := fun _ =>
        okLib "import Prelude\ndef twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)\n#ir twice"
          ["def twice x0 x1 :=\n  dup x0\n  let x2 := ap x0 x1\n  let x3 := ap x0 x2\n  ret x3"] },
    { name := "reuse: a dead cell is reused for a new one (Exercise 8.3)", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let src := "import Prelude\ndef inc : List Nat → List Nat\n  | .nil => .nil\n  | .cons x xs => .cons (x + 1) (inc xs)\n#ir inc\n#run inc (.cons 1 (.cons 2 .nil))"
        let s := runFrontend (R := ZeroOneMany) src { loader := fun _ => some prelude }
        let texts := s.messages.toList.map (·.text)
        check (texts.any fun t => (t.splitOn "reuse").length > 1) s!"no reuse in {texts}"
        check (texts.contains ".cons 2 (.cons 3 .nil)") s!"wrong result: {texts}" },
    { name := "unused parameters are borrowed (the caller drops them)", run := fun _ =>
        okLib "import Prelude\ndef k (x y : List Nat) : List Nat := x\n#ir k"
          ["def k x0 @&x1 :=\n  ret x0"] }
  ]

/-- Programs for the reuse tests: functions that take a cell apart and rebuild it after one
or two `case`s on a `Bool` returned by a call; a zipper insertion into a binary tree;
and a structure updated through calls (`record`, as `drafts/rust/lowered/07`). -/
def reuseSrc : String := "import Prelude
inductive T where
  | a (x : Nat) (y : Nat)
  | b (x : Nat) (y : Nat)
def small : Nat → Bool
  | .zero => .true
  | .succ _ => .false
def f (t : T) : T := match t with
  | .a x y => (match small x with
    | .true => T.b y x
    | .false => T.a y x)
  | .b x y => T.b y x
def g (t : T) : T := match t with
  | .a x y => (match small x with
    | .true => (match small y with
      | .true => T.b y x
      | .false => T.a x x)
    | .false => T.a y x)
  | .b x y => T.b y x
def h (t u : T) : T := match t with
  | .a x y => (match small x with
    | .true => u
    | .false => T.a y x)
  | .b x y => T.b y x
structure Stats where
  hits : Nat
  misses : Nat
def step (n : Nat) : Option Nat := match small n with
  | .true => .none
  | .false => .some (Nat.succ n)
def bump2 (a b : Nat) : Option (Nat × Nat) := match step a with
  | .some a => .some (a, Nat.succ (Nat.succ b))
  | .none => .none
def record (s : Stats) : Option Stats := match s with
  | (h, m, _) => match step h with
    | .some h => (match bump2 h m with
      | .some r => .some (Stats.mk r.1 r.2)
      | .none => .none)
    | .none => .none
inductive Tree where
  | leaf
  | node (key : Nat) (left : Tree) (right : Tree)
inductive Path where
  | top
  | inLeft (key : Nat) (right : Tree) (up : Path)
  | inRight (key : Nat) (left : Tree) (up : Path)
def Path.plug : Path → Tree → Tree
  | .top, t => t
  | .inLeft key right up, t => Path.plug up (Tree.node key t right)
  | .inRight key left up, t => Path.plug up (Tree.node key left t)
def Tree.insert (k : Nat) : Tree → Path → Tree
  | .node key left right, path => (match Nat.lt k key with
    | .true => Tree.insert k left (Path.inLeft key right path)
    | .false => match Nat.lt key k with
      | .true => Tree.insert k right (Path.inRight key left path)
      | .false => Path.plug path (Tree.node key left right))
  | .leaf, path => Path.plug path (Tree.node k .leaf .leaf)
def spine : Nat → Nat → Tree
  | i, .zero => Tree.leaf
  | i, .succ m => Tree.node i Tree.leaf (spine (Nat.succ i) m)
def ta : T := T.a 1 2
def fa : T := f (T.a 1 2)
def fb : T := f (T.a 0 2)
def ga : T := g (T.a 0 0)
def gb : T := g (T.a 0 1)
def gc : T := g (T.a 1 1)
def ha : T := h (T.a 0 5) (T.b 1 1)
def hb : T := h (T.a 1 5) (T.b 1 1)
def s0 : Stats := Stats.mk 1 2
def r0 : Option Stats := record (Stats.mk 1 2)
def t10 : Tree := spine 1 10
def t20 : Tree := spine 1 20
def z10 : Tree := Tree.insert 11 (spine 1 10) Path.top
def z20 : Tree := Tree.insert 21 (spine 1 20) Path.top
"

def reuseState : IO (CommandState ZeroOneMany) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let s := runFrontend (R := ZeroOneMany) reuseSrc { loader := fun m => if m == "Prelude" then some prelude else none }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render reuseSrc
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure s

/-- Run each entry point of `reuseSrc` through the optimised IR on the checked heap: the
objects allocated (a leak, or using a freed object, is an error). -/
def reuseAllocs (entries : List Name) : IO (List Nat) := do
  let s ← reuseState
  entries.mapM fun n => do
    let r : Except String Nat := do
      let code ← (compileReachable s.globals s.builtins [n]).mapError toString
      let decls ← IR.lowerProgram code (.global n)
      let (_, a) ← IR.runProgram (IR.optimizeProgram decls)
      pure a
    match r with
    | .ok a => pure a
    | .error e => throw (IO.userError s!"{n}: {e}")

/-- The optimised IR of a function of `reuseSrc`, as lines. -/
def reuseIR (n : Name) : IO (List String) := do
  let s ← reuseState
  match (do
      let code ← (compileReachable s.globals s.builtins [n]).mapError toString
      IR.lowerProgram code (.global n) : Except String (Array IR.Decl)) with
  | .ok decls =>
    let d := ((IR.optimizeProgram decls).find? (·.name == n)).get!
    pure ((d.toString.splitOn "\n").map (·.trimAscii.toString))
  | .error e => throw (IO.userError e)

/-- Only the parameter `x0` is reset (a `Bool` returned by `small` is never paired). -/
def onlyParamReset (n : Name) : IO Unit := do
  let ls ← reuseIR n
  let resets := ls.filter fun l => (l.splitOn ":= reset").length > 1
  check (!resets.isEmpty && resets.all (·.endsWith ":= reset x0")) s!"resets: {resets}\n{"\n".intercalate ls}"

def reuseGroup : Group where
  name := "reuse"
  exercise := "Stage 8c"
  cases := [
    { name := "across one case: the cell is rebuilt in both branches, no allocation", run := fun _ => do
        checkEq [1, 1, 1] (← reuseAllocs ["ta", "fa", "fb"])
        onlyParamReset "f" },
    { name := "across nested cases", run := fun _ => do
        checkEq [1, 1, 1] (← reuseAllocs ["ga", "gb", "gc"])
        onlyParamReset "g" },
    { name := "a branch that doesn't rebuild frees the token (no leak)", run := fun _ => do
        checkEq [2, 2] (← reuseAllocs ["ha", "hb"])
        let ls ← reuseIR "h"
        check (ls.any fun l => l.endsWith ":= reuse x1000000 in ctor 0") s!"no freed token:\n{"\n".intercalate ls}" },
    { name := "a Bool returned by a call is never reset", run := fun _ => do
        onlyParamReset "f"; onlyParamReset "g"; onlyParamReset "h" },
    { name := "a zipper insertion allocates nothing per level", run := fun _ => do
        let [t10, t20, z10, z20] ← reuseAllocs ["t10", "t20", "z10", "z20"] | throw (IO.userError "?")
        -- the tree, and the new node
        checkEq (t10 + 1, t20 + 1) (z10, z20) },
    { name := "a structure updated through calls reuses its own cells, in place", run := fun _ => do
        let [s0, r0] ← reuseAllocs ["s0", "r0"] | throw (IO.userError "?")
        let ls ← reuseIR "record"
        -- `Stats` is one pair since 22i (its last field is unboxed): the parameter's cell
        -- holds the new one
        check (ls.any fun l => (l.splitOn ":= reuse x1000000 in ctor 0 ").length > 1 &&
            ((l.splitOn ":= reuse x1000000 in ctor 0 ")[1]!.splitOn " ").length == 2)
          s!"the parameter's cell is not rebuilt in place:\n{"\n".intercalate ls}"
        -- the two `step`s' options and bump2's result (an option and a pair) are the only
        -- allocations: the new `Stats` takes the parameter's cell
        checkEq (s0 + 4) r0 },
    { name := "renaming a body renames reset and reuse", run := fun _ => do
        let b : IR.Body := .vdecl 5 (.reset 1) (.vdecl 6 (.reuse 5 0 #[2, 3]) (.ret 6))
        let σ : Std.HashMap IR.Var IR.Var := ({} : Std.HashMap _ _).insert 1 10 |>.insert 2 20 |>.insert 3 30
        let ls := ((IR.Body.rename σ b).toString.splitOn "\n").map (·.trimAscii.toString)
        checkEq ["let x5 := reset x10", "let x6 := reuse x5 in ctor 0 x20 x30", "ret x6"] ls }
  ]

/-- Programs for the borrowing tests (stage 8e): functions that only look at their
argument, a closure over one, and a pair taken apart at once. -/
def borrowSrc : String := "import Prelude
def len : List Nat → Nat
  | .nil => 0
  | .cons _ xs => Nat.succ (len xs)
def sumAcc : Nat → List Nat → Nat
  | acc, .nil => acc
  | acc, .cons x xs => sumAcc (Nat.add acc x) xs
inductive Tree where
  | leaf
  | node (key : Nat) (left : Tree) (right : Tree)
def Tree.mem (k : Nat) : Tree → Bool
  | .leaf => .false
  | .node key l r => match Nat.lt k key with
    | .true => Tree.mem k l
    | .false => match Nat.lt key k with
      | .true => Tree.mem k r
      | .false => .true
def mapL (f : List Nat → Nat) : List (List Nat) → List Nat
  | .nil => .nil
  | .cons x xs => .cons (f x) (mapL f xs)
def split (xs : List Nat) : List Nat × List Nat := (xs, xs)
def both (xs : List Nat) : Nat := match split xs with
  | (a, b) => Nat.add (len a) (len b)
def t3 : Tree := Tree.node 2 (Tree.node 1 .leaf .leaf) (Tree.node 3 .leaf .leaf)
"

/-- The optimised IR of a function of `borrowSrc`, as lines. -/
def borrowIR (n : Name) : IO (List String) := do
  let s := runFrontend (R := ZeroOneMany) borrowSrc { loader := ← preludeLoader }
  match (do
      let code ← (compileReachable s.globals s.builtins [n]).mapError toString
      IR.lowerProgram code (.global n) : Except String (Array IR.Decl)) with
  | .ok decls =>
    let d := ((IR.optimizeProgram decls).find? (·.name == n)).get!
    pure ((d.toString.splitOn "\n").map (·.trimAscii.toString))
  | .error e => throw (IO.userError e)

/-- Parameter `x{i}` of `n` is borrowed and never counted. -/
def borrowedUncounted (n : Name) (i : Nat) : IO Unit := do
  let ls ← borrowIR n
  let hdr := ls.headD ""
  check ((hdr.splitOn s!"@&x{i} ").length > 1 || hdr.endsWith s!"@&x{i} :=") s!"x{i} not borrowed:\n{"\n".intercalate ls}"
  check (!ls.any fun l => l == s!"dup x{i}" || l == s!"drop x{i}") s!"x{i} counted:\n{"\n".intercalate ls}"

/-- Build `main` with the C backend and compare its printed value. Skipped (passes) if
the C toolchain can't find GMP: give the suite a toolchain (`Tests/Main.lean`) to run these. -/
def cRun (src : String) (expected : String) (llvm : Bool := false) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) src { loader := ← preludeLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal (← toolchain) s "main" dir llvm with
  | .ok v => checkEq expected v
  | .error e =>
    let missing := ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1
    if missing then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)

/-- A program that projects field 1 of a number (the old unary-view fallback: since
`proj` is borrowed, the objects it made would leak). Lowering never emits this. -/
def projOfNumber : Array IR.Decl :=
  #[{ name := "wiz.entry", params := #[],
      body := .vdecl 0 (.lit 5) (.vdecl 1 (.proj 1 0) (.ret 1)) }]

def borrowGroup : Group where
  name := "borrow"
  exercise := "Stage 8e"
  cases := [
    { name := "the length of a list borrows it", run := fun _ => borrowedUncounted "len" 0 },
    { name := "a left fold borrows the list (and keeps its tail call)", run := fun _ => do
        borrowedUncounted "sumAcc" 1
        let ls ← borrowIR "sumAcc"
        check (ls.any fun l => l.startsWith "let " && (l.splitOn ":= sumAcc").length > 1) s!"no call:\n{"\n".intercalate ls}" },
    { name := "a lookup in a tree borrows the tree", run := fun _ => borrowedUncounted "Tree.mem" 1 },
    { name := "comparisons borrow: the key and the keys it meets are not counted", run := fun _ => do
        borrowedUncounted "Tree.mem" 0
        let ls ← borrowIR "Tree.mem"
        check (!ls.any fun l => l.startsWith "dup " || l.startsWith "drop ") s!"counted:\n{"\n".intercalate ls}"
        -- big numbers are objects: a borrowing comparison must neither free nor leak them
        let big := "1180591620717411303424"
        cRun (borrowSrc ++ s!"def tb : Tree := Tree.node (Nat.add {big} 2) (Tree.node {big} .leaf .leaf) .leaf\n" ++
          s!"def b2n : Bool → Nat\n  | .true => 1\n  | .false => 0\n" ++
          s!"def main : Nat := Nat.add (b2n (Tree.mem {big} tb)) (Nat.add (b2n (Tree.mem (Nat.add {big} 1) tb)) (b2n (Tree.mem (Nat.add {big} 2) tb)))\n") "2" },
    { name := "borrowing functions run without leaks", run := fun _ =>
        okLib (borrowSrc ++ "#run len (.cons 1 (.cons 2 .nil))\n#run sumAcc 0 (.cons 1 (.cons 2 .nil))\n#run Tree.mem 3 t3\n#run Tree.mem 4 t3")
          ["2", "3", ".true", ".false"] },
    { name := "a closure over a borrowing function goes through an owned wrapper", run := fun _ => do
        okLib (borrowSrc ++ "#run mapL len (.cons (.cons 1 .nil) (.cons .nil .nil))") [".cons 1 (.cons 0 .nil)"]
        let s := runFrontend (R := ZeroOneMany) (borrowSrc ++ "def lens : List Nat := mapL len (.cons .nil .nil)\n") { loader := ← preludeLoader }
        match (do
            let code ← (compileReachable s.globals s.builtins ["lens"]).mapError toString
            IR.lowerProgram code (.global "lens") : Except String (Array IR.Decl)) with
        | .ok decls =>
          let ds := IR.optimizeProgram decls
          check (ds.any (·.name == "len._owned")) "no wrapper"
          check (ds.all fun d => (d.toString.splitOn "pap len ").length == 1) "len partially applied directly"
        | .error e => throw (IO.userError e) },
    { name := "drop specialisation: a unique pair taken apart moves its fields", run := fun _ => do
        let ls ← borrowIR "both"
        check (ls.any fun l => (l.splitOn "prim dropMoved").length > 1) s!"no specialised drop:\n{"\n".intercalate ls}"
        okLib (borrowSrc ++ "#run both (.cons 1 (.cons 2 .nil))") ["4"] },
    { name := "proj of a field of a number stops the IR interpreter and the C runtime", run := fun _ => do
        match IR.runProgram projOfNumber with
        | .ok _ => throw (IO.userError "the IR interpreter projected a number")
        | .error e => check ((e.splitOn "internal error: proj 1 of the number 5").length > 1) e
        let dir ← IO.FS.createTempDir
        let exe := dir / "proj"
        match ← Build.compileC (← toolchain) (C.program projOfNumber) exe with
        | .error e =>
          if (e.splitOn "gmp.h").length > 1 then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)
        | .ok () =>
          let out ← IO.Process.output { cmd := exe.toString }
          checkEq 3 out.exitCode
          check ((out.stderr.splitOn "internal error: proj").length > 1) out.stderr },
    { name := "borrowing and drop specialisation in C", run := fun _ =>
        cRun (borrowSrc ++ "def main : Nat := Nat.add (both (.cons 1 (.cons 2 .nil))) (len (mapL len (.cons .nil .nil)))\n") "5" }
  ]

/-- Build `main : IO _` with the C backend (and the `IO` library) and compare its output. -/
def ioRun (src : String) (expected : String) (args : Array String := #[]) (llvm : Bool := false) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let effLib ← IO.FS.readFile "lib/Eff.wiz"
  let stdLib ← IO.FS.readFile "lib/Std.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Eff" then some effLib
    else if m == "Std" then some stdLib else none
  let headers ← Build.preprocessHeaders (← toolchain) src
  let s := runFrontend (R := ZeroOneMany) src { loader, cHeaders := (headers[·]?) }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal (← toolchain) s "main" dir llvm (timeout := some 120) (args := args) with
  | .ok v => checkEq expected v
  | .error e =>
    let missing := ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1
    if missing then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)

def ioFails (src : String) (fragment : String) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let effLib ← IO.FS.readFile "lib/Eff.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Eff" then some effLib else none
  let s := runFrontend (R := ZeroOneMany) src { loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

def ffiGroup : Group where
  name := "ffi"
  exercise := "Stage 9a"
  cases := [
    { name := "IO actions run in order", run := fun _ =>
        ioRun "import IO\ndef main : IO Unit := do\n  IO.println \"one\";\n  IO.println \"two\"" "one\ntwo\n" },
    { name := "the world is linear: it can't be duplicated", run := fun _ =>
        ioFails "import IO\ndef bad (x : IO Unit) : IO Unit := fun w =>\n  let 1 (a, w') := x w; x w" "quantity 1" },
    { name := "machine integers and floats", run := fun _ =>
        ioRun ("import IO\ndef main : IO Unit := do\n" ++
          "  IO.println (Nat.toString (UInt64.toNat (UInt64.mul (UInt64.ofNat 1000000) (UInt64.ofNat 1000000))));\n" ++
          "  IO.println (Float64.toString (Float64.div (Float64.ofNat 1) (Float64.ofNat 4)))") "1000000000000\n0.25\n" },
    { name := "strings are marshalled as UTF-8", run := fun _ =>
        ioRun "import IO\ndef main : IO Unit := IO.println \"λ ✓\"" "λ ✓\n" },
    { name := "a C library function, through its header", run := fun _ =>
        ioRun ("import IO\nextern \"strlen\" (header := \"string.h\") strlen : String → Nat\n" ++
          "def main : IO Unit := IO.println (Nat.toString (strlen \"hello\"))") "5\n" },
    { name := "import_c binds a header's functions", run := fun _ =>
        ioRun ("import IO\nimport_c \"string.h\"\nimport_c \"stdlib.h\" (pure)\ndef main : IO Unit := do\n" ++
          "  n ← C.strlen \"hello, world\";\n  IO.println (Nat.toString n);\n  IO.println (Nat.toString (C.atoi \"42\"))") "12\n42\n" },
    { name := "the C subset parser (Exercise 9.1)", run := fun _ => do
        let fs := FFI.parseHeader "typedef unsigned long size_t;\nextern size_t strlen (const char *__s) __attribute__ ((__pure__));\nstruct S { int x; };\ntypedef int (*cmp_t)(const void *, const void *);\nvoid qsort(void *b, size_t n, size_t s, cmp_t c);\nstatic inline int twice(int x) { return 2 * x; }\nint printf(const char *f, ...);"
        checkEq "[strlen, qsort, twice, printf]" (toString (fs.toList.map (·.name)))
        checkEq "true" (toString (fs.toList.find? (·.name == "printf") |>.map (·.variadic) |>.getD false))
        let q := (fs.toList.find? (·.name == "qsort")).get!
        checkEq "true" (toString (q.params.getLast! == FFI.CType.other "function pointer")) },
    { name := "glue: checked C snippets", run := fun _ =>
        ioRun ("import IO\nimport_c \"string.h\"\n" ++
          "glue sumTo (n : Nat) : Nat := \"uint64_t s = 0; for (uint64_t i = 0; i < n; i++) s += i; return s;\"\n" ++
          "glue twiceLen (s : String) : Nat := \"return strlen(s) * 2;\"\n" ++
          "def main : IO Unit := do\n  IO.println (Nat.toString (sumTo 100));\n  IO.println (Nat.toString (twiceLen \"hello\"))")
          "4950\n10\n" },
    { name := "glue: no pointers (Exercise 9.2)", run := fun _ =>
        ioFails "import IO\nglue bad (n : Nat) : Nat := \"return *n;\"" "pointer dereference" },
    { name := "glue: no indexing", run := fun _ =>
        ioFails "import IO\nglue bad (s : String) : Nat := \"return s[0];\"" "indexing" },
    { name := "glue: only declared functions", run := fun _ =>
        ioFails "import IO\nglue bad (n : Nat) : Nat := \"return system(n);\"" "unknown C function system" },
    { name := "observing codata is memoised", run := fun _ =>
        -- `noisy` prints when it runs. Building `s` unfolds `counter 0` (one step: the
        -- next state is computed with the payload); the first `s.head` unfolds `s` and
        -- overwrites it with its payload, so the second doesn't (`wiz_lazy_set`).
        ioRun ("import IO\nimport_c \"stdio.h\" (pure)\ncoinductive Stream (A : Type) where\n  head : A\n  tail : Stream A\n" ++
          "def noisy (n : Nat) : Nat := n + 0 * C.puts \"step\"\n" ++
          "def counter (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => counter (noisy (n + 1))\n" ++
          "def main : IO Unit := do\n  let s := (counter 0).tail;\n  IO.println (Nat.toString s.head);\n  IO.println (Nat.toString s.head)")
          "step\nstep\n1\n1\n" },
    { name := "a long stream observed twice computes each element once", run := fun _ =>
        ioRun ("import IO\nimport_c \"stdio.h\" (pure)\ncoinductive Stream (A : Type) where\n  head : A\n  tail : Stream A\n" ++
          "def noisy (n : Nat) : Nat := n + 0 * C.puts \"step\"\n" ++
          "def counter (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => counter (noisy (n + 1))\n" ++
          "def sumN : Nat → Stream Nat → Nat\n  | .zero, _ => 0\n  | .succ k, s => s.head + sumN k s.tail\n" ++
          "def main : IO Unit := do\n  let s := counter 0;\n  IO.println (Nat.toString (sumN 1000 s));\n  IO.println (Nat.toString (sumN 1000 s))")
          (String.join (List.replicate 1000 "step\n") ++ "499500\n499500\n") },
    { name := "glue: types are checked", run := fun _ =>
        ioFails "import IO\nglue bad (n : Nat) : String := \"return n + 1;\"" "expected a string" },
    { name := "foreign pointers are released by their finalizer", run := fun _ =>
        ioRun ("import IO\nforeign_type FILE (finalizer := \"fclose\")\n" ++
          "extern \"fopen\" (header := \"stdio.h\") fopen : String → String → IO FILE\n" ++
          "extern \"fputs\" (header := \"stdio.h\") fputs : String → FILE → IO Nat\n" ++
          "def main : IO Unit := do\n  f ← fopen \"/tmp/wiz_test_fin.txt\" \"w\";\n  n ← fputs \"closed\\n\" f;\n" ++
          "  s ← IO.readFile \"/tmp/wiz_test_fin.txt\";\n  IO.print s") "closed\n" },
    { name := "byte buffers", run := fun _ =>
        ioRun ("import IO\ndef fill : Nat → Bytes → Bytes\n  | .zero, b => b\n  | .succ n, b => Bytes.push (fill n b) (65 + n)\n" ++
          "def main : IO Unit := do\n  IO.println (Bytes.toString (fill 3 Bytes.empty));\n" ++
          "  IO.println (Nat.toString (Bytes.size (Bytes.ofString \"λx\")))") "ABC\n3\n" },
    { name := "foreign types are checked", run := fun _ =>
        ioFails "import IO\nextern \"f\" f : (Nat → Nat) → Nat" "foreign function" }
  ]

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

-- the generators of Wiz source moved to `Wiz/Selfhost.lean` (grail builds the
-- self-hosted toolchain too); the names stay here for the scripts that use them
export Wiz.Selfhost (wizLit wizPD wizList wizTables)

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

/-- Level expressions over parameters, for the declaration test. -/
inductive MLvl where
  | num (n : Nat)
  | param (u : String)
  | succ (l : MLvl)
  | max (a b : MLvl)
  | imax (a b : MLvl)
  deriving Inhabited

def MLvl.toWiz : MLvl → String
  | num n => s!"(.lnum {n})"
  | param u => s!"(.lparam \"{u}\")"
  | succ l => s!"(.lsucc {l.toWiz})"
  | max a b => s!"(.lmax {a.toWiz} {b.toWiz})"
  | imax a b => s!"(.limax {a.toWiz} {b.toWiz})"

def MLvl.toLevel : MLvl → Level
  | num n => Level.ofNat n
  | param u => .param u
  | succ l => .succ l.toLevel
  | max a b => .max a.toLevel b.toLevel
  | imax a b => .imax a.toLevel b.toLevel

def MLvl.pretty : MLvl → String
  | num n => toString n
  | param u => u
  | succ l => s!"({l.pretty})+1"
  | max a b => s!"max({a.pretty}, {b.pretty})"
  | imax a b => s!"imax({a.pretty}, {b.pretty})"

/-- A random level over `u` and `v`. -/
partial def MLvl.gen (s : Nat) (depth : Nat) : MLvl × Nat :=
  let s := (s * 1103515245 + 12345) % 2147483648
  if depth == 0 then
    match s / 7 % 4 with
    | 0 => (num (s / 11 % 3), s)
    | 1 => (param "u", s)
    | 2 => (param "v", s)
    | _ => (num 0, s)
  else match s / 7 % 5 with
    | 0 => let (l, s) := gen s (depth - 1); (succ l, s)
    | 1 => let (a, s) := gen s (depth - 1); let (b, s) := gen s (depth - 1); (max a b, s)
    | 2 => let (a, s) := gen s (depth - 1); let (b, s) := gen s (depth - 1); (imax a b, s)
    | _ => gen s 0

/-- An equivalent level, by rewriting with identities that hold at every level. -/
partial def MLvl.rewrite (s : Nat) : MLvl → MLvl × Nat
  | l =>
    let s := (s * 1103515245 + 12345) % 2147483648
    match l, s / 7 % 6 with
    | max a b, 0 => let (b, s) := rewrite s b; let (a, s) := rewrite s a; (max b a, s)
    | max a b, 1 => let (a, s) := rewrite s a; (max a (max b a), s)
    | succ (max a b), 2 => (max (succ a) (succ b), s)
    | imax a (succ b), 3 => (max a (succ b), s)
    | imax a b, 4 => let (a, s) := rewrite s a; (imax (max a b) b, s)
    | succ l, _ => let (l, s) := rewrite s l; (succ l, s)
    | max a b, _ => let (a, s) := rewrite s a; let (b, s) := rewrite s b; (max a b, s)
    | imax a b, _ => let (a, s) := rewrite s a; let (b, s) := rewrite s b; (imax a b, s)
    | l, 5 => (max l (num 0), s)
    | l, _ => (l, s)

/-- The core calculus of `selfhost/Kernel.wiz`, for differential tests against the
Lean kernel. -/
inductive MTm where
  | var (i : Nat)
  | univ (n : Nat)
  | pi (a b : MTm)
  | lam (b : MTm)
  | app (f a : MTm)
  | letE (ty v b : MTm)
  | ann (t ty : MTm)
  | sigma (a b : MTm)
  | pair (a b : MTm)
  | fst (p : MTm)
  | snd (p : MTm)
  | unit (n : Nat)
  | star
  | empty (n : Nat)
  | exfalso (m t : MTm)
  | enum (k : Nat)
  | tag (k i : Nat)
  | ecase (m s : MTm) (bs : List MTm)
  | prop
  | ptrue
  | pfalse
  | eq (A a b : MTm)
  | eqTy (A B : MTm)
  | refl (A a : MTm)
  | reflTy (X : MTm)
  | cast (A B e t : MTm)
  | transp (A a P p b e : MTm)
  | desc (l : Nat) (I : MTm)
  | dret (i : MTm)
  | darg (S E : MTm)
  | drec (j E : MTm)
  | dhrec (H j E : MTm)
  | delim (v : Nat) (P a b c h D : MTm)
  | mu (l : Nat) (I D i : MTm)
  | con (x : MTm)
  | ind (l : Nat) (I D : MTm) (v : Nat) (P m i x : MTm)
  /-- a global, from `globalDefs`, at some universe levels -/
  | const (name : String) (levels : List Nat := [])
  /-- `Sort u` for a level parameter (inside universe-polymorphic globals) -/
  | sortParam (u : String)
  /-- `Sort l` for any level expression -/
  | sortLv (l : MLvl)
  /-- binders with a quantity other than ω: `0` or `1` -/
  | piq (q : ZeroOneMany) (a b : MTm)
  | sigmaq (q : ZeroOneMany) (a b : MTm)
  | letq (q : ZeroOneMany) (ty v b : MTm)
  | size
  | szInf
  | szSuc (s : MTm)
  | sizeLt (s : MTm)
  | mus (l : Nat) (I D i s : MTm)
  | sfix (l : Nat) (I D : MTm) (v : Nat) (P f s i x : MTm)
  | nu (l : Nat) (I D i s : MTm)
  | out (x : MTm)
  | cocon (x : MTm)
  | scofix (l : Nat) (I D A f s i a : MTm)
  | coit (l : Nat) (I D S st i s : MTm)
  | scase (l : Nat) (I D : MTm) (v : Nat) (P m s i x : MTm)
  /-- a `Π`/`Σ` with its sort (level `l`) -/
  | sorted (l : Nat) (t : MTm)
  /-- `ULift A` in `Sort l` (Q4), its constructor and eliminator -/
  | ulift (l : Nat) (A : MTm)
  | up (a : MTm)
  | down (t : MTm)
  deriving Inhabited

namespace MTm

/-- The global definitions (or axioms, without a value) the differential test uses, in
order. -/
def natD0 : MTm := darg (enum 2) (lam (ecase (desc 0 (unit 0)) (var 0) [dret star, drec star (dret star)]))
def globalDefs : List (String × List String × Option MTm × MTm) :=
  [("idU", [], some (lam (var 0)), pi (univ 0) (univ 0)),
   ("Nat", [], some (mu 0 (unit 0) natD0 star), univ 0),
   ("zero", [], some (ann (con (pair (tag 2 0) (pair star star))) (const "Nat")), const "Nat"),
   ("one", [], some (ann (con (pair (tag 2 1) (pair (const "zero") (pair star star)))) (const "Nat")), const "Nat"),
   ("twice", [], some (lam (lam (app (var 1) (app (var 1) (var 0))))), pi (pi (univ 0) (univ 0)) (pi (univ 0) (univ 0))),
   ("A", [], none, univ 0),
   ("a", [], none, const "A"),
   -- universe-polymorphic
   ("idP", ["u"], some (lam (lam (var 0))), pi (sortParam "u") (pi (var 0) (var 1))),
   ("constP", ["u", "v"], some (lam (lam (lam (lam (var 1))))),
     pi (sortParam "u") (pi (sortParam "v") (pi (var 1) (pi (var 1) (var 3)))))]

def qWiz : ZeroOneMany → String
  | .zero => ".qz"
  | .one => ".qo"
  | .many => ".qw"

def labels (k : Nat) : List Name := (List.range k).map (s!"a{·}")

partial def toWiz : MTm → String
  | var i => s!"(.var {i})"
  | univ n => s!"(.univ {n})"
  | pi a b => s!"(.pi {a.toWiz} {b.toWiz})"
  | lam b => s!"(.lam {b.toWiz})"
  | app f a => s!"(.app {f.toWiz} {a.toWiz})"
  | letE t v b => s!"(.letE {t.toWiz} {v.toWiz} {b.toWiz})"
  | ann t ty => s!"(.ann {t.toWiz} {ty.toWiz})"
  | sigma a b => s!"(.sigma {a.toWiz} {b.toWiz})"
  | pair a b => s!"(.pair {a.toWiz} {b.toWiz})"
  | fst p => s!"(.fst {p.toWiz})"
  | snd p => s!"(.snd {p.toWiz})"
  | unit n => s!"(.unit {n})"
  | star => ".star"
  | empty n => s!"(.empty {n})"
  | exfalso m t => s!"(.exfalso {m.toWiz} {t.toWiz})"
  | enum k => s!"(.enum {k})"
  | tag k i => s!"(.tag {k} {i})"
  | ecase m s bs => s!"(.ecase {m.toWiz} {s.toWiz} {bs.foldr (fun b acc => s!"(.tcons {b.toWiz} {acc})") ".tnil"})"
  | prop => ".prop"
  | ptrue => ".ptrue"
  | pfalse => ".pfalse"
  | eq A a b => s!"(.eq {A.toWiz} {a.toWiz} {b.toWiz})"
  | eqTy A B => s!"(.eqTy {A.toWiz} {B.toWiz})"
  | refl A a => s!"(.eqRefl {A.toWiz} {a.toWiz})"
  | reflTy X => s!"(.tyRefl {X.toWiz})"
  | sorted l t => s!"(.sorted (.lnum {l}) {t.toWiz})"
  | cast A B e t => s!"(.coe {A.toWiz} {B.toWiz} {e.toWiz} {t.toWiz})"
  | transp A a P p b e => s!"(.subst {A.toWiz} {a.toWiz} {P.toWiz} {p.toWiz} {b.toWiz} {e.toWiz})"
  | desc l I => s!"(.descr {l} {I.toWiz})"
  | dret i => s!"(.dret {i.toWiz})"
  | darg S E => s!"(.darg {S.toWiz} {E.toWiz})"
  | drec j E => s!"(.drec {j.toWiz} {E.toWiz})"
  | dhrec H j E => s!"(.dhrec {H.toWiz} {j.toWiz} {E.toWiz})"
  | delim v P a b c h D => s!"(.delim {v} {P.toWiz} {a.toWiz} {b.toWiz} {c.toWiz} {h.toWiz} {D.toWiz})"
  | mu l I D i => s!"(.mu {l} {I.toWiz} {D.toWiz} {i.toWiz})"
  | con x => s!"(.con {x.toWiz})"
  | ind l I D v P m i x => s!"(.ind {l} {I.toWiz} {D.toWiz} {v} {P.toWiz} {m.toWiz} {i.toWiz} {x.toWiz})"
  | const n ls => match globalDefs.find? (·.1 == n) with
    | some (_, ps, some v, ty) =>
      let psW := ps.foldr (fun p acc => s!"(.cons \"{p}\" {acc})") ".nil"
      let lsW := ls.foldr (fun l acc => s!"(.cons (.lnum {l}) {acc})") ".nil"
      s!"(.const \"{n}\" {psW} {lsW} {v.toWiz} {ty.toWiz})"
    | some (_, _, none, ty) => s!"(.axiomC \"{n}\" {ty.toWiz})"
    | none => "(.var 999)"
  | sortParam u => s!"(.sortL (.lparam \"{u}\"))"
  | sortLv l => s!"(.sortL {l.toWiz})"
  | piq q a b => s!"(.piq {qWiz q} {a.toWiz} {b.toWiz})"
  | sigmaq q a b => s!"(.sigmaq {qWiz q} {a.toWiz} {b.toWiz})"
  | letq q t v b => s!"(.letq {qWiz q} {t.toWiz} {v.toWiz} {b.toWiz})"
  | size => ".size"
  | szInf => ".szInf"
  | szSuc s => s!"(.szSuc {s.toWiz})"
  | sizeLt s => s!"(.sizeLt {s.toWiz})"
  | mus l I D i s => s!"(.mus {l} {I.toWiz} {D.toWiz} {i.toWiz} {s.toWiz})"
  | sfix l I D v P f s i x => s!"(.sfix {l} {I.toWiz} {D.toWiz} {v} {P.toWiz} {f.toWiz} {s.toWiz} {i.toWiz} {x.toWiz})"
  | nu l I D i s => s!"(.nu {l} {I.toWiz} {D.toWiz} {i.toWiz} {s.toWiz})"
  | out x => s!"(.out {x.toWiz})"
  | cocon x => s!"(.cocon {x.toWiz})"
  | scofix l I D A f s i a => s!"(.scofix {l} {I.toWiz} {D.toWiz} {A.toWiz} {f.toWiz} {s.toWiz} {i.toWiz} {a.toWiz})"
  | coit l I D S st i s => s!"(.coit {l} {I.toWiz} {D.toWiz} {S.toWiz} {st.toWiz} {i.toWiz} {s.toWiz})"
  | scase l I D v P m s i x => s!"(.scase {l} {I.toWiz} {D.toWiz} {v} {P.toWiz} {m.toWiz} {s.toWiz} {i.toWiz} {x.toWiz})"
  | ulift l A => s!"(.ulift {l} {A.toWiz})"
  | up a => s!"(.up {a.toWiz})"
  | down t => s!"(.down {t.toWiz})"

partial def toTerm : MTm → Term ZeroOneMany
  | var i => .var i
  | univ n => .sort (Level.ofNat (n + 1))
  | pi a b => .pi "x" .default (.qlit .many) a.toTerm b.toTerm none
  | lam b => .lam "x" b.toTerm
  | app f a => .app f.toTerm a.toTerm
  | letE t v b => .letE "x" (.qlit .many) t.toTerm v.toTerm b.toTerm
  | ann t ty => .ann t.toTerm ty.toTerm
  | sigma a b => .sigma "x" (.qlit .many) a.toTerm b.toTerm none
  | pair a b => .pair a.toTerm b.toTerm
  | fst p => .fst p.toTerm
  | snd p => .snd p.toTerm
  | unit n => .unit (Level.ofNat (n + 1))
  | star => .tt
  | empty n => .empty (Level.ofNat (n + 1))
  | exfalso m t => .absurd m.toTerm t.toTerm
  | enum k => .enum (labels k)
  | tag k i => .tag (labels k) i
  | ecase m s bs => .ecase "z" m.toTerm s.toTerm (bs.map toTerm)
  | prop => .sort .zero
  | ptrue => .unit .zero
  | pfalse => .empty .zero
  | eq A a b => .eq A.toTerm a.toTerm b.toTerm
  | eqTy A B => .eqTy A.toTerm B.toTerm
  | refl A a => .refl A.toTerm a.toTerm
  | reflTy X => .reflTy X.toTerm
  | sorted l t => match t.toTerm with
    | .pi x bi q a b _ => .pi x bi q a b (some (Level.ofNat l))
    | .sigma x q a b _ => .sigma x q a b (some (Level.ofNat l))
    | u => u
  | cast A B e t => .cast A.toTerm B.toTerm e.toTerm t.toTerm
  | transp A a P p b e => .transp A.toTerm a.toTerm P.toTerm p.toTerm b.toTerm e.toTerm
  | desc l I => .desc (Level.ofNat l) I.toTerm
  | dret i => .dret i.toTerm
  | darg S E => .darg (.qlit .many) S.toTerm E.toTerm
  | drec j E => .drec (.qlit .many) j.toTerm E.toTerm
  | dhrec H j E => .dhrec (.qlit .many) H.toTerm j.toTerm E.toTerm
  | delim v P a b c h D => .delim (Level.ofNat v) P.toTerm a.toTerm b.toTerm c.toTerm h.toTerm D.toTerm
  | mu l I D i => .mu (Level.ofNat l) I.toTerm D.toTerm i.toTerm .szInf none
  | con x => .con x.toTerm
  | ind l I D v P m i x => .ind (Level.ofNat l) I.toTerm D.toTerm (Level.ofNat v) P.toTerm m.toTerm i.toTerm x.toTerm
  | const n ls => .const n (ls.map Level.ofNat)
  | sortParam u => .sort (.param u)
  | sortLv l => .sort l.toLevel
  | piq q a b => .pi "x" .default (.qlit q) a.toTerm b.toTerm none
  | sigmaq q a b => .sigma "x" (.qlit q) a.toTerm b.toTerm none
  | letq q t v b => .letE "x" (.qlit q) t.toTerm v.toTerm b.toTerm
  | size => .size
  | szInf => .szInf
  | szSuc s => .szSuc s.toTerm
  | sizeLt s => .sizeLt s.toTerm
  | mus l I D i s => .mu (Level.ofNat l) I.toTerm D.toTerm i.toTerm s.toTerm none
  | sfix l I D v P f s i x => .sfix (Level.ofNat l) I.toTerm D.toTerm (Level.ofNat v) P.toTerm f.toTerm s.toTerm i.toTerm x.toTerm
  | nu l I D i s => .nu (Level.ofNat l) I.toTerm D.toTerm i.toTerm s.toTerm none
  | out x => .out x.toTerm
  | cocon x => .cocon x.toTerm
  | scofix l I D A f s i a => .scofix (Level.ofNat l) I.toTerm D.toTerm A.toTerm f.toTerm s.toTerm i.toTerm a.toTerm
  | coit l I D S st i s => .coit (Level.ofNat l) I.toTerm D.toTerm S.toTerm st.toTerm i.toTerm s.toTerm
  | scase l I D v P m s i x => .scase (Level.ofNat l) I.toTerm D.toTerm (Level.ofNat v) P.toTerm m.toTerm s.toTerm i.toTerm x.toTerm
  | ulift l A => .ulift (Level.ofNat l) A.toTerm
  | up a => .up a.toTerm
  | down t => .down t.toTerm

partial def ofTerm : Term ZeroOneMany → Option MTm
  | .var i => some (var i)
  | .sort l => match l.toNat? with
    | some (n + 1) => some (univ n)
    | some 0 => some prop
    | _ => none
  | .pi _ _ (.qlit .many) a b _ => return pi (← ofTerm a) (← ofTerm b)
  | .pi _ _ (.qlit q) a b _ => return piq q (← ofTerm a) (← ofTerm b)
  | .lam _ b => return lam (← ofTerm b)
  | .app f a => return app (← ofTerm f) (← ofTerm a)
  | .sigma _ (.qlit .many) a b _ => return sigma (← ofTerm a) (← ofTerm b)
  | .sigma _ (.qlit q) a b _ => return sigmaq q (← ofTerm a) (← ofTerm b)
  | .pair a b => return pair (← ofTerm a) (← ofTerm b)
  | .fst p => return fst (← ofTerm p)
  | .snd p => return snd (← ofTerm p)
  | .unit l => match l.toNat? with
    | some (n + 1) => some (unit n)
    | some 0 => some ptrue
    | _ => none
  | .tt => some star
  | .empty l => match l.toNat? with
    | some (n + 1) => some (empty n)
    | some 0 => some pfalse
    | _ => none
  | .absurd m t => return exfalso (← ofTerm m) (← ofTerm t)
  | .enum ls => some (enum ls.length)
  | .tag ls i => some (tag ls.length i)
  | .ecase _ m s bs => return ecase (← ofTerm m) (← ofTerm s) (← bs.mapM ofTerm)
  | .eq A a b => return eq (← ofTerm A) (← ofTerm a) (← ofTerm b)
  | .eqTy A B => return eqTy (← ofTerm A) (← ofTerm B)
  | .refl A a => return refl (← ofTerm A) (← ofTerm a)
  | .reflTy X => return reflTy (← ofTerm X)
  | .cast A B e t => return cast (← ofTerm A) (← ofTerm B) (← ofTerm e) (← ofTerm t)
  | .transp A a P p b e => return transp (← ofTerm A) (← ofTerm a) (← ofTerm P) (← ofTerm p) (← ofTerm b) (← ofTerm e)
  | .desc l I => return desc (← l.toNat?) (← ofTerm I)
  | .dret i => return dret (← ofTerm i)
  | .darg _ S E => return darg (← ofTerm S) (← ofTerm E)
  | .drec _ j E => return drec (← ofTerm j) (← ofTerm E)
  | .dhrec _ H j E => return dhrec (← ofTerm H) (← ofTerm j) (← ofTerm E)
  | .delim v P a b c h D => return delim (← v.toNat?) (← ofTerm P) (← ofTerm a) (← ofTerm b) (← ofTerm c) (← ofTerm h) (← ofTerm D)
  | .mu l I D i .szInf _ => return mu (← l.toNat?) (← ofTerm I) (← ofTerm D) (← ofTerm i)
  | .mu l I D i s _ => return mus (← l.toNat?) (← ofTerm I) (← ofTerm D) (← ofTerm i) (← ofTerm s)
  | .nu l I D i s _ => return nu (← l.toNat?) (← ofTerm I) (← ofTerm D) (← ofTerm i) (← ofTerm s)
  | .out x => return out (← ofTerm x)
  | .cocon x => return cocon (← ofTerm x)
  | .scofix l I D A f s i a => return scofix (← l.toNat?) (← ofTerm I) (← ofTerm D) (← ofTerm A) (← ofTerm f) (← ofTerm s) (← ofTerm i) (← ofTerm a)
  | .coit l I D S st i s => return coit (← l.toNat?) (← ofTerm I) (← ofTerm D) (← ofTerm S) (← ofTerm st) (← ofTerm i) (← ofTerm s)
  | .sfix l I D v P f s i x => return sfix (← l.toNat?) (← ofTerm I) (← ofTerm D) (← v.toNat?) (← ofTerm P) (← ofTerm f) (← ofTerm s) (← ofTerm i) (← ofTerm x)
  | .scase l I D v P m s i x => return scase (← l.toNat?) (← ofTerm I) (← ofTerm D) (← v.toNat?) (← ofTerm P) (← ofTerm m) (← ofTerm s) (← ofTerm i) (← ofTerm x)
  | .size => some size
  | .szInf => some szInf
  | .szSuc s => return szSuc (← ofTerm s)
  | .sizeLt s => return sizeLt (← ofTerm s)
  | .con x => return con (← ofTerm x)
  | .ind l I D v P m i x => return ind (← l.toNat?) (← ofTerm I) (← ofTerm D) (← v.toNat?) (← ofTerm P) (← ofTerm m) (← ofTerm i) (← ofTerm x)
  | .const n us => return const n (← us.mapM Level.toNat?)
  | .ulift l A => return ulift (← l.toNat?) (← ofTerm A)
  | .up a => return up (← ofTerm a)
  | .down t => return down (← ofTerm t)
  | _ => none

/-- Printed like `show .nil` in `Kernel.wiz`. -/
partial def pretty (l : Nat) : MTm → String
  | var i => s!"x{l - i - 1}"
  | univ n => s!"U{n}"
  | pi a b => s!"(x{l} : {pretty l a}) → {pretty (l + 1) b}"
  | lam b => s!"λx{l}. {pretty (l + 1) b}"
  | app f a => s!"({pretty l f} {pretty l a})"
  | letE _ v b => s!"let x{l} := {pretty l v}; {pretty (l + 1) b}"
  | ann t ty => s!"({pretty l t} : {pretty l ty})"
  | sigma a b => s!"(x{l} : {pretty l a}) × {pretty (l + 1) b}"
  | pair a b => s!"({pretty l a}, {pretty l b})"
  | fst p => s!"{pretty l p}.1"
  | snd p => s!"{pretty l p}.2"
  | unit n => s!"Unit{n}"
  | star => "tt"
  | empty n => s!"Empty{n}"
  | exfalso m t => s!"absurd({pretty l m}, {pretty l t})"
  | enum k => s!"Enum{k}"
  | tag _ i => s!"#{i}"
  | ecase m s bs => s!"case({pretty (l + 1) m}, {pretty l s}{String.join (bs.map fun b => ", " ++ pretty l b)})"
  | prop => "Prop"
  | ptrue => "True"
  | pfalse => "False"
  | eq A a b => s!"Eq({pretty l A}, {pretty l a}, {pretty l b})"
  | eqTy A B => s!"EqTy({pretty l A}, {pretty l B})"
  | refl A a => s!"refl({pretty l A}, {pretty l a})"
  | reflTy X => s!"reflTy({pretty l X})"
  | sorted _ t => pretty l t
  | cast A B e t => s!"cast({pretty l A}, {pretty l B}, {pretty l e}, {pretty l t})"
  | transp A a P p b e => s!"transp({pretty l A}, {pretty l a}, {pretty l P}, {pretty l p}, {pretty l b}, {pretty l e})"
  | desc k I => s!"Desc{k}({pretty l I})"
  | dret i => s!"ret({pretty l i})"
  | darg S E => s!"arg({pretty l S}, {pretty l E})"
  | drec j E => s!"rec({pretty l j}, {pretty l E})"
  | dhrec H j E => s!"hrec({pretty l H}, {pretty l j}, {pretty l E})"
  | delim _ P a b c h D => s!"elim({pretty l P}, {pretty l a}, {pretty l b}, {pretty l c}, {pretty l h}, {pretty l D})"
  | mu k I D i => s!"μ{k}({pretty l I}, {pretty l D}, {pretty l i})"
  | con x => s!"con({pretty l x})"
  | ind _ _ _ _ P m i x => s!"ind({pretty l P}, {pretty l m}, {pretty l i}, {pretty l x})"
  | const n ls => if ls.isEmpty then n else n ++ ".{" ++ ", ".intercalate (ls.map toString) ++ "}"
  | sortParam u => s!"Sort {u}"
  | sortLv l => s!"Sort({l.pretty})"
  | piq q a b => s!"(x{l} :{q} {pretty l a}) → {pretty (l + 1) b}"
  | sigmaq q a b => s!"(x{l} :{q} {pretty l a}) × {pretty (l + 1) b}"
  | letq _ _ v b => s!"let x{l} := {pretty l v}; {pretty (l + 1) b}"
  | nu k I D i s => s!"ν{k}({pretty l I}, {pretty l D}, {pretty l i}, {pretty l s})"
  | out x => s!"out({pretty l x})"
  | cocon x => s!"cocon({pretty l x})"
  | scofix _ _ _ A f s i a => s!"scofix({pretty l A}, {pretty l f}, {pretty l s}, {pretty l i}, {pretty l a})"
  | coit _ _ _ S st i s => s!"coit({pretty l S}, {pretty l st}, {pretty l i}, {pretty l s})"
  | sfix _ _ _ _ P f s i x => s!"sfix({pretty l P}, {pretty l f}, {pretty l s}, {pretty l i}, {pretty l x})"
  | scase _ _ _ _ P m s i x => s!"scase({pretty l P}, {pretty l m}, {pretty l s}, {pretty l i}, {pretty l x})"
  | size => "Size"
  | szInf => "∞"
  | szSuc s => s!"↑({pretty l s})"
  | sizeLt s => s!"Size<({pretty l s})"
  | mus k I D i s => s!"μ{k}({pretty l I}, {pretty l D}, {pretty l i}, {pretty l s})"
  | ulift k A => s!"ULift{k}({pretty l A})"
  | up a => pretty l a
  | down t => pretty l t

/-- A well-typed pair (at random levels), for the generator: `(U k, U k)`, or the
dependent `(U k, λx. x) : (A : U (k+1)) × (A → A)`. -/
def wellTypedPair (s : Nat) : MTm :=
  let k := s / 5 % 2
  if s / 3 % 2 == 0 then ann (pair (univ k) (univ k)) (sigma (univ (k + 1)) (univ (k + 1)))
  else ann (pair (univ k) (lam (var 0))) (sigma (univ (k + 1)) (pi (var 0) (var 1)))

def lams : Nat → MTm → MTm
  | 0, b => b
  | k + 1, b => lam (lams k b)

/-- The natural numbers as a description, `arg Enum2 (fun t => case t [ret tt, rec tt (ret tt)])`. -/
def natD : MTm := darg (enum 2) (lam (ecase (desc 0 (unit 0)) (var 0) [dret star, drec star (dret star)]))
def natTy : MTm := mu 0 (unit 0) natD star
def natAt (s : MTm) : MTm := mus 0 (unit 0) natD star s
/-- streams of bits, the stream that alternates (by coiteration), and zeros (by corecursion) -/
def streamD : MTm := darg (enum 2) (lam (drec star (dret star)))
def streamAt (s : MTm) : MTm := nu 0 (unit 0) streamD star s
def streamTy : MTm := streamAt szInf
def alt : MTm := coit 0 (unit 0) streamD (lam (enum 2))
  (lams 2 (pair (var 0) (pair (ecase (enum 2) (var 0) [tag 2 1, tag 2 0]) (pair star star)))) star (tag 2 0)
def zeros : MTm := scofix 0 (unit 0) streamD (lam (unit 0))
  (lams 4 (cocon (pair (tag 2 0) (pair (app (app (var 2) (var 1)) (var 0)) (pair star star))))) szInf star star
def shead (x : MTm) : MTm := fst (out x)
def stail (x : MTm) : MTm := fst (snd (out x))
def natZero : MTm := ann (con (pair (tag 2 0) (pair star star))) natTy
def natSucc (n : MTm) : MTm := ann (con (pair (tag 2 1) (pair n (pair star star)))) natTy

def eqRefl' (A a : MTm) : MTm := refl A a

/-- The proof of `False` from equivalent propositions of different shapes: `True = (True
→ True)` at `Prop`, carried by `transp` to `(True → Unit) = ((True → True) → Unit)`, whose
first component (the domains' equation) was `False` when domains were compared by shape. -/
def propShapes : List MTm :=
  let T1 := sorted 0 (pi ptrue ptrue)
  let G (X : MTm) := sorted 1 (pi X (unit 0))
  let e := ann (pair (lam (lam (var 0))) (lam star)) (eq prop ptrue T1)
  let bad := transp prop ptrue (lam (lam (eqTy (G ptrue) (G (var 1))))) (reflTy (G ptrue)) T1 e
  let erasedArg (A : MTm) := app (ann (lam star) (piq .zero A (unit 0))) (fst bad)
  [erasedArg pfalse, erasedArg (eqTy T1 ptrue)]

/-- Finding O1: `Size = Size` is not `False`. The self-hosted kernel counted `Size` and
`Size< s` as type formers, so equations between them (even `Size = Size`) fell through
to "different formers ⇒ False", and `absurd(Empty, reflTy Size) : Empty` checked. In the
Lean kernel these equations stay stuck: the three `absurd`s are rejected, and `reflTy`
has the type `Size = Size` (resp. `Size< ∞ = Size< ∞`). -/
def sizeEq : List MTm :=
  [exfalso (empty 0) (reflTy size), exfalso (empty 0) (reflTy (sizeLt szInf)),
   ann (lam (exfalso (empty 0) (var 0))) (pi (eqTy size (sizeLt szInf)) (empty 0)),
   reflTy size, reflTy (sizeLt szInf)]

/-- Decision D2: `∞` is not below itself (`↑∞ = ∞` makes `↑s ≤ ∞` true of every `s`).
The first five are rejected: `∞` (or `↑∞`) as a `Size< ∞`, a variable of type `Size` (it
may be `∞`), and the loop `sfix (fun s rec i x => rec ∞ i x) ∞ tt 0 : Empty` (its `rec`
takes sizes below the generic `s`, so it was already rejected). The rest are accepted:
a bounded variable and its successors are below `∞`. -/
def sizeInf : List MTm :=
  let sizeArg (A s : MTm) := app (ann (lam star) (piq .zero A (unit 0))) s
  [ann szInf (sizeLt szInf), ann (szSuc szInf) (sizeLt szInf), sizeArg (sizeLt szInf) szInf,
   ann (lam (var 0)) (pi size (sizeLt szInf)),
   sfix 0 (unit 0) natD 1 (lams 2 (empty 0)) (lams 4 (app (app (app (var 2) szInf) (var 1)) (var 0))) szInf star natZero,
   ann (lam (var 0)) (pi (sizeLt szInf) (sizeLt szInf)),
   ann (lam (szSuc (szSuc (var 0)))) (pi (sizeLt szInf) (sizeLt szInf)),
   ann (lam (lam (var 0))) (pi size (pi (sizeLt (var 0)) (sizeLt szInf))),
   ann (lam (lam (szSuc (var 0)))) (pi size (pi (sizeLt (var 0)) (sizeLt (szSuc (var 1))))),
   ann (lam (lam (sizeArg (sizeLt szInf) (var 0)))) (pi size (pi (sizeLt (var 0)) (unit 0)))]

/-- K3: the size of `μ^s`/`ν^s` must be a size. The first two (`tt`, `Enum 2` as sizes) are
rejected, the rest accepted. -/
def sizeArgs : List MTm :=
  [mus 0 (unit 0) natD star star, streamAt (enum 2),
   natAt szInf, ann (lam (natAt (var 0))) (pi size (univ 0)), ann (lam (streamAt (szSuc (var 0)))) (pi size (univ 0))]

/-- Q4 (fixed): a description field must live exactly in `Sort (l+1)`, the universe
`Desc.elim`'s `marg` takes it from. It used to be enough for it to fit (`Sort k`,
`k ≤ l+1`), and universes aren't cumulative, so `Desc.elim` could reduce to a term of the
wrong type: `getS D : Type` was accepted and reduced to `True`, while `True : Type` is
rejected. Now that `D` is rejected (the first four are errors, and so is the last), and the field is lifted
instead: `getS D' : Type` reduces to `ULift True`, which is in `Type`. The rest: the rules
of `ULift` (a boxed proof, `down`, equality and casts, η, the level check). -/
def smallField : List MTm :=
  let getS (D : MTm) := delim 2 (lam (univ 0)) (lam (unit 0)) (lams 4 (var 2)) (lams 4 (unit 0)) (lams 5 (unit 0)) D
  let D := ann (darg ptrue (lam (dret star))) (desc 0 (unit 0))
  let L (A : MTm) := ulift 1 A
  let D' := ann (darg (L ptrue) (lam (dret star))) (desc 0 (unit 0))
  let boxed := ann (up star) (L ptrue)
  let liftedTag (i : Nat) := ann (up (tag 2 i)) (L (enum 2))
  [-- rejected: the small field, `getS` on it, `True : Type`, and `ULift.{1} Type`
   D, ann (getS D) (univ 0), ann ptrue (univ 0), L (univ 0),
   -- accepted: the lifted field; `getS D'` is `ULift True` (by `reflTy`), a type
   D', ann (getS D') (univ 0), ann (reflTy (getS D')) (eqTy (getS D') (L ptrue)),
   ann (con (pair (up star) (pair star star))) (mu 0 (unit 0) D' star),
   -- a boxed proof, its contents, and equality of boxed proofs (`True`)
   boxed, down boxed, ann star (eq (L ptrue) boxed boxed),
   ann (lam (lam star)) (pi (L ptrue) (pi (L ptrue) (eq (L ptrue) (var 1) (var 0)))),
   -- η: a variable of type `ULift A` is `up (down x)`
   ann (lam (refl (L (enum 2)) (var 0))) (pi (L (enum 2)) (eq (L (enum 2)) (var 0) (up (down (var 0))))),
   ann (lam (up (var 0))) (pi (enum 2) (ulift 2 (enum 2))),
   -- type equality: `ULift A = ULift B` is `A = B`; `ULift A = A` is `False`
   reflTy (L ptrue), reflTy (L (enum 2)),
   ann (lam (exfalso (empty 0) (var 0))) (pi (eqTy (L (enum 2)) (enum 2)) (empty 0)),
   -- casts go through `down`
   ann star (eq (L (enum 2)) (cast (L (enum 2)) (L (enum 2)) star (liftedTag 1)) (liftedTag 1)),
   -- rejected: boxed different tags are different
   ann star (eq (L (enum 2)) (liftedTag 0) (liftedTag 1))]

/-- F6: two types whose binder quantities are different literals are unequal (`False`, so
the `absurd` checks), and equal literals give the Σ rule. (`MTm` has no quantity variables,
the case F6 was about: its Lean test is in the group *quantity polymorphism*.) -/
def qtyApart : List MTm :=
  let F (q : ZeroOneMany) := sorted 1 (piq q (enum 2) (enum 2))
  [ann (lam (exfalso (empty 0) (var 0))) (pi (eqTy (F .zero) (F .one)) (empty 0)),
   ann (lam (exfalso (empty 0) (var 0))) (pi (eqTy (sorted 1 (sigmaq .one (enum 2) (enum 2))) (sorted 1 (sigma (enum 2) (enum 2)))) (empty 0)),
   ann (lam (exfalso (empty 0) (var 0))) (pi (eqTy (F .one) (F .one)) (empty 0)),
   reflTy (F .one)]

/-- Terms the differential test always checks (well-typed ones the generator rarely
builds whole), before the random ones. -/
def samples : List MTm :=
  propShapes ++ qtyApart ++ sizeInf ++ sizeEq ++ sizeArgs ++ smallField ++ [natTy, natZero, natSucc natZero, natSucc (natSucc natZero), ann natD (desc 0 (unit 0)),
   eq natTy natZero (natSucc natZero), eq natTy (natSucc natZero) (natSucc natZero), refl natTy (natSucc natZero),
   delim 1 (lam (unit 0)) (lam star) (lams 4 star) (lams 4 star) (lams 5 star) (ann natD (desc 0 (unit 0))),
   ann (con (pair (tag 2 1) (pair star (pair star star)))) natTy,
   ann (con (pair (tag 2 0) star)) natTy,
   -- induction: a constant method, and one that returns the constructor's tag
   ind 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (tag 2 0)) star natZero,
   ind 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (fst (var 1))) star (natSucc natZero),
   -- it computes: `tt : ind … 1 = #1` checks, `tt : ind … 1 = #0` doesn't
   ann star (eq (enum 2) (ind 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (fst (var 1))) star (natSucc natZero)) (tag 2 1)),
   ann star (eq (enum 2) (ind 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (fst (var 1))) star (natSucc natZero)) (tag 2 0)),
   -- stuck on a variable
   ann (lam (ind 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (fst (var 1))) star (var 0))) (pi natTy (enum 2)),
   -- an ill-typed method
   ind 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (var 1)) star natZero,
   -- globals: kept folded in types, unfolded when needed
   const "idU", app (const "idU") (enum 2), ann star (eq (univ 0) (app (const "idU") (enum 2)) (enum 2)),
   const "one", ann (const "zero") (const "Nat"), app (app (const "twice") (const "idU")) (const "A"),
   eq (const "Nat") (const "zero") (const "one"), const "a", app (const "idU") (const "a"),
   ann (lam (var 0)) (pi (const "A") (const "A")),
   ann star (eq (enum 2) (ind 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (fst (var 1))) star (const "one")) (tag 2 1)),
   ann (eqRefl' (pi (univ 0) (univ 0)) (app (const "twice") (const "idU")))
     (eq (pi (univ 0) (univ 0)) (app (const "twice") (const "idU")) (lam (var 0))),
   -- universe polymorphism: instances at different levels
   const "idP" [1], const "idP" [0], const "idP" [2], app (app (const "idP" [1]) (enum 2)) (tag 2 1),
   app (app (const "idP" [1]) (univ 0)) (enum 2), app (app (const "idP" [2]) (univ 0)) (enum 2),
   app (app (app (app (const "constP" [1, 2]) (enum 2)) (univ 0)) (tag 2 0)) (enum 3),
   ann (const "idP" [1]) (pi (univ 0) (pi (var 0) (var 1))),
   ann (lam (app (app (const "idP" [1]) (enum 2)) (var 0))) (pi (enum 2) (enum 2)),
   eq (pi (enum 2) (enum 2)) (app (const "idP" [1]) (enum 2)) (lam (var 0)),
   -- quantities: linear and erased binders
   ann (lam (var 0)) (piq .one (univ 0) (univ 0)),
   ann (lam (pair (var 0) (var 0))) (piq .one (univ 0) (sigma (univ 0) (univ 0))),
   ann (lam (var 0)) (piq .zero (univ 0) (univ 0)),
   ann (lam (ann star (unit 0))) (piq .zero (univ 0) (unit 0)),
   ann (lam (lam (var 0))) (piq .zero (univ 0) (pi (var 0) (var 1))),
   app (ann (lam (lam (var 0))) (piq .zero (univ 0) (pi (var 0) (var 1)))) (enum 2),
   letq .one (univ 0) (enum 2) (var 0), letq .zero (univ 0) (enum 2) (var 0),
   letq .zero (univ 0) (enum 2) (ann (lam (var 0)) (pi (var 0) (var 1))),
   fst (ann (pair (univ 0) star) (sigmaq .zero (univ 1) (unit 0))),
   snd (ann (pair (univ 0) star) (sigmaq .zero (univ 1) (unit 0))),
   -- `p.2` drops `p.1`: not if that field is linear (Q1)
   ann (lam (snd (var 0))) (piq .one (sigmaq .one (univ 0) (univ 0)) (univ 0)),
   ann (lam (snd (var 0))) (piq .one (sigmaq .many (univ 0) (univ 0)) (univ 0)),
   snd (ann (pair (enum 2) (enum 2)) (sigmaq .one (univ 0) (univ 0))),
   ann (lam (lam (ecase (univ 0) (var 1) [var 0, var 0]))) (pi (enum 2) (piq .one (univ 0) (univ 0))),
   ann (lam (lam (ecase (univ 0) (var 1) [var 0, univ 0]))) (pi (enum 2) (piq .one (univ 0) (univ 0))),
   -- sizes and subtyping
   size, szInf, sizeLt szInf, szSuc szInf,
   ann (lam (ann (con (pair (tag 2 0) (pair star star))) (natAt (szSuc (var 0))))) (pi size (natAt (szSuc (var 0)))),
   ann (lam (lam (ann (con (pair (tag 2 1) (pair (var 0) (pair star star)))) (natAt (szSuc (var 1))))))
     (pi size (pi (natAt (var 0)) (natAt (szSuc (var 1))))),
   ann (lam (lam (var 0))) (pi size (pi (natAt (var 0)) natTy)),
   ann (lam (lam (var 0))) (pi size (pi natTy (natAt (var 0)))),
   ann (lam (lam (var 0))) (pi size (pi (sizeLt (var 0)) size)),
   ann (lam (lam (var 0))) (pi size (pi (sizeLt (var 0)) (sizeLt (szSuc (var 1))))),
   ann (lam (lam (var 0))) (pi size (pi (sizeLt (szSuc (var 0))) (sizeLt (var 1)))),
   ann (lam (ann (con (pair (tag 2 0) (pair star star))) (natAt (var 0)))) (pi size (natAt (var 0))),
   -- sized case analysis and recursion: they compute (the method / function gets ∞)
   scase 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (fst (var 0))) szInf star (natSucc natZero),
   ann star (eq (enum 2) (scase 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (fst (var 0))) szInf star (natSucc natZero)) (tag 2 1)),
   ann star (eq (enum 2) (scase 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (fst (var 0))) szInf star (natSucc natZero)) (tag 2 0)),
   sfix 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 4 (tag 2 0)) szInf star natZero,
   ann star (eq (enum 2) (sfix 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 4 (tag 2 1)) szInf star natZero) (tag 2 1)),
   ann (lam (lam (sfix 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 4 (tag 2 0)) (var 1) star (var 0))))
     (pi size (pi (natAt (var 0)) (enum 2))),
   -- an ill-typed method (the index is erased: it can't be returned)
   scase 0 (unit 0) natD 1 (lams 2 (unit 0)) (lams 3 (var 1)) szInf star natZero,
   -- coinduction: unfoldings compute when observed
   alt, zeros,
   ann star (eq (enum 2) (shead alt) (tag 2 0)),
   ann star (eq (enum 2) (shead (stail alt)) (tag 2 1)),
   ann star (eq (enum 2) (shead (stail alt)) (tag 2 0)),
   ann star (eq (enum 2) (shead (stail (stail zeros))) (tag 2 0)),
   ann (cocon (pair (tag 2 1) (pair alt (pair star star)))) streamTy,
   ann star (eq (enum 2) (shead (ann (cocon (pair (tag 2 1) (pair alt (pair star star)))) streamTy)) (tag 2 1)),
   coit 0 (unit 0) streamD (lam (enum 2)) (lams 2 (pair (var 0) star)) star (tag 2 0),
   -- only a value of size ↑s (or ∞) can be observed; ν is contravariant in its size
   ann (lam (lam (shead (var 0)))) (pi size (pi (streamAt (var 0)) (enum 2))),
   ann (lam (lam (shead (var 0)))) (pi size (pi (streamAt (szSuc (var 0))) (enum 2))),
   ann (lam (lam (var 0))) (pi size (pi streamTy (streamAt (var 1)))),
   ann (lam (lam (var 0))) (pi size (pi (streamAt (var 0)) streamTy)),
   -- stuck observations compare by their spines
   ann (lam (lam (var 0))) (pi streamTy (pi (eq (enum 2) (shead (var 0)) (tag 2 0)) (eq (enum 2) (shead (var 1)) (tag 2 0)))),
   ann (lam (lam (var 0))) (pi streamTy (pi (eq (enum 2) (shead (var 0)) (tag 2 0)) (eq (enum 2) (shead (stail (var 1))) (tag 2 0))))]

/-- Random terms over `n` variables (a linear congruential generator), biased towards
well-typed ones: annotated λs, applications of them, universes. -/
partial def gen (seed : Nat) (depth n : Nat) : MTm × Nat :=
  let next (s : Nat) := (s * 1103515245 + 12345) % 2147483648
  let s := next seed
  let pick := s / 65536 % 24
  if depth == 0 then
    if n > 0 && pick < 5 then (var (s / 7 % n), s) else (univ (s / 7 % 2), s)
  else match pick with
    | 0 | 1 => let (a, s) := gen s (depth - 1) n; let (b, s) := gen s (depth - 1) (n + 1); (pi a b, s)
    | 2 | 3 =>
      let (a, s) := gen s (depth - 1) n
      let (b, s) := gen s (depth - 1) (n + 1)
      let (body, s) := gen s (depth - 1) (n + 1)
      let ty := match s / 29 % 4 with
        | 0 => piq .zero a b
        | 1 => piq .one a b
        | _ => pi a b
      (ann (lam body) ty, s)
    | 4 | 5 => let (f, s) := gen s (depth - 1) n; let (a, s) := gen s (depth - 1) n; (app f a, s)
    | 6 =>
      let (t, s) := gen s (depth - 1) n
      let (v, s) := gen s (depth - 1) n
      let (b, s) := gen s (depth - 1) (n + 1)
      (letE t v b, s)
    | 7 => let (t, s) := gen s (depth - 1) n; let (ty, s) := gen s (depth - 1) n; (ann t ty, s)
    | 8 => let (a, s) := gen s (depth - 1) n; let (b, s) := gen s (depth - 1) (n + 1); (sigma a b, s)
    | 9 =>
      let (ta, s) := gen s (depth - 1) n
      let (tb, s) := gen s (depth - 1) (n + 1)
      let (a, s) := gen s (depth - 1) n
      let (b, s) := gen s (depth - 1) n
      (ann (pair a b) (sigma ta tb), s)
    | 10 =>
      let (p, s) := if s / 11 % 2 == 0 then gen s (depth - 1) n else (wellTypedPair s, (s * 7 + 3) % 2147483648)
      (if s / 3 % 2 == 0 then fst p else snd p, s)
    | 11 => (wellTypedPair s, s)
    | 12 => let k := s / 5 % 2; (if s / 3 % 2 == 0 then unit k else ann star (unit k), s)
    | 13 => let k := s / 5 % 3 + 1; (tag k (s / 7 % (k + 1)), s)
    | 14 =>
      -- a case on a tag (or a variable), returning tags of another enumeration
      let k := s / 5 % 2 + 1
      let k' := s / 11 % 2 + 1
      let (sc, s) := if n > 0 && s / 13 % 3 == 0 then (var (s / 17 % n), s) else (tag k (s / 7 % k), s)
      let bs := (List.range k).map fun j => tag k' ((s / (j + 19)) % k')
      (ecase (enum k') sc bs, s)
    | 15 => let (t, s) := gen s (depth - 1) n; (exfalso (univ 0) t, s)
    | 16 =>
      -- propositions: `Prop`, `True`, `False`, `(P : Prop) → P → P`, `A → True`
      match s / 5 % 6 with
      | 0 => (prop, s)
      | 1 => (ptrue, s)
      | 2 => (pfalse, s)
      | 3 => (pi prop (pi (var 0) (var 1)), s)
      | 4 => let (a, s) := gen s (depth - 1) n; (pi a ptrue, s)
      | _ => (ann star ptrue, s)
    | 17 =>
      -- a proof term: `λP p. p : (P : Prop) → P → P`, applied or not
      let idP := ann (lam (lam (var 0))) (pi prop (pi (var 0) (var 1)))
      (if s / 5 % 2 == 0 then idP else app (app idP ptrue) (ann star ptrue), s)
    | 18 =>
      -- equalities and their proofs, often well-typed
      let k := s / 5 % 2 + 1
      let i := s / 7 % k
      let j := s / 11 % k
      let fnTy := pi (univ 0) (univ 0)
      let idU := ann (lam (var 0)) fnTy
      match s / 13 % 8 with
      | 0 => (refl (enum k) (tag k i), s)
      | 1 => (ann star (eq (enum k) (tag k i) (tag k j)), s)
      | 2 => (eq (enum k) (tag k i) (tag k j), s)
      | 3 => (cast (univ 0) (univ 0) (reflTy (univ 0)) (enum k), s)
      | 4 => (eqTy (univ 0) (univ (s / 17 % 2)), s)
      | 5 => (cast fnTy fnTy (reflTy fnTy) idU, s)
      | 6 => (eq fnTy idU idU, s)
      | _ => (refl (univ 0) (enum k), s)
    | 19 =>
      let (a, s) := gen s (depth - 1) n
      let (b, s) := gen s (depth - 1) n
      let (A, s) := gen s (depth - 1) n
      (if s / 3 % 2 == 0 then eq A a b else cast A A (reflTy A) a, s)
    | 20 =>
      -- data: the natural numbers
      match s / 5 % 7 with
      | 0 => (natTy, s)
      | 1 => (natZero, s)
      | 2 => (natSucc natZero, s)
      | 3 => (ann natD (desc 0 (unit 0)), s)
      | 4 => (eq natTy natZero (natSucc natZero), s)
      | 5 => (refl natTy (natSucc natZero), s)
      | _ =>
        -- `Desc.elim` into `Unit`: every method gives `tt`
        (delim 1 (lam (unit 0)) (lam star) (lams 4 star) (lams 4 star) (lams 5 star) (ann natD (desc 0 (unit 0))), s)
    | 22 =>
      -- a global, applied or not
      let names := ["idU", "Nat", "zero", "one", "twice", "A", "a", "idP", "constP"]
      let nm := names[s / 5 % names.length]!
      let lv := (List.range (if nm == "idP" then 1 else if nm == "constP" then 2 else 0)).map fun j => s / (j + 23) % 3
      let c := const nm lv
      let (a, s) := gen s (depth - 1) n
      (if s / 3 % 2 == 0 then c else app c a, s)
    | 21 =>
      -- ill-typed or random data
      let (x, s) := gen s (depth - 1) n
      (if s / 3 % 2 == 0 then ann (con x) natTy else ann (dret x) (desc 0 (unit 0)), s)
    | _ => if n > 0 then (var (s / 7 % n), s) else (univ (s / 7 % 3), s)

/-- Declarations `(level params, value, type)` for the declaration test: they are
checked with their parameters symbolic. -/
def declSamples : List (List String × Option MTm × MTm) :=
  let u := MLvl.param "u"
  let v := MLvl.param "v"
  [(["u"], some (lam (lam (var 0))), pi (sortParam "u") (pi (var 0) (var 1))),
   (["u"], some (lam (var 0)), pi (sortParam "u") (sortParam "u")),
   (["u"], some (lam (sortParam "u")), pi (sortParam "u") (sortLv (.succ u))),
   (["u"], some (lam (var 0)), pi (sortParam "u") (sortLv (.succ u))),
   (["u"], some (lam (pi (var 0) (var 1))), pi (sortParam "u") (sortParam "u")),
   (["u", "v"], some (pi (sortParam "u") (sortParam "v")), sortLv (.max (.succ u) (.succ v))),
   (["u", "v"], some (pi (sortParam "u") (sortParam "v")), sortLv (.succ (.max u v))),
   (["u", "v"], some (pi (sortParam "u") (sortParam "v")), sortLv (.max u v)),
   (["u", "v"], some (pi (sortParam "u") (sortParam "v")), sortLv (.imax (.succ u) v)),
   -- a type in `Sort (imax u v)`: `Prop` when `v` is
   (["u", "v"], some (lam (lam (pi (var 1) (var 1)))), pi (sortParam "u") (pi (sortParam "v") (sortLv (.imax u v)))),
   (["u", "v"], some (lam (lam (pi (var 1) (var 1)))), pi (sortParam "u") (pi (sortParam "v") (sortLv (.max u v)))),
   (["u"], some (pi (sortParam "u") prop), sortLv (.succ u)),
   (["u"], none, pi (sortParam "u") (var 0)),
   -- polymorphic globals at symbolic levels
   (["u"], some (app (const "idP" [0]) (univ 0)), pi (univ 0) (univ 0)),
   -- equality needs a level that is never zero
   (["u"], some (lam (lam (eq (var 1) (var 0) (var 0)))), pi (sortLv (.succ u)) (pi (var 0) prop)),
   (["u"], some (lam (lam (eq (var 1) (var 0) (var 0)))), pi (sortParam "u") (pi (var 0) prop))]

/-- Random level puzzles: `Sort a : Sort b`, about half of them with `b` a rewriting of
`a + 1` (so they hold), and `Π`s of sorts. -/
def levelPuzzles (n : Nat) : List (List String × Option MTm × MTm) := Id.run do
  let mut out := []
  let mut s := 7
  for i in [0:n] do
    let (a, s1) := MLvl.gen s 2
    let (b, s2) := MLvl.gen s1 2
    if i % 2 == 0 then
      let (a', s3) := MLvl.rewrite s2 (.succ a)
      out := out ++ [(["u", "v"], some (sortLv a), sortLv a')]
      s := s3
    else if i % 4 == 1 then
      out := out ++ [(["u", "v"], some (sortLv a), sortLv (.succ b))]
      s := s2
    else
      let (c, s3) := MLvl.rewrite s2 (.imax (.succ a) (.succ b))
      let c := if i % 8 == 3 then c else (MLvl.gen s3 2).1
      out := out ++ [(["u", "v"], some (pi (sortLv a) (sortLv b)), sortLv c)]
      s := s3
  return out

/-- (D1) `abelCoquand` as one core term (lets instead of definitions), for the self-hosted
kernel. `selfApp`: `Omega := delta omega` (no normal form); otherwise `Omega := omega`, the
control. -/
def abelCoquand (selfApp : Bool) : MTm :=
  let top := sorted 0 (pi prop (sorted 0 (pi (var 0) (var 1))))
  -- Box P := μ (Desc.arg ((_ : Enum [u]) × P) (fun _ => Desc.ret ())) (); `boxD n` with P at index n
  let boxD (n : Nat) := darg (sorted 1 (sigma (enum 1) (var (n + 1)))) (lam (dret star))
  let p2 := sorted 1 (sigma (enum 2) (enum 2))
  letE prop top <|                                                 -- Top
  letE prop (sorted 0 (pi (var 0) (var 1))) <|                     -- T2 := Top → Top
  letE (var 0) (lam (var 0)) <|                                    -- id2 : T2
  letE (var 1) (lam (app (app (app (var 0) (var 2)) (var 1)) (var 0))) <|  -- delta z := z T2 id2 z
  letE (pi prop (univ 0)) (lam (mu 0 (unit 0) (boxD 0) star)) <|  -- Box
  letE (pi prop (pi (var 0) (app (var 2) (var 1))))                -- mk (P : Prop) (p : P) : Box P
    (lam (lam (con (pair (pair (tag 1 0) (var 0)) (pair star star))))) <|
  letE (pi prop (pi (app (var 2) (var 0)) (var 1)))                -- unbox (P : Prop) (b : Box P) : P
    (lam (lam (ind 0 (unit 0) (boxD 1) 0 (lams 2 (var 3)) (lams 3 (snd (fst (var 1)))) star (var 0)))) <|
  letE (pi prop (pi prop (pi (var 1) (pi (var 1) (eq prop (var 3) (var 2))))))  -- tautext
    (lams 4 (pair (lam (var 1)) (lam (var 2)))) <|
  -- omega A a := unbox A (cast (Box T2) (Box A) (transp … (reflTy (Box T2)) (tautext T2 A id2 a)) (mk T2 delta))
  letE (var 7) (lam (lam (app (app (var 3) (var 1))
    (cast (app (var 5) (var 8)) (app (var 5) (var 1))
      (transp prop (var 8) (lam (lam (eqTy (app (var 7) (var 10)) (app (var 7) (var 1)))))
        (reflTy (app (var 5) (var 8))) (var 1) (app (app (app (app (var 2) (var 8)) (var 1)) (var 7)) (var 0)))
      (app (app (var 4) (var 8)) (var 6)))))) <|
  letE (var 8) (if selfApp then app (var 5) (var 0) else var 0) <|  -- Omega
  ann (refl (enum 2) (tag 2 0))
    (eq (enum 2) (fst (cast p2 p2 (app (app (var 0) (eqTy p2 p2)) (reflTy p2)) (pair (tag 2 0) (tag 2 1)))) (tag 2 0))

end MTm

/-- The globals of the differential test, in the Lean kernel. (A function, so that it
is computed in the test, not when the module starts.) -/
def leanGlobals (_ : Unit := ()) : Globals ZeroOneMany :=
  MTm.globalDefs.foldl (fun g (n, ps, v, ty) => match addDecl g { name := n, levelParams := ps, type := ty.toTerm, value := v.map MTm.toTerm } with
    | .ok g' => g'
    | .error _ => g) {}

/-- What the Lean kernel says about a closed term: its type (printed like the Wiz
kernel prints) or `error`. -/
def leanVerdict (t : MTm) : String :=
  let g := leanGlobals ()
  match infer (R := ZeroOneMany) { globals := g } t.toTerm with
  | .ok (ty, _) => match MTm.ofTerm (quote g 0 ty) with
    | some m => m.pretty 0
    | none => "?"
  | .error _ => "error"

/-- What the Lean kernel says about a declaration: `ok` or `error`. -/
def leanDeclVerdict (d : List String × Option MTm × MTm) : String :=
  let (ps, v, ty) := d
  match addDecl (R := ZeroOneMany) (leanGlobals ()) { name := "test", levelParams := ps, type := ty.toTerm, value := v.map MTm.toTerm } with
  | .ok _ => "ok"
  | .error _ => "error"

/-- The whole self-hosted pipeline as a compiled program that checks the file `input.wiz`
in its working directory. It is built once and kept (under `/tmp`, keyed by its source
and this test binary), since every test that uses it would otherwise compile it again. -/
def selfhostChecker : IO (Except String System.FilePath) := do
  let src ← Selfhost.checkerFiles.mapM (fun (f : String) => IO.FS.readFile f)
  let prog := Selfhost.checkerSource src
  let stamp := toString (← (← IO.appPath).metadata).modified.sec
  let dir : System.FilePath := s!"/tmp/wiz-selfhost-{hash (prog ++ stamp)}"
  let exe := dir / "checker"
  if ← exe.pathExists then return .ok exe
  IO.FS.createDirAll dir
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let stdLib ← IO.FS.readFile "lib/Std.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Std" then some stdLib else none
  let s := runFrontend (R := ZeroOneMany) prog { loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render prog
  unless errs.isEmpty do return .error s!"unexpected errors:\n{"\n".intercalate errs.toList}"
  match Build.irProgram s "main" with
  | .error e => return .error e
  | .ok (decls, _) =>
    -- built under another name and renamed: tests may run at the same time
    let tmp := dir / s!"checker-{← IO.monoNanosNow}"
    match ← Build.compileC (← toolchain) (C.program decls true (Build.extraC s)) tmp with
    | .error e => return .error e
    | .ok () => IO.FS.rename tmp exe; return .ok exe

/-- The self-hosted compiler (stage 21): the frontend and `Backend.wiz`, printing the C
program for `input.wiz` (the frontend's own output as comments). -/
def selfhostCompiler : IO (Except String System.FilePath) := do
  let src ← Selfhost.compilerFiles.mapM (fun (f : String) => IO.FS.readFile f)
  let prog := Selfhost.compilerSource src
  let stamp := toString (← (← IO.appPath).metadata).modified.sec
  let dir : System.FilePath := s!"/tmp/wiz-selfhost-{hash (prog ++ stamp)}"
  let exe := dir / "compiler"
  if ← exe.pathExists then return .ok exe
  IO.FS.createDirAll dir
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let stdLib ← IO.FS.readFile "lib/Std.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Std" then some stdLib else none
  let s := runFrontend (R := ZeroOneMany) prog { loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render prog
  unless errs.isEmpty do return .error s!"unexpected errors:\n{"\n".intercalate errs.toList}"
  match Build.irProgram s "main" with
  | .error e => return .error e
  | .ok (decls, _) =>
    let tmp := dir / s!"compiler-{← IO.monoNanosNow}"
    match ← Build.compileC (← toolchain) (C.program decls true (Build.extraC s)) tmp with
    | .error e => return .error e
    | .ok () => IO.FS.rename tmp exe; return .ok exe

/-- A program for the self-hosted backend (recursion, lists, arrays, maps, strings, mutual
types), printing `6765 5050 1989 2 yes, ünïcode 2 5`. -/
def selfhostProgram1 : String :=
  "import Prelude\npartial def fib : Nat → Nat\n  | 0 => 0\n  | 1 => 1\n  | n + 2 => fib n + fib (n + 1)\npartial def countdown (n : Nat) (acc : List Nat) : List Nat := match n with\n  | 0 => acc\n  | .succ k => countdown k (List.cons n acc)\ndef sum : List Nat → Nat\n  | .nil => 0\n  | .cons x xs => x + sum xs\ndef fill (a : Array Nat) : Nat → Array Nat\n  | 0 => a\n  | .succ k => fill (Array.push a k) k\nmutual\ninductive Tree where\n  | leaf (n : Nat)\n  | node (ts : Forest)\ninductive Forest where\n  | nil\n  | cons (t : Tree) (ts : Forest)\nend\nmutual\ndef sizeT (t : Tree) : Nat := match t with\n  | .leaf _ => 1\n  | .node ts => sizeF ts\ndef sizeF (f : Forest) : Nat := match f with\n  | .nil => 0\n  | .cons t ts => sizeT t + sizeF ts\nend\ndef main : IO Unit := do\n  IO.println (Nat.toString (fib 20));\n  IO.println (Nat.toString (sum (countdown 100 .nil)));\n  let a := fill Array.empty 1000;\n  IO.println (Nat.toString (Array.size a + Array.getD a 10 0));\n  let m := StrMap.insert (StrMap.insert StrMap.empty (Str.ofString \"a\") 1) (Str.ofString \"b\") 2;\n  IO.println (Nat.toString (StrMap.findD m (Str.ofString \"b\") 0));\n  IO.println (if Nat.blt 3 4 then String.append \"yes, \" \"ünïcode\" else \"no\");\n  IO.println (Nat.toString (sizeT (Tree.node (Forest.cons (Tree.leaf 1) (Forest.cons (Tree.leaf 2) Forest.nil)))));\n  IO.println (Nat.toString (String.length \"hello\"))\n"

/-- A program for the reference counting mode: a list a million long (built, walked by
`ind`, freed without deep recursion), a hypothesis never read, a shared array updated
(copied), closures applied twice, a parameter never used, a key inserted twice. -/
def selfhostProgram2 : String :=
  "import Prelude\ndef len : List Nat → Nat\n  | .nil => 0\n  | .cons _ t => len t + 1\npartial def build (n : Nat) (acc : List Nat) : List Nat := match n with\n  | 0 => acc\n  | .succ k => build k (List.cons k acc)\ndef firstOr (d : Nat) : List Nat → Nat\n  | .nil => d\n  | .cons x _ => x\ndef twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)\ndef adder (n : Nat) : Nat → Nat := fun x => x + n\ndef pick (b : Bool) (x y : List Nat) : List Nat := if b then x else y\ndef ignore (x : List Nat) (y : Nat) : Nat := y\ndef main : IO Unit := do\n  let big := build 1000000 .nil;\n  IO.println (Nat.toString (len big));\n  IO.println (Nat.toString (firstOr 7 big));\n  let a := Array.push (Array.push Array.empty 1) 2;\n  let b := Array.set a 0 5;\n  IO.println (Nat.toString (Array.getD a 0 0 + Array.getD b 0 0));\n  let add3 := adder 3;\n  IO.println (Nat.toString (twice add3 1 + twice add3 2));\n  IO.println (Nat.toString (len (pick .false big (List.cons 1 .nil)) + ignore big 4));\n  let m := StrMap.insert (StrMap.insert StrMap.empty (Str.ofString \"k\") 1) (Str.ofString \"k\") 2;\n  IO.println (Nat.toString (StrMap.findD m (Str.ofString \"k\") 0 + StrMap.size m))\n"

/-- Compile a program with the self-hosted compiler, then the C it prints with the
self-hosted runtime (`selfhost/rt.c`, with the garbage collector given by the
toolchain's `gcCflags`/`gcLdflags`), run it, and compare its output. -/
def selfhostCompileRun (file expected : String) (flags : Array String := #[]) (progArgs : Array String := #[]) : IO Unit := do
  let tc ← toolchain
  if tc.gcCflags.isEmpty then IO.println "    (skipped: no garbage collector, --gc-cflags)"; return
  match ← selfhostCompiler with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "input.wiz") file
    let out ← IO.Process.output { cmd := "timeout", args := #["300", exe.toString] ++ flags, cwd := dir }
    unless out.exitCode == 0 do throw (IO.userError s!"the compiler failed ({out.exitCode}): {out.stderr}")
    IO.FS.writeFile (dir / "out.c") out.stdout
    let rt := (← IO.currentDir) / "selfhost"
    let args := #["-O1", "-w", s!"-I{rt}"] ++ tc.gcCflags.toArray ++ #["out.c", "-o", "prog"] ++ tc.gcLdflags.toArray
    let cc ← IO.Process.output { cmd := tc.cc, args, cwd := dir }
    unless cc.exitCode == 0 do throw (IO.userError s!"cc failed: {cc.stderr.take 2000}")
    let run ← IO.Process.output { cmd := "timeout", args := #["60", (dir / "prog").toString] ++ progArgs, cwd := dir }
    unless run.exitCode == 0 do throw (IO.userError s!"the program failed ({run.exitCode}): {run.stderr}")
    checkEq expected run.stdout

/-- Check a file of commands with the whole self-hosted pipeline (compiled), and compare
its output. -/
def selfhostCheckFile (file expected : String) : IO Unit := do
  match ← selfhostChecker with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "input.wiz") file
    let out ← IO.Process.output { cmd := "timeout", args := #["120", exe.toString], cwd := dir }
    unless out.exitCode == 0 do throw (IO.userError s!"the checker failed ({out.exitCode}): {out.stderr}")
    checkEq expected out.stdout

-- the self-hosted checker's output for a file
def selfhostOutput (file : String) : IO (Option String) := do
  match ← selfhostChecker with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then
      IO.println "    (skipped: no toolchain)"
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
  let s := runFrontend (R := ZeroOneMany) src { loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  match Build.irProgram s "main" with
  | .error e => throw (IO.userError e)
  | .ok (decls, _) =>
    let dir ← IO.FS.createTempDir
    let exe := dir / "wiz_main"
    match ← Build.compileC (← toolchain) (C.program decls true (Build.extraC s)) exe with
    | .error e =>
      if (e.splitOn "gmp.h").length > 1 then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)
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
    let s := runFrontend (R := ZeroOneMany) src { loader }
    let leanOk := (s.messages.filter (·.severity == .error)).isEmpty
    unless leanOk == ok do throw (IO.userError s!"the Lean frontend {if leanOk then "accepts" else "rejects"}:\n{d}")
    let some out ← selfhostOutput src | return
    let errs := (out.splitOn "\n").filter (·.startsWith "error")
    unless errs.isEmpty == ok do
      throw (IO.userError s!"the self-hosted frontend {if errs.isEmpty then "accepts" else "rejects"}:\n{d}\n{out}")

/-- (stage 21i) Phantom parameters, for both frontends. -/
def phantomHeader : String :=
  "inductive UIntN (w : Nat) where\n  | mk (toNat : Nat)\ninductive Proxy (A : Type) where\n  | mk\n" ++
  "structure S (w : Nat) where\n  x : Nat\ninductive N (w : Nat) where\n  | z\n  | s (n : N w)\n" ++
  "def width (w : Nat) (a : UIntN w) : Nat := w\ndef u8 : UIntN 8 := .mk 3\n"

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
          "  IO.println (normalize (.app (.app add two) two));\n  IO.println (typeOf (.app (.univ 0) (.univ 0)))\n"
        ioRun (kernel ++ "\n" ++ defs ++ main) ("(x0 : U0) → (x1 : x0) → x0\n(x0 : U0) → (x1 : x0) → x0\n" ++
          "error: type mismatch: expected U0, got U1\n(x0 : U0) → (x1 : (x1 : x0) → x0) → (x2 : x0) → x0\n" ++
          "λx0. λx1. λx2. (x1 (x1 (x1 (x1 x2))))\nerror: not a function: its type is U1\n") },
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
          "Nat : U0\nadd : (x0 : Nat) → (x1 : Nat) → Nat\nList : (x0 : U0) → U0\n(x0 : U0) → (x1 : x0) → (x2 : (List x0)) → (List x0)\none : Nat\nxs : (List Nat)\nlength : (x0 : U0) → (x1 : (List x0)) → Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nsum : (x0 : (List Nat)) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nappend : (x0 : U0) → (x1 : (List x0)) → (x2 : (List x0)) → (List x0)\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nPair : (x0 : U0) → (x1 : U0) → U0\nfst : (x0 : U0) → (x1 : U0) → (x2 : ((Pair x0) x1)) → x0\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\n" },
    { name := "definitions by equations, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive List (A : Type) where\n  | nil\n  | cons (head : A) (tail : List A)\ndef len (A : Type) : List A → Nat\n  | .nil => Nat.zero\n  | .cons h t => Nat.succ (len A t)\n#check len\n#reduce len Nat (List.cons Nat.zero List.nil)\ndef double : (n : Nat) → Nat\n  | .zero => Nat.zero\n  | .succ k => Nat.succ (Nat.succ (double k))\n#reduce double (Nat.succ Nat.zero)\n"
          "Nat : U0\nList : (x0 : U0) → U0\nlen : (x0 : U0) → (x1 : (List x0)) → Nat\n(x0 : U0) → (x1 : (List x0)) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\ndouble : (x0 : Nat) → Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\n" },
    { name := "several scrutinees and nested patterns, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive Bool where\n  | false\n  | true\ndef eq : Nat → Nat → Bool\n  | .zero, .zero => Bool.true\n  | .succ m, .succ n => eq m n\n  | _, _ => Bool.false\ndef one : Nat := Nat.succ Nat.zero\ndef two : Nat := Nat.succ one\n#reduce eq two two\n#reduce eq two one\ninductive List (A : Type) where\n  | nil\n  | cons (head : A) (tail : List A)\ndef zipAdd : List Nat → List Nat → List Nat\n  | .cons a as, .cons b bs => List.cons (Nat.succ a) (zipAdd as bs)\n  | _, _ => List.nil\n#reduce zipAdd (List.cons one (List.cons two List.nil)) (List.cons Nat.zero List.nil)\ndef second (A : Type) (d : A) : List A → A\n  | .cons _ (.cons b _) => b\n  | _ => d\n#reduce second Nat Nat.zero (List.cons one (List.cons two List.nil))\ndef sub : Nat → Nat → Nat\n  | m, .zero => m\n  | .zero, _ => Nat.zero\n  | .succ m, .succ n => sub m n\n#reduce sub two one\ndef g : Nat → Nat\n  | .succ k => g k\n  | x => Nat.succ x\n#reduce g two\n"
          "Nat : U0\nBool : U0\neq : (x0 : Nat) → (x1 : Nat) → Bool\none : Nat\ntwo : Nat\ncon((#1, (tt, tt)))\ncon((#0, (tt, tt)))\nList : (x0 : U0) → U0\nzipAdd : (x0 : (List Nat)) → (x1 : (List Nat)) → (List Nat)\ncon((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt)))))\nsecond : (x0 : U0) → (x1 : x0) → (x2 : (List x0)) → x0\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nsub : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\ng : (x0 : Nat) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\n" },
    { name := "implicit arguments, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef id {A : Type} (x : A) : A := x\n#check id\n#check id Nat.zero\n#reduce id (Nat.succ Nat.zero)\ndef const {A B : Type} (a : A) (b : B) : A := a\n#reduce const Nat.zero (Nat.succ Nat.zero)\ninductive List (A : Type) where\n  | nil\n  | cons (head : A) (tail : List A)\ndef one : List Nat := List.cons Nat.zero List.nil\n#check one\n#reduce one\ndef two : List Nat := List.cons (id Nat.zero) (List.cons (Nat.succ Nat.zero) List.nil)\n#reduce two\ndef twice {A : Type} (f : A → A) (x : A) : A := f (f x)\n#reduce twice Nat.succ Nat.zero\ndef bad : List Nat := List.nil\ndef bad2 : Nat := id List.nil\ndef map {A B : Type} (f : A → B) (l : List A) : List B := match l with\n  | .nil => List.nil\n  | .cons h t => List.cons (f h) (map f t)\n#reduce map Nat.succ (List.cons Nat.zero List.nil)\ndef length {A : Type} : List A → Nat\n  | .nil => Nat.zero\n  | .cons _ t => Nat.succ (length t)\n#reduce length one\n"
          "Nat : U0\nid : (x0 : U0) → (x1 : x0) → x0\n(x0 : U0) → (x1 : x0) → x0\nNat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nconst : (x0 : U0) → (x1 : U0) → (x2 : x0) → (x3 : x1) → x0\ncon((#0, (tt, tt)))\nList : (x0 : U0) → U0\none : (List Nat)\n(List Nat)\ncon((#1, (con((#0, (tt, tt))), (con((#0, (tt, tt))), (tt, tt)))))\ntwo : (List Nat)\ncon((#1, (con((#0, (tt, tt))), (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt))))), (tt, tt)))))\ntwice : (x0 : U0) → (x1 : (x1 : x0) → x0) → (x2 : x0) → x0\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nbad : (List Nat)\nerror: type mismatch: expected Nat, got (List ?m1)\nmap : (x0 : U0) → (x1 : U0) → (x2 : (x2 : x0) → x1) → (x3 : (List x0)) → (List x1)\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt)))))\nlength : (x0 : U0) → (x1 : (List x0)) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\n" },
    { name := "constructors by their names (.c) and @f, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive List (A : Type) where\n  | nil\n  | cons (head : A) (tail : List A)\ndef two : Nat := .succ (.succ .zero)\n#reduce two\ndef xs : List Nat := .cons .zero (.cons two .nil)\n#reduce xs\ndef id {A : Type} (x : A) : A := x\n#reduce @id Nat .zero\ndef add : Nat → Nat → Nat\n  | .zero, n => n\n  | .succ m, n => .succ (add m n)\n#reduce add two two\ndef map {A B : Type} (f : A → B) : List A → List B\n  | .nil => .nil\n  | .cons h t => .cons (f h) (map f t)\n#reduce map (add two) xs\ndef bad : Nat := .nil\n"
          "Nat : U0\nList : (x0 : U0) → U0\ntwo : Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nxs : (List Nat)\ncon((#1, (con((#0, (tt, tt))), (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt))))), (tt, tt)))))\nid : (x0 : U0) → (x1 : x0) → x0\ncon((#0, (tt, tt)))\nadd : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nmap : (x0 : U0) → (x1 : U0) → (x2 : (x2 : x0) → x1) → (x3 : (List x0)) → (List x1)\ncon((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (con((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt))))), (tt, tt)))))\nerror: unknown identifier Nat.nil\n" },
    { name := "partial definitions and mutual blocks, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive Bool where\n  | false\n  | true\npartial def loop (n : Nat) : Nat := loop (.succ n)\n#check loop\nmutual\ndef isEven : Nat → Bool\n  | .zero => .true\n  | .succ n => isOdd n\ndef isOdd : Nat → Bool\n  | .zero => .false\n  | .succ n => isEven n\nend\n#check isOdd\npartial def bad (n : Nat) : Nat := Type\n"
          "Nat : U0\nBool : U0\nloop : (x0 : Nat) → Nat\n(x0 : Nat) → Nat\nisEven : (x0 : Nat) → Bool\nisOdd : (x0 : Nat) → Bool\n(x0 : Nat) → Bool\nerror: type mismatch: expected Nat, got U1\n" },
    { name := "indexed families, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A Nat.zero\n  | cons (n : Nat) (a : A) (v : Vec A n) : Vec A (Nat.succ n)\n#check Vec.cons\ndef v2 : Vec Nat (.succ (.succ .zero)) := Vec.cons (.succ .zero) .zero (Vec.cons .zero (.succ .zero) Vec.nil)\n#reduce v2\ndef len {A : Type} {n : Nat} (v : Vec A n) : Nat := match v with\n  | .nil => Nat.zero\n  | .cons _ _ t => Nat.succ (len t)\n#reduce len v2\ndef head {A : Type} {n : Nat} (d : A) (v : Vec A n) : A := match v with\n  | .cons _ a _ => a\n  | _ => d\n#reduce head (.succ (.succ .zero)) v2\ndef bad : Vec Nat .zero := Vec.cons .zero .zero Vec.nil\n"
          "Nat : U0\nVec : (x0 : U0) → (x1 : Nat) → U0\n(x0 : U0) → (x1 : Nat) → (x2 : x0) → (x3 : ((Vec x0) x1)) → ((Vec x0) (Nat.succ x1))\nv2 : ((Vec Nat) (Nat.succ (Nat.succ Nat.zero)))\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (con((#1, (con((#0, (tt, tt))), (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (refl(Nat, Nat.zero), tt))), (refl(Nat, (Nat.succ con((#0, (tt, tt))))), tt)))))), (refl(Nat, (Nat.succ con((#1, (con((#0, (tt, tt))), (tt, tt)))))), tt))))))\nlen : (x0 : U0) → (x1 : Nat) → (x2 : ((Vec x0) x1)) → Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nhead : (x0 : U0) → (x1 : Nat) → (x2 : x0) → (x3 : ((Vec x0) x1)) → x0\ncon((#0, (tt, tt)))\nerror: type mismatch: expected ((Vec Nat) Nat.zero), got ((Vec ?m0) (Nat.succ Nat.zero))\n" },
    { name := "impossible cases ruled out by index equations, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A Nat.zero\n  | cons (n : Nat) (a : A) (v : Vec A n) : Vec A (Nat.succ n)\ndef head1 {A : Type} (v : Vec A (.succ .zero)) : A := match v with\n  | .cons _ a _ => a\n#reduce head1 (Vec.cons .zero (Nat.succ Nat.zero) Vec.nil)\ndef isNil {A : Type} (v : Vec A .zero) : Nat := match v with\n  | .nil => .zero\n#reduce isNil (@Vec.nil Nat)\ndef bad {A : Type} (v : Vec A (.succ .zero)) : A := match v with\n  | .nil => Type\n"
          "Nat : U0\nVec : (x0 : U0) → (x1 : Nat) → U0\nhead1 : (x0 : U0) → (x1 : ((Vec x0) (Nat.succ Nat.zero))) → x0\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nisNil : (x0 : U0) → (x1 : ((Vec x0) Nat.zero)) → Nat\ncon((#0, (tt, tt)))\nerror: type mismatch: expected A, got U1\n" },
    { name := "mutual inductive types, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\nmutual\ninductive Tm where\n  | var (n : Nat)\n  | app (f : Tm) (args : Tms)\ninductive Tms where\n  | nil\n  | cons (t : Tm) (rest : Tms)\nend\n#check Tm.app\ndef t1 : Tm := .app (.var .zero) (.cons (.var (.succ .zero)) .nil)\n#check t1\ndef head : Tm → Nat\n  | .var n => n\n  | .app f _ => head f\n#reduce head t1\ndef len : Tms → Nat\n  | .nil => .zero\n  | .cons _ r => .succ (len r)\n#reduce len (.cons (.var .zero) (.cons (.var .zero) .nil))\n"
          "Nat : U0\nTm : U0\nTms : U0\n(x0 : Tm) → (x1 : Tms) → Tm\nt1 : Tm\nTm\nhead : (x0 : Tm) → Nat\ncon((#0, (tt, tt)))\nlen : (x0 : Tms) → Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\n" },
    { name := "parameterised mutual inductive types, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\nmutual\ninductive Tree (A : Type) where\n  | leaf (a : A)\n  | node (kids : Forest A)\ninductive Forest (A : Type) where\n  | nil\n  | cons (t : Tree A) (rest : Forest A)\nend\n#check Tree.node\ndef t : Tree Nat := .node (.cons (.leaf .zero) (.cons (.leaf (.succ .zero)) .nil))\ndef size {A : Type} : Forest A → Nat\n  | .nil => .zero\n  | .cons _ r => .succ (size r)\ndef kids {A : Type} (d : Forest A) : Tree A → Forest A\n  | .node k => k\n  | _ => d\n#reduce size (kids .nil t)\n"
          "Nat : U0\nTree : (x0 : U0) → U0\nForest : (x0 : U0) → U0\n(x0 : U0) → (x1 : (Forest x0)) → (Tree x0)\nt : (Tree Nat)\nsize : (x0 : U0) → (x1 : (Forest x0)) → Nat\nkids : (x0 : U0) → (x1 : (Forest x0)) → (x2 : (Tree x0)) → (Forest x0)\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\n" },
    { name := "structures and projections, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\nstructure Pair (A B : Type) where\n  fst : A\n  snd : B\n#check Pair.mk\ndef p : Pair Nat (Pair Nat Nat) := .mk .zero (.mk (.succ .zero) .zero)\n#reduce Pair.fst (Pair.snd p)\ndef swap {A B : Type} (q : Pair A B) : Pair B A := .mk (Pair.snd q) (Pair.fst q)\n#reduce Pair.fst (swap p)\n#reduce p.snd.fst\ndef swap2 {A B : Type} (q : Pair A B) : Pair B A := .mk q.snd q.fst\n#reduce (swap2 p).fst\n"
          "Nat : U0\nPair : (x0 : U0) → (x1 : U0) → U0\nPair.fst : (x0 : U0) → (x1 : U0) → (x2 : ((Pair x0) x1)) → x0\nPair.snd : (x0 : U0) → (x1 : U0) → (x2 : ((Pair x0) x1)) → x1\n(x0 : U0) → (x1 : U0) → (x2 : x0) → (x3 : x1) → ((Pair x0) x1)\np : ((Pair Nat) ((Pair Nat) Nat))\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nswap : (x0 : U0) → (x1 : U0) → (x2 : ((Pair x0) x1)) → ((Pair x1) x0)\ncon((#0, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt)))))\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nswap2 : (x0 : U0) → (x1 : U0) → (x2 : ((Pair x0) x1)) → ((Pair x1) x0)\ncon((#0, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt)))))\n" },
    { name := "numerals and match as a term, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef add : Nat → Nat → Nat\n  | 0, n => n\n  | .succ m, n => .succ (add m n)\n#reduce add 2 3\ndef isSmall : Nat → Nat\n  | 0 => 1\n  | 1 => 1\n  | _ => 0\n#reduce isSmall 1\n#reduce isSmall 5\ninductive Bool where\n  | false\n  | true\ndef lt : Nat → Nat → Bool\n  | _, 0 => .false\n  | 0, .succ _ => .true\n  | .succ m, .succ n => lt m n\n#reduce lt 1 3\ndef pick (b : Bool) (x y : Nat) : Nat := add (match b with\n  | .true => x\n  | .false => y) 1\n#reduce pick .false 2 5\ndef both (a b : Bool) : Bool := match a, b with\n  | .true, .true => .true\n  | _, _ => .false\n#reduce both .true .false\n"
          "Nat : U0\nadd : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nisSmall : (x0 : Nat) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\ncon((#0, (tt, tt)))\nBool : U0\nlt : (x0 : Nat) → (x1 : Nat) → Bool\ncon((#1, (tt, tt)))\npick : (x0 : Bool) → (x1 : Nat) → (x2 : Nat) → Nat\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nboth : (x0 : Bool) → (x1 : Bool) → Bool\ncon((#0, (tt, tt)))\n" },
    { name := "the Prelude, if and strings, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\n#check Nat.add\ndef three : Nat := Nat.add 1 2\n#reduce Nat.beq three 3\ndef min (m n : Nat) : Nat := if Nat.blt m n then m else n\n#reduce min 2 1\ndef hi : String := \"hi\"\n#reduce String.length (String.append hi \"!\")\ndef firstCode (s : String) : Nat := match s.data with\n  | .cons c _ => c.code\n  | .nil => 0\n#reduce Nat.beq (firstCode \"A\") 65\n"
          "(x0 : Nat) → (x1 : Nat) → Nat\nthree : Nat\ncon((#1, (tt, tt)))\nmin : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nhi : String\ncon((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nfirstCode : (x0 : String) → Nat\ncon((#1, (tt, tt)))\n" },
    { name := "infix operators, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\n#reduce Nat.beq (2 + 3 * 2) 8\ndef pred2 : Nat → Nat\n  | n + 2 => n\n  | _ => 0\n#reduce Nat.beq (pred2 5) 3\n#reduce Nat.beq (10 - 3 - 2) 5\ninfixr:50 \" ⊕ \" => Bool.or\n#reduce .false ⊕ .false ⊕ .true\ndef len3 : Nat := List.length (List.cons 1 .nil ++ List.cons 2 (List.cons 3 .nil))\n#reduce Nat.beq len3 3\n#reduce Nat.le 3 3\n"
          "con((#1, (tt, tt)))\npred2 : (x0 : Nat) → Nat\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\nlen3 : Nat\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\n" },
    { name := "axioms, Unit, Array, IO and do, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\naxiom Secret : Type\nextern \"wiz_peek\" peek : Secret → Nat\ndef unit : Unit := ()\ndef twice (s : String) : IO Unit := do\n  IO.println s;\n  let t := String.append s \"!\";\n  IO.println t\ndef readLen (p : String) : IO Nat := do\n  s ← IO.readFile p;\n  IO.pure (String.length s)\ndef push2 (a : Array Nat) : Array Nat := Array.push (Array.push a 1) 2\ndef size2 : Nat := Array.size (push2 Array.empty)\ndef sum3 (n : Nat) : Nat :=\n  let m := n + n;\n  m + n\n#reduce Nat.beq (sum3 2) 6\n"
          "Secret : U0\npeek : (x0 : Secret) → Nat\nunit : Unit0\ntwice : (x0 : String) → (IO Unit0)\nreadLen : (x0 : String) → (IO Nat)\npush2 : (x0 : (Array Nat)) → (Array Nat)\nsize2 : Nat\nsum3 : (x0 : Nat) → Nat\ncon((#1, (tt, tt)))\n" },
    { name := "Syntax, StrMap and definitions as types, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\ndef leaf : Syntax := .node \"leaf\" (.cons (.atom \"x\") .nil)\ndef kindOf : Syntax → String\n  | .node k _ => k\n  | _ => \"\"\n#reduce String.length (kindOf leaf)\ndef argCount {b : Bool} : SyntaxF b → Nat\n  | .cons _ t => argCount t + 1\n  | .node _ args => argCount args\n  | _ => 0\n#reduce Nat.beq (argCount leaf) 1\ninductive Cat where\n  | mk (name : String) (n : Nat)\ndef find : List Cat → String → Option Cat\n  | .nil, _ => .none\n  | .cons (.mk m n) rest, name => match Nat.beq (String.length m) (String.length name) with\n    | .true => .some (.mk m n)\n    | .false => find rest name\ndef m : StrMap Nat := StrMap.insert StrMap.empty (Str.ofString \"k\") 1\n"
          "leaf : Syntax\nkindOf : (x0 : Syntax) → String\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nargCount : (x0 : Bool) → (x1 : (SyntaxF x0)) → Nat\ncon((#1, (tt, tt)))\nCat : U0\nfind : (x0 : (List Cat)) → (x1 : String) → (Option Cat)\nm : (StrMap Nat)\n" },
    { name := "function fields and catch-alls on mutual types, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\nmutual\ninductive Tm where\n  | lit (n : Nat)\n  | app (f : Tm) (a : Tm)\n  | many (ts : Tms)\ninductive Tms where\n  | nil\n  | cons (t : Tm) (ts : Tms)\nend\ndef litOr : Tm → Tm\n  | .lit n => .lit (n + 1)\n  | t => t\n#reduce litOr (.lit 1)\n#reduce litOr (.many .nil)\nmutual\ninductive Val where\n  | vnat (n : Nat)\n  | vlazy (v : Unit → Val)\n  | vbox (b : Box)\ninductive Box where\n  | mk (v : Val)\nend\npartial def force : Val → Val\n  | .vlazy v => force (v ())\n  | v => v\ndef unwrap : Val → Val\n  | .vlazy v => v ()\n  | v => v\n#reduce unwrap (Val.vlazy (fun _ => Val.vnat 3))\ndef big (n : Nat) : Nat := Nat.max n 3\n#reduce Nat.beq (big 1) 3\n"
          "Tm : U0\nTms : U0\nlitOr : (x0 : Tm) → Tm\ncon((#0, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (refl(Enum2, #0), tt))))\ncon((#2, (con((#3, (refl(Enum2, #1), tt))), (refl(Enum2, #0), tt))))\nVal : U0\nBox : U0\nforce : (x0 : Val) → Val\nunwrap : (x0 : Val) → Val\ncon((#0, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (refl(Enum2, #0), tt))))\nbig : (x0 : Nat) → Nat\ncon((#1, (tt, tt)))\n" },
    { name := "recursion through function fields, reordered parameters, big numerals, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\nmutual\ninductive Val where\n  | vnat (n : Nat)\n  | vsuc (v : Val)\n  | vlazy (v : Unit → Val)\n  | vbox (b : Box)\ninductive Box where\n  | mk (v : Val)\nend\ndef whnf : Val → Val\n  | .vlazy v => whnf (v ())\n  | v => v\ndef depth : Val → Nat\n  | .vsuc v => depth v + 1\n  | .vlazy v => depth (v ())\n  | _ => 0\n#reduce Nat.beq (depth (whnf (Val.vlazy (fun _ => Val.vlazy (fun _ => Val.vnat 3))))) 0\n#reduce Nat.beq (depth (Val.vsuc (Val.vlazy (fun _ => Val.vsuc (Val.vnat 0))))) 2\ndef apps : Nat → List Nat → Nat\n  | f, .nil => f\n  | f, .cons a rest => apps (f + a) rest\n#reduce Nat.beq (apps 1 (List.cons 2 (List.cons 3 .nil))) 6\ndef big : Nat := 100000\n#check big\n#reduce Nat.beq (Nat.sub 1000 999) 1\n"
          "Val : U0\nBox : U0\nwhnf : (x0 : Val) → Val\ndepth : (x0 : Val) → Nat\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\napps : (x0 : Nat) → (x1 : (List Nat)) → Nat\ncon((#1, (tt, tt)))\nbig : Nat\nNat\ncon((#1, (tt, tt)))\n" },
    { name := "postponed and inferred matches, pruning, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\ndef h1 : List Syntax → List String\n  | .nil => .nil\n  | .cons s rest => .cons (match s with\n      | .ident n => n\n      | _ => \"_\") .nil\ndef h2 (s : Syntax) : List String := .cons (match s with\n      | .ident n => n\n      | _ => \"_\") .nil\ndef h3 (s : List Nat) : List Nat := .cons (match s with\n      | .nil => 0\n      | _ => 1) .nil\ndef h4 (s : List Nat) : List Nat := List.cons (match s with\n      | .nil => 0\n      | _ => 1) .nil\ndef k1 (s : List Nat) : Nat :=\n  let x := match s with\n    | .nil => 0\n    | _ => 1;\n  x + 1\ndef k2 (b : Bool) : Nat :=\n  let y := if b then 2 else 3;\n  y\n#reduce Nat.beq (k1 .nil) 1\n#reduce Nat.beq (k2 .false) 3\ndef genTys (p base : Nat) : Nat → List Nat → List Nat\n  | _, .nil => .nil\n  | m, .cons t rest => .cons (t + m + p) (genTys p base (m + 1) rest)\n#reduce Nat.beq (List.length (genTys 1 2 0 (List.cons 1 (List.cons 2 .nil)))) 2\ndef kw (stx : Syntax) (p : Nat) : String :=\n  let kw := match stx with\n    | .atom v => v\n    | _ => \"infix\";\n  kw\ndef g2 (xs : List Nat) : Nat := match xs with\n    | .cons _ t => match List.append t t with\n      | .nil => 0\n      | later => List.length later\n    | .nil => 0\n#reduce Nat.beq (g2 (List.cons 1 (List.cons 2 .nil))) 2\ndef takeL {A : Type} : Nat → List A → List A\n  | .zero, _ => .nil\n  | .succ n, xs => match xs with\n    | .nil => .nil\n    | .cons x rest => .cons x (takeL n rest)\ndef sp (k : Nat) : List (List Nat) → List (List Nat)\n  | .nil => .nil\n  | .cons pats rest =>\n    let before := takeL k pats;\n    match List.length pats with\n    | .zero => .cons (List.append before .nil) (sp k rest)\n    | .succ _ => sp k rest\ndef sp2 (k : Nat) (pats : List Nat) : List (List Nat) :=\n    let before := takeL k pats;\n    .cons (List.append before .nil) .nil\ninductive Cl where\n  | mk (pats : List Nat) (binds : List Nat) (rhs : Nat)\ndef sp3 (k : Nat) : List Cl → List Cl\n  | .nil => .nil\n  | .cons (.mk pats binds rhs) rest =>\n    let before := takeL k pats;\n    let after := takeL k pats;\n    match List.length pats with\n    | .zero => .cons (.mk (List.append before (List.append pats after)) binds rhs) (sp3 k rest)\n    | .succ _ => sp3 k rest\ndef sp4 (T : String) (k : Nat) : List Cl → List Cl\n  | .nil => .nil\n  | .cons (.mk pats binds rhs) rest =>\n    let before := takeL k pats;\n    match List.length pats with\n    | .zero => .cons (.mk (List.append before pats) binds rhs) (sp4 T k rest)\n    | .succ _ =>\n      let binds' := match Nat.beq k 0 with\n        | .true => binds\n        | .false => List.append binds (.cons k .nil);\n      .cons (.mk before binds' rhs) (sp4 T k rest)\n"
          "h1 : (x0 : (List Syntax)) → (List String)\nh2 : (x0 : Syntax) → (List String)\nh3 : (x0 : (List Nat)) → (List Nat)\nh4 : (x0 : (List Nat)) → (List Nat)\nk1 : (x0 : (List Nat)) → Nat\nk2 : (x0 : Bool) → Nat\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ngenTys : (x0 : Nat) → (x1 : Nat) → (x2 : Nat) → (x3 : (List Nat)) → (List Nat)\ncon((#1, (tt, tt)))\nkw : (x0 : Syntax) → (x1 : Nat) → String\ng2 : (x0 : (List Nat)) → Nat\ncon((#1, (tt, tt)))\ntakeL : (x0 : U0) → (x1 : Nat) → (x2 : (List x0)) → (List x0)\nsp : (x0 : Nat) → (x1 : (List (List Nat))) → (List (List Nat))\nsp2 : (x0 : Nat) → (x1 : (List Nat)) → (List (List Nat))\nCl : U0\nsp3 : (x0 : Nat) → (x1 : (List Cl)) → (List Cl)\nsp4 : (x0 : String) → (x1 : Nat) → (x2 : (List Cl)) → (List Cl)\n" },
    { name := "the self-hosted frontend: a lambda waits for the arguments that fix its domains", run := fun _ =>
        selfhostCheckFile ("import Prelude\n" ++
          "def zip3 {A B C D : Type} (f : A → B → C → D) : List A → List B → List C → List D\n" ++
          "  | .cons a as, .cons b bs, .cons c cs => .cons (f a b c) (zip3 f as bs cs)\n  | _, _, _ => .nil\n" ++
          "def sel (c : List Bool) (t e : List Nat) : List Nat := zip3 (fun b x y => if b then x else y) c t e\n" ++
          "#reduce Nat.beq (List.length (sel (List.cons .true .nil) (List.cons 1 .nil) (List.cons 2 .nil))) 1\n")
          ("zip3 : (x0 : U0) → (x1 : U0) → (x2 : U0) → (x3 : U0) → (x4 : (x4 : x0) → (x5 : x1) → (x6 : x2) → x3) → (x5 : (List x0)) → (x6 : (List x1)) → (x7 : (List x2)) → (List x3)\n" ++
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
          ("UIntN : (x0 : Nat) → U0\nProxy : (x0 : U0) → U0\nS : (x0 : Nat) → U0\nS.x : (x0 : Nat) → (x1 : (S x0)) → Nat\nN : (x0 : Nat) → U0\n" ++
          "width : (x0 : Nat) → (x1 : (UIntN x0)) → Nat\nu8 : (UIntN (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))\n" ++
          "con((#1, (tt, tt)))\ncon((#1, (tt, tt)))\nN.toNat : (x0 : Nat) → (x1 : (N x0)) → Nat\ncon((#1, (tt, tt)))\n" ++
          "error: a parameter that no constructor mentions (a phantom parameter) of an indexed family is not supported by the self-hosted frontend\n") },
    { name := "the self-hosted backend: phantom parameters are erased (21i)", run := fun _ =>
        selfhostCompileRun ("import Prelude\ninductive Box (w : Nat) where\n  | mk (n : Nat)\nstructure Pt (w : Nat) where\n  x : Nat\n  y : Nat\n" ++
          "def get {w : Nat} : Box w → Nat\n  | .mk n => n\ndef sum {w : Nat} (p : Pt w) : Nat := p.x + p.y\n" ++
          "def b : Box 8 := .mk 3\ndef p : Pt 8 := .mk 1 2\n" ++
          "def main : IO Unit := IO.println (Nat.toString (get b + sum p))\n") "6\n" },
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
    { name := "D1 (Abel–Coquand): the Wiz kernel checks the program (and does not terminate with regularity on)", run := fun _ => do
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
        -- with regularity (`kernelRegularity`) the Wiz kernel loops
        let off := "def kernelRegularity : Bool := .false"
        unless (kernel.splitOn off).length == 2 do throw (IO.userError "kernelRegularity not found")
        let withReg := kernel.replace off "def kernelRegularity : Bool := .true"
        ioDiverges (withReg ++ "\n" ++ verdict ++ s!"def main : IO Unit := IO.println (verdict {loop.toWiz})\n") }
  ]

def languageGroup : Group where
  name := "language"
  exercise := "Stage 13"
  cases := [
    { name := "castRefl: a propositional regularity axiom in the Prelude; it doesn't compute (D1)", run := fun _ =>
        okLib ("import Prelude\ndef r (A : Type) (e : A = A) (a : A) : (cast e a : A) = a := castRefl e a\n" ++
          "#reduce fun (A : Type) (e : A = A) (a : A) => castRefl e a")
          ["fun A e a => castRefl A e a"] },
    { name := "an equation between numbers has one shape, numeral or constructor", run := fun _ =>
        okLib ("import Prelude\n#reduce ((0 : Nat) = 0)\n#reduce (Nat.zero = Nat.zero)\n#reduce ((0 : Nat) = Nat.zero)\n" ++
          "#reduce ((2 : Nat) = Nat.succ (Nat.succ Nat.zero))\n#reduce fun (m n : Nat) => (Nat.succ m = Nat.succ n)\n" ++
          "def t (e : (0 : Nat) = 0) : Nat.zero = Nat.zero := e\n")
          ["True", "True", "True", "True", "fun m n => m = n"] },
    { name := "a proof of True is not a pair", run := fun _ =>
        failsLib "import Prelude\ndef bad (x : True) : True := x.1\n" "cannot project" },
    { name := "recursion on a later argument, with parameters before the colon", run := fun _ =>
        okLib ("import Prelude\ndef addE (w : Nat) : List Nat → List Nat\n  | .nil => .cons w .nil\n" ++
          "  | .cons x xs => .cons x (addE w xs)\ndef app2 : Nat → List Nat → List Nat → List Nat\n" ++
          "  | k, .nil, ys => ys\n  | k, .cons x xs, ys => .cons (Nat.add x k) (app2 k xs ys)\n" ++
          "#eval addE 9 (.cons 1 .nil)\n#eval app2 10 (.cons 1 .nil) (.cons 7 .nil)")
          [".cons 1 (.cons 9 .nil)", ".cons 11 (.cons 7 .nil)"] },
    { name := "a parameter must be passed unchanged", run := fun _ =>
        failsLib "import Prelude\ndef bad (w : Nat) : List Nat → Nat\n  | .nil => w\n  | .cons x xs => bad x xs"
          "must pass the parameter w unchanged" },
    { name := "mutual (partial) definitions", run := fun _ =>
        okLib ("import Prelude\nmutual\ndef isEven : Nat → Bool\n  | .zero => .true\n  | .succ n => isOdd n\n" ++
          "def isOdd : Nat → Bool\n  | .zero => .false\n  | .succ n => isEven n\nend\n#eval isOdd 7\n" ++
          "partial def down (n : Nat) : Nat := match n with\n  | .zero => 0\n  | .succ m => down m\n#eval down 5")
          [".true", "0"] },
    { name := "a partial definition needs an inhabited type", run := fun _ =>
        failsLib "import Prelude\ninductive Void where\npartial def loop (n : Nat) : Void := loop n"
          "must be visibly inhabited" },
    { name := "match without an expected type", run := fun _ =>
        okLib ("import Prelude\ndef f (b : Bool) (n : Nat) : Nat :=\n  let k := match b with\n    | .true => n\n" ++
          "    | .false => 0;\n  Nat.add k 1\n#eval f .true 4") ["5"] },
    { name := "tuple patterns", run := fun _ =>
        okLib ("import Prelude\ndef sum3 : Nat × Nat × Nat → Nat\n  | (a, b, c) => Nat.add a (Nat.add b c)\n" ++
          "def firstZero : Nat × Nat → Bool\n  | (.zero, _) => .true\n  | p => .false\n" ++
          "#eval sum3 (1, 2, 3)\n#eval firstZero (0, 5)\n#eval firstZero (2, 5)") ["6", ".true", ".false"] },
    { name := "the pipe operator", run := fun _ =>
        okLib "import Prelude\n#eval 3 |> Nat.succ |> Nat.succ" ["5"] },
    { name := "recursion over a family at a concrete index", run := fun _ =>
        okLib ("import Prelude\ndef len : SyntaxF .false → Nat\n  | .nil => 0\n  | .cons _ xs => Nat.succ (len xs)\n" ++
          "#eval len (.cons .missing (.cons .missing .nil))") ["2"] },
    { name := "mutual inductive types", run := fun _ =>
        okLib ("import Prelude\nmutual\ninductive Tm where\n  | var (i : Nat)\n  | lam (body : Tm)\n  | app (f : Tm) (args : Tms)\n" ++
          "inductive Tms where\n  | nil\n  | cons (t : Tm) (ts : Tms)\nend\nmutual\ndef size : Tm → Nat\n  | .var _ => 1\n" ++
          "  | .lam b => Nat.succ (size b)\n  | .app f args => Nat.add (size f) (sizes args)\ndef sizes : Tms → Nat\n" ++
          "  | .nil => 0\n  | .cons t ts => Nat.add (size t) (sizes ts)\nend\n" ++
          "#eval size (.app (.lam (.var 0)) (.cons (.var 1) (.cons (.var 2) .nil)))") ["4"] },
    { name := "tactic keywords are not reserved", run := fun _ =>
        okLib "import Prelude\ndef f (first exact : Nat) : Nat := Nat.add first exact\n#eval f 1 2\ndef t : Nat := by exact 3" ["3"] },
    { name := "a catch-all of a recursive definition is the value at hand", run := fun _ =>
        okLib ("import Prelude\ndef g : Nat → Nat\n  | .succ k => g k\n  | x => Nat.succ x\n" ++
          "def t : g 3 = 1 := rfl\n#eval g 3") ["1"] },
    { name := "structural recursion through a function field of a mutual family", run := fun _ =>
        okLib ("import Prelude\nmutual\ninductive A where\n  | a0\n  | a1 (f : Unit → A)\n" ++
          "inductive B where\n  | b0\n  | b1 (x : A)\nend\n" ++
          "def depthA : A → Nat\n  | .a1 f => Nat.succ (depthA (f ()))\n  | .a0 => 0\n" ++
          "#eval depthA (.a1 (fun _ => .a1 (fun _ => .a0)))") ["2"] }
  ]

/-- Machine words (`lib/Word.wiz`): one table of operations at widths 8–100, signed and
unsigned, with its expected values. The kernel and the interpreters compute with the
definitions; compiled code calls the natives (`implemented_by`). -/
def wordTable : String := "import Word\ndef b2n : Bool → Nat\n  | .true => 1\n  | .false => 0\ndef m64 : Nat := 18446744073709551615\ndef main : List Nat :=\n  (.cons ((UIntN.add (U8.ofNat 200) (U8.ofNat 100)).toNat)\n    (.cons ((UIntN.sub (U8.ofNat 3) (U8.ofNat 5)).toNat)\n    (.cons ((UIntN.mul (U64.ofNat m64) (U64.ofNat m64)).toNat)\n    (.cons ((UIntN.add (U64.ofNat m64) (U64.ofNat 1)).toNat)\n    (.cons ((UIntN.mul (U64.ofNat m64) (U64.ofNat 3)).toNat)\n    (.cons ((UIntN.shiftLeft (U32.ofNat 5) 40).toNat)\n    (.cons ((UIntN.shiftLeft (U32.ofNat 5) 20).toNat)\n    (.cons ((UIntN.not (U64.ofNat 12345)).toNat)\n    (.cons ((UIntN.add (UIntN.ofNat 65 (Nat.pow 2 65 - 1)) (UIntN.ofNat 65 2)).toNat)\n    (.cons ((UIntN.mul (UIntN.ofNat 100 (Nat.pow 3 60)) (UIntN.ofNat 100 (Nat.pow 3 10))).toNat)\n    (.cons ((UIntN.div (U32.ofNat 1000) (U32.ofNat 7)).toNat)\n    (.cons ((UIntN.mod (U32.ofNat 1000) (U32.ofNat 7)).toNat)\n    (.cons ((UIntN.div (U32.ofNat 1000) (U32.ofNat 0)).toNat)\n    (.cons ((UIntN.mod (U32.ofNat 1000) (U32.ofNat 0)).toNat)\n    (.cons ((IntN.div (I8.ofNeg 7) (I8.ofNat 2)).toNat)\n    (.cons ((IntN.rem (I8.ofNeg 7) (I8.ofNat 2)).toNat)\n    (.cons ((IntN.div (I8.ofNeg 128) (I8.ofNeg 1)).toNat)\n    (.cons ((IntN.shiftRight (I8.ofNeg 100) 3).toNat)\n    (.cons ((IntN.resize 16 (I8.ofNeg 1)).toNat)\n    (.cons ((IntN.div (I64.ofNeg (Nat.pow 2 63)) (I64.ofNeg 1)).toNat)\n    (.cons ((IntN.div (I64.ofNeg 1000000000000) (I64.ofNat 7)).toNat)\n    (.cons ((IntN.rem (I64.ofNeg 1000000000000) (I64.ofNat 7)).toNat)\n    (.cons ((IntN.mul (I64.ofNeg 5) (I64.ofNat (Nat.pow 2 62))).toNat)\n    (.cons ((IntN.shiftRight (I64.ofNeg 123456789) 10).toNat)\n    (.cons (b2n (IntN.lt (I64.ofNeg 1) (I64.ofNat 0)))\n    (.cons (b2n (IntN.lt (I64.ofNat 0) (I64.ofNeg 1)))\n    (.cons (b2n (IntN.le (I8.ofNeg 128) (I8.ofNeg 128)))\n    (.cons (b2n (IntN.lt (I8.ofNat 127) (I8.ofNeg 128)))\n    (.cons (IntN.natAbs (IntN.min 64))\n    (.cons ((IntN.div (IntN.ofNeg 70 (Nat.pow 2 69)) (IntN.ofNeg 70 1)).toNat)\n    (.cons ((IntN.shiftRight (IntN.ofNeg 70 5) 100).toNat)\n    (.cons ((IntN.rem (IntN.ofNeg 70 7) (IntN.ofNeg 70 2)).toNat)\n    (.cons ((UIntN.neg (U8.ofNat 1)).toNat)\n    (.cons ((IntN.sub (I32.ofNat 0) (I32.ofNat 1)).toNat)\n    .nil))))))))))))))))))))))))))))))))))\n"
def wordTableValue : String := ".cons 44 (.cons 254 (.cons 1 (.cons 0 (.cons 18446744073709551613 (.cons 0 (.cons 5242880 (.cons 18446744073709539270 (.cons 1 (.cons 813220142716762761079858673625 (.cons 142 (.cons 6 (.cons 0 (.cons 1000 (.cons 253 (.cons 255 (.cons 128 (.cons 243 (.cons 65535 (.cons 9223372036854775808 (.cons 18446743930852408759 (.cons 18446744073709551615 (.cons 13835058055282163712 (.cons 18446744073709431052 (.cons 1 (.cons 0 (.cons 1 (.cons 0 (.cons 9223372036854775808 (.cons 590295810358705651712 (.cons 1180591620717411303423 (.cons 1180591620717411303423 (.cons 255 (.cons 4294967295 .nil)))))))))))))))))))))))))))))))))"

/-- 64-bit edge cases and the operations natively implemented in stage 22d (words as
their bits: scalars below 2^63, raw boxes below 2^64), plus a 64-bit FNV-1a, generic
width, and `match` on a word. -/
def wordTable64 : String := "import Word\ndef b2n : Bool → Nat\n  | .true => 1\n  | .false => 0\ndef m64 : Nat := 18446744073709551615\ndef p63 : Nat := 9223372036854775808\ndef fnv64 : List Nat → U64 → U64\n  | .nil, h => h\n  | .cons b bs, h => fnv64 bs (UIntN.mul (UIntN.xor h (U64.ofNat b)) (U64.ofNat 1099511628211))\ndef twice {ω w : Nat} (a : UIntN w) : UIntN w := UIntN.add a a\ndef bits : U64 → Nat\n  | .mk n => n\ndef bump (a : I64) : I64 := match a with\n  | .mk n => .mk (Nat.mod (Nat.add n 1) (Nat.pow 2 64))\ndef main : List Nat :=\n  (.cons ((U64.ofNat p63).toNat)\n    (.cons ((UIntN.add (U64.ofNat p63) (U64.ofNat p63)).toNat)\n    (.cons ((UIntN.sub (U64.ofNat 0) (U64.ofNat 1)).toNat)\n    (.cons (b2n (UIntN.beq (U64.ofNat p63) (UIntN.add (U64.ofNat 4611686018427387904) (U64.ofNat 4611686018427387904))))\n    (.cons (b2n (UIntN.lt (U64.ofNat (p63 - 1)) (U64.ofNat p63)))\n    (.cons (b2n (UIntN.le (U64.ofNat m64) (U64.ofNat 5)))\n    (.cons ((UIntN.land (U64.ofNat m64) (U64.ofNat (p63 + 5))).toNat)\n    (.cons ((UIntN.xor (U64.ofNat m64) (U64.ofNat 1)).toNat)\n    (.cons ((UIntN.lor (U64.ofNat p63) (U64.ofNat 1)).toNat)\n    (.cons ((UIntN.shiftRight (U64.ofNat m64) 63).toNat)\n    (.cons ((UIntN.shiftRight (U64.ofNat m64) 64).toNat)\n    (.cons ((UIntN.shiftLeft (U64.ofNat 1) 63).toNat)\n    (.cons ((UIntN.shiftLeft (U64.ofNat 1) 64).toNat)\n    (.cons ((UIntN.shiftLeft (U64.ofNat 1) 1000).toNat)\n    (.cons (b2n (UIntN.testBit (U64.ofNat p63) 63))\n    (.cons (b2n (UIntN.testBit (U64.ofNat m64) 64))\n    (.cons (b2n (UIntN.msb (U64.ofNat p63)))\n    (.cons ((UIntN.resize 8 (U64.ofNat m64)).toNat)\n    (.cons ((UIntN.resize 100 (U64.ofNat m64)).toNat)\n    (.cons ((IntN.resize 100 (I64.ofNeg 1)).toNat)\n    (.cons ((IntN.resize 64 (IntN.ofNeg 100 3)).toNat)\n    (.cons ((I64.ofNeg 1).toNat)\n    (.cons ((IntN.shiftRight (I64.ofNeg 1) 200).toNat)\n    (.cons ((IntN.shiftRight (I64.ofNeg p63) 63).toNat)\n    (.cons (b2n (IntN.lt (I64.ofNeg p63) (I64.ofNat (p63 - 1))))\n    (.cons ((IntN.rem (I64.ofNeg p63) (I64.ofNeg 1)).toNat)\n    (.cons ((IntN.mul (I64.ofNeg 1) (I64.ofNeg 1)).toNat)\n    (.cons (IntN.natAbs (UIntN.toIntN (U64.ofNat m64)))\n    (.cons (b2n (IntN.isNeg (I64.ofNat p63)))\n    (.cons ((U64.ofNat (Nat.add m64 8)).toNat)\n    (.cons ((I64.ofNeg (Nat.add m64 2)).toNat)\n    (.cons ((UIntN.mul (UIntN.ofNat 65 (Nat.add m64 1)) (UIntN.ofNat 65 2)).toNat)\n    (.cons ((UIntN.ofNat 65 (Nat.add m64 1)).toNat)\n    (.cons ((UIntN.div (U64.ofNat m64) (U64.ofNat p63)).toNat)\n    (.cons ((UIntN.mod (U64.ofNat m64) (U64.ofNat p63)).toNat)\n    (.cons ((UIntN.not (U64.ofNat 0)).toNat)\n    (.cons (b2n (IntN.beq (I64.ofNeg 1) (IntN.not (I64.ofNat 0))))\n    (.cons ((fnv64 (.cons 104 (.cons 105 .nil)) (U64.ofNat 14695981039346656037)).toNat)\n    (.cons ((twice (U64.ofNat p63)).toNat)\n    (.cons ((twice (UIntN.ofNat 70 p63)).toNat)\n    (.cons (bits (U64.ofNat m64))\n    (.cons ((bump (I64.ofNeg 1)).toNat)\n    (.cons ((IntN.toUIntN (I64.ofNeg 2)).toNat)\n    .nil)))))))))))))))))))))))))))))))))))))))))))\n"
def wordTable64Value : String := ".cons 9223372036854775808 (.cons 0 (.cons 18446744073709551615 (.cons 1 (.cons 1 (.cons 0 (.cons 9223372036854775813 (.cons 18446744073709551614 (.cons 9223372036854775809 (.cons 1 (.cons 0 (.cons 9223372036854775808 (.cons 0 (.cons 0 (.cons 1 (.cons 0 (.cons 1 (.cons 255 (.cons 18446744073709551615 (.cons 1267650600228229401496703205375 (.cons 18446744073709551613 (.cons 18446744073709551615 (.cons 18446744073709551615 (.cons 18446744073709551615 (.cons 1 (.cons 0 (.cons 1 (.cons 1 (.cons 1 (.cons 7 (.cons 18446744073709551615 (.cons 0 (.cons 18446744073709551616 (.cons 1 (.cons 9223372036854775807 (.cons 18446744073709551615 (.cons 1 (.cons 628919584683901914 (.cons 0 (.cons 18446744073709551616 (.cons 18446744073709551615 (.cons 0 (.cons 18446744073709551614 .nil))))))))))))))))))))))))))))))))))))))))))"

def wordGroup : Group where
  name := "word"
  exercise := "Stage 22c"
  cases := [
    { name := "the definitions compute in the kernel", run := fun _ =>
        okLib (wordTable ++ s!"def t : main = ({wordTableValue} : List Nat) := refl main") },
    { name := "#eval runs the definitions", run := fun _ =>
        okLib (wordTable ++ "#eval main") [wordTableValue] },
    { name := "#run runs the definitions", run := fun _ =>
        okLib (wordTable ++ "#run main") [wordTableValue] },
    { name := "compiled code runs the natives (C)", run := fun _ => cRun wordTable wordTableValue },
    { name := "compiled code runs the natives (LLVM)", run := fun _ => cRun (llvm := true) wordTable wordTableValue },
    { name := "compiled code calls the native", run := fun _ => do
        let loader ← preludeLoader
        let src := "import Word\ndef f (a b : U32) : U32 := UIntN.add a b\n#ir f"
        let s := runFrontend (R := ZeroOneMany) src { loader }
        let out := String.intercalate "\n" (s.messages.toList.map (·.text))
        check ((out.splitOn "wiz_word_add").length > 1) s!"no native call in:\n{out}" },
    { name := "the width is part of the type, and is inferred", run := fun _ => do
        okLib "import Word\ndef w {ω n : Nat} (a : UIntN n) : Nat := n\n#check w (U8.ofNat 3)\n#eval w (U8.ofNat 3)"
          ["w 8 (U8.ofNat 3) : Nat", "8"]
        let loader ← preludeLoader
        let s := runFrontend (R := ZeroOneMany) "import Word\ndef bad (x : U8) : U16 := x" { loader }
        check (s.messages.any (·.severity == .error)) "U8 was accepted as U16" },
    { name := "field notation through the fixed widths", run := fun _ =>
        okLib "import Word\ndef f (a b : I16) : Bool := a.lt b\n#eval f (I16.ofNeg 2) (I16.ofNat 1)" [".true"] },
    { name := "64-bit edges: the kernel", run := fun _ =>
        okLib (wordTable64 ++ s!"def t : main = ({wordTable64Value} : List Nat) := refl main") },
    { name := "64-bit edges: #eval", run := fun _ => okLib (wordTable64 ++ "#eval main") [wordTable64Value] },
    { name := "64-bit edges: #run", run := fun _ => okLib (wordTable64 ++ "#run main") [wordTable64Value] },
    { name := "64-bit edges: C", run := fun _ => cRun wordTable64 wordTable64Value },
    { name := "64-bit edges: LLVM", run := fun _ => cRun (llvm := true) wordTable64 wordTable64Value },
    { name := "a word is not an object: no constructor in the IR", run := fun _ => do
        let loader ← preludeLoader
        let src := "import Word\ndef f (a b : U64) : U64 := UIntN.add (UIntN.xor a b) (U64.ofNat 3)\n" ++
          "def g : U64 → Nat\n  | .mk n => n\n#ir f\n#ir g"
        let s := runFrontend (R := ZeroOneMany) src { loader }
        let out := String.intercalate "\n" (s.messages.toList.map (·.text))
        check ((out.splitOn "ctor").length == 1 && (out.splitOn "proj").length == 1) s!"a word object in:\n{out}"
        check ((out.splitOn "wiz_word_to_bits").length > 1) s!"match doesn't read the bits natively:\n{out}" },
    { name := "a U64 result is read back from a raw box", run := fun _ =>
        cRun "import Word\ndef main : U64 := UIntN.mul (U64.ofNat 18446744073709551615) (U64.ofNat 3)"
          ".mk 18446744073709551613" }
  ]

def stdGroup : Group where
  name := "std"
  exercise := "Stage 12a"
  cases := [
    { name := "arrays, updated in place", run := fun _ =>
        ioRun ("import Std\ndef fill : Nat → Array Nat → Array Nat\n  | .zero, a => a\n  | .succ n, a => Array.push (fill n a) (n * n)\n" ++
          "def main : IO Unit := do\n  let a := fill 10 Array.empty;\n  IO.println (Nat.toString (Array.getD a 9 0));\n" ++
          "  IO.println (Nat.toString (Array.getD (Array.set a 9 5) 9 0));\n  IO.println (Nat.toString (Array.getD a 9 0))")
          "81\n5\n81\n" },
    { name := "native text", run := fun _ =>
        ioRun ("import Std\ndef main : IO Unit := do\n  let t := Str.append (Str.ofString \"hello, \") (Str.ofString \"world\");\n" ++
          "  IO.println (Str.toString (Str.slice t 7 12));\n  IO.println (Nat.toString (Str.size t))") "world\n12\n" },
    { name := "maps from text", run := fun _ =>
        ioRun ("import Std\ndef count : List String → StrMap Nat → StrMap Nat\n  | .nil, m => m\n" ++
          "  | .cons w ws, m => count ws (StrMap.insert m (Str.ofString w) (StrMap.findD m (Str.ofString w) 0 + 1))\n" ++
          "def main : IO Unit := do\n  let m := count (.cons \"a\" (.cons \"b\" (.cons \"a\" .nil))) StrMap.empty;\n" ++
          "  IO.println (Nat.toString (StrMap.findD m (Str.ofString \"a\") 0));\n  IO.println (Nat.toString (StrMap.size m))") "2\n2\n" }
  ]

def effectsGroup : Group where
  name := "effects"
  exercise := "Stage 10a"
  cases := [
    { name := "a program reads its command-line arguments (IO.args, 21k), C and LLVM", run := fun _ => do
        let src := "import IO\ndef printAll : List String → IO Unit\n  | .nil => IO.pure ()\n  | .cons s rest => do\n    IO.println s;\n    printAll rest\n" ++
          "def main : IO Unit := do\n  n ← IO.argCount;\n  IO.println (Nat.toString n);\n  args ← IO.args;\n  printAll args\n"
        ioRun src "0\n"
        ioRun src "2\n--rc\na b\n" (args := #["--rc", "a b"])
        ioRun src "1\nx\n" (args := #["x"]) (llvm := true) },
    { name := "state, exceptions and output, handled in turn", run := fun _ =>
        ioRun ("import Eff\ndef prog : Eff (Row.cons (State Nat) (Row.cons (Exn String) (Row.cons Console Row.nil))) Nat := do\n" ++
          "  n ← get;\n  println \"starting\";\n  put (n + 1);\n  m ← get;\n  Monad.pure (m * 10)\n" ++
          "def report : Except String (Nat × Nat) → String\n  | .ok p => Nat.toString p.1\n  | .error e => e\n" ++
          "def main : IO Unit := do\n  r ← runConsole (runExn (runState prog 4));\n  IO.println (report r)") "starting\n50\n" },
    { name := "an exception stops the computation", run := fun _ =>
        ioRun ("import Eff\ndef prog : Eff (Row.cons (Exn String) (Row.cons Console Row.nil)) Nat := do\n" ++
          "  println \"before\";\n  n ← throw \"boom\";\n  println \"after\";\n  Monad.pure n\n" ++
          "def report : Except String Nat → String\n  | .ok n => Nat.toString n\n  | .error e => e\n" ++
          "def main : IO Unit := do\n  r ← runConsole (runExn prog);\n  IO.println (report r)") "before\nboom\n" },
    { name := "fusion: one program, as a tree or directly", run := fun _ => do
        let prog := "import Eff\ndef tick {m : Type → Type} [i : Monad m] [st : MonadState Nat m] : Nat → m Unit\n" ++
          "  | .zero => Monad.pure ()\n  | .succ n => do\n    k ← MonadState.getS;\n    MonadState.putS (k + 2);\n    tick n\n" ++
          "def prog {m : Type → Type} [i : Monad m] [st : MonadState Nat m] [c : MonadConsole m] : m Nat := do\n" ++
          "  MonadConsole.printLn \"counting\";\n  tick 50;\n  MonadState.getS\n" ++
          "def report (p : Nat × Nat) : IO Unit := IO.println (Nat.toString p.1)\n"
        ioRun (prog ++ "def main : IO Unit := do\n  p ← runConsole (runState (prog : Eff (Row.cons (State Nat) (Row.cons Console Row.nil)) Nat) 0);\n  report p")
          "counting\n100\n"
        ioRun (prog ++ "def main : IO Unit := do\n  p ← (prog : StateT Nat IO Nat) 0;\n  report p") "counting\n100\n" },
    { name := "effects that commute: the proof is checked", run := fun _ =>
        ioRun ("import Eff\ndef ReaderM (E A : Type) : Type := E → A\ninstance {E : Type} : Monad (ReaderM E) where\n" ++
          "  pure := fun a => fun _ => a\n  bind := fun x f => fun env => f (x env) env\n" ++
          "instance {E : Type} : Handler (Reader E) (ReaderM E) where\n  handle := fun _ => fun env => env\n" ++
          "instance {E : Type} : Commute (Reader E) (Reader E) (ReaderM E) where\n  comm := fun o₁ o₂ B f => rfl\n" ++
          "def main : IO Unit := IO.println \"ok\"") "ok\n" },
    { name := "effects that don't commute: no proof", run := fun _ =>
        ioFails ("import Eff\ndef StateM (S A : Type) : Type := S → A × S\ninstance {S : Type} : Monad (StateM S) where\n" ++
          "  pure := fun a => fun s => (a, s)\n  bind := fun x f => fun s => let (a, s') := x s; f a s'\n" ++
          "instance {S : Type} : Handler (State S) (StateM S) where\n  handle := fun o => match o with\n" ++
          "    | .get => fun s => (s, s)\n    | .put s' => fun _ => ((), s')\n" ++
          "instance {S : Type} : Commute (State S) (State S) (StateM S) where\n  comm := fun o₁ o₂ B f => rfl") "kernel rejected" }
  ]

def toolingGroup : Group where
  name := "tooling"
  exercise := "Stage 11"
  cases := [
    { name := "queries: an edit re-elaborates only what follows it", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let init : CommandState ZeroOneMany := { loader := fun m => if m == "Prelude" then some prelude else none }
        let v1 := "import Prelude\ndef a : Nat := 1\ndef b : Nat := a + 1\ndef c : Nat := b + 1\n"
        let (s1, eng) := Query.elaborate {} v1 init
        checkEq 4 eng.elaborated
        let v2 := v1.replace "b + 1" "b + 2"
        let (s2, eng) := Query.elaborate eng v2 init
        checkEq 5 eng.elaborated
        check (s1.messages.isEmpty && s2.messages.isEmpty) "unexpected messages"
        -- the same text again: everything is reused
        let (_, eng) := Query.elaborate eng v2 init
        checkEq 5 eng.elaborated },
    { name := "queries: hover, definition, completion", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let init : CommandState ZeroOneMany := { loader := fun m => if m == "Prelude" then some prelude else none }
        let src := "import Prelude\ndef double (n : Nat) : Nat := n + n\ndef four : Nat := double 2\n"
        let (s, _) := Query.elaborate {} src init
        let off := (src.splitOn "double 2")[0]!.length
        checkEq "(some (double, Nat → Nat))" (toString (Query.hoverAt s off))
        match Query.definitionAt s off with
        | some (n, info, m) => checkEq "double 15 \"\"" s!"{n} {info.start} {repr m}"
        | none => throw (IO.userError "no definition")
        let pre := src ++ "def x : Nat := dou"
        let (s', _) := Query.elaborate {} pre init
        checkEq "#[double]" (toString (Query.completionsAt s' pre pre.length)) },
    { name := "the shared cache gives the same results", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let init : CommandState ZeroOneMany := { loader := fun m => if m == "Prelude" then some prelude else none }
        let src := "import Prelude\ninductive T where\n  | a\n  | b (t : T)\ndef size : T → Nat\n  | .a => 1\n  | .b t => size t + 1\n#eval size (.b (.b .a))\ndef bad : Nat := true\n"
        let plain := runFrontend src init
        let dir ← IO.FS.createTempDir
        let (cold, h1) ← Cache.elaborateCached dir src init 0
        let (warm, h2) ← Cache.elaborateCached dir src init 0
        checkEq 0 h1
        check (h2 > 0) "nothing came from the cache"
        let msgs (st : CommandState ZeroOneMany) := toString (st.messages.toList.map (·.render src))
        checkEq (msgs plain) (msgs cold)
        checkEq (msgs plain) (msgs warm)
        checkEq plain.globals.order.size warm.globals.order.size },
    { name := "another build of wiz misses the shared cache (its binary is in the key)", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let init : CommandState ZeroOneMany := { loader := fun m => if m == "Prelude" then some prelude else none }
        let src := "import Prelude\ndef two : Nat := 1 + 1\n#eval two\n"
        let dir ← IO.FS.createTempDir
        let (_, h1) ← Cache.elaborateCached dir src init 0 (binary := some 1)
        let (_, h2) ← Cache.elaborateCached dir src init 0 (binary := some 1)
        let (_, h3) ← Cache.elaborateCached dir src init 0 (binary := some 2)
        checkEq 0 h1
        check (h2 > 0) "the same binary got nothing from the cache"
        checkEq 0 h3
        -- by default, the key is this test driver's own hash, remembered by its stamp
        let me ← Cache.binaryId (some dir)
        checkEq me (← Cache.binaryId (some dir))
        checkEq me (hash (← IO.FS.readBinFile (← IO.appPath)))
        let (_, h4) ← Cache.elaborateCached dir src init 0
        let (_, h5) ← Cache.elaborateCached dir src init 0 (binary := some me)
        checkEq 0 h4
        check (h5 > 0) "the default is not this binary's hash" },
    { name := "terms survive the cache's format", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let st := runFrontend (R := ZeroOneMany) "import Prelude" { loader := fun _ => some prelude }
        for n in ["List.append", "Nat.rec", "SyntaxF.casesOn", "Tac.rec", "Monad.bind"] do
          let some d := st.globals.find? n | throw (IO.userError s!"no {n}")
          let text := (Cache.term d.type).render
          match (Cache.Sx.parse text).bind (Cache.dterm (R := ZeroOneMany)) with
          | some t => check (t == d.type) s!"{n}: the type changed in the round trip"
          | none => throw (IO.userError s!"{n}: could not read back {text.take 200}") },
    { name := "the language server answers requests", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let srv : LSP.Server := { libs := ({} : Std.HashMap String (String × String)).insert "Prelude" ("lib/Prelude.wiz", prelude) }
        let req (s : String) : Lean.Json := (Lean.Json.parse s).toOption.get!
        let (srv, out) := LSP.handle srv (req "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{}}")
        check ((out[0]!.compress.splitOn "hoverProvider").length > 1) "no capabilities"
        let (srv, out) := LSP.handle srv (req ("{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":" ++
          "{\"uri\":\"file:///t.wiz\",\"text\":\"import Prelude\\ndef ok : Nat := 1\\ndef bad : Nat := true\\n\"}}}"))
        check ((out[0]!.compress.splitOn "unknown identifier").length > 1) s!"no diagnostic: {out[0]!.compress}"
        let (_, out) := LSP.handle srv (req ("{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/hover\",\"params\":" ++
          "{\"textDocument\":{\"uri\":\"file:///t.wiz\"},\"position\":{\"line\":1,\"character\":9}}}"))
        check ((out[0]!.compress.splitOn "Nat : Type").length > 1) s!"no hover: {out[0]!.compress}" }
  ]

/-- Programs for the native backends (C, or LLVM). -/
def nativeCases (llvm : Bool) : List Case :=
[
    { name := "memoised codata: no leaks, also when dropped part-way", run := fun _ =>
        cRun (llvm := llvm) memoStreamSrc "14946" },
    { name := "numbers, with GMP for big ones", run := fun _ =>
        cRun (llvm := llvm) "import Prelude\ndef fact : Nat → Nat\n  | .zero => 1\n  | .succ n => (.succ n) * fact n\ndef main : Nat := fact 25"
          "15511210043330985984000000" },
    { name := "strings", run := fun _ =>
        cRun (llvm := llvm) "import Prelude\ndef main : String := String.append \"hello, \" \"world\"" "\"hello, world\"" },
    { name := "closures", run := fun _ =>
        cRun (llvm := llvm) "import Prelude\ndef adder (n : Nat) : Nat → Nat := fun x => x + n\ndef twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)\ndef main : Nat := twice (adder 10) 1" "21" },
    { name := "codata", run := fun _ =>
        cRun (llvm := llvm) (streamPrelude ++ "def main : Nat := (nats .zero).tail.tail.head") ".succ (.succ .zero)" },
    { name := "codata by copatterns: register (cocon) and mealy (coit)", run := fun _ =>
        cRun (llvm := llvm) ("import Prelude\ncoinductive Stream (A : Type) where\n  head : A\n  tail : Stream A\n" ++
          "def nats (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => nats (n + 1)\n" ++
          "def register {A : Type} (init : A) (s : Stream A) : Stream A\n  | .head => init\n  | .tail => s\n" ++
          "def mealy {S I O : Type} (f : S → I → S × O) (st : S) (i : Stream I) : Stream O\n" ++
          "  | .head => (f st i.head).2\n  | .tail => mealy f (f st i.head).1 i.tail\n" ++
          "def take {A : Type} : Nat → Stream A → List A\n  | .zero, _ => .nil\n  | .succ n, s => .cons s.head (take n s.tail)\n" ++
          "def main : List Nat := take 6 (register 100 (mealy (fun acc x => (acc + x, acc + x)) 0 (Stream.mk 1 (nats 1))))")
          ".cons 100 (.cons 1 (.cons 2 (.cons 4 (.cons 7 (.cons 11 .nil)))))" },
    { name := "infinitary data", run := fun _ =>
        cRun (llvm := llvm) (treePrelude ++ "def main : Nat := Tree.depthAt (.node (fun i => .node (fun j => .leaf))) 3") "3" },
    { name := "deep recursion (direct recursion, big stack)", run := fun _ =>
        cRun (llvm := llvm) "import Prelude\ndef sumTo : Nat → Nat\n  | .zero => 0\n  | .succ n => (.succ n) + sumTo n\ndef main : Nat := sumTo 100000"
          "5000050000" },
    { name := "type classes and do", run := fun _ =>
        cRun (llvm := llvm) ("import Prelude\ninstance : Monad Option where\n  pure := fun a => Option.some a\n" ++
          "  bind := fun x f => match x with\n    | .none => Option.none\n    | .some a => f a\n" ++
          "def main : Option Nat := do\n  a ← Option.some 1;\n  b ← Option.some 2;\n  Monad.pure (a + b)") ".some 3" },
    { name := "division, powers and bits (small and GMP numbers)", run := fun _ =>
        cRun (llvm := llvm) ("import Prelude\ndef big : Nat := Nat.pow 3 50\n" ++
          "def main : List Nat := .cons (Nat.div big 1000007) (.cons (Nat.mod big 1000007) (.cons (Nat.div 100 7) " ++
          "(.cons (Nat.mod 100 0) (.cons (Nat.land big (Nat.pow 2 70 - 1)) (.cons (Nat.lor 12 10) (.cons (Nat.xor big big) " ++
          "(.cons (Nat.shiftLeft 3 70) (.cons (Nat.shiftRight big 40) (.cons (Nat.log2 big) (.cons (Nat.log2 0) " ++
          "(.cons (Nat.pow 0 0) (.cons (Nat.shiftLeft 1 61) (.cons (Nat.shiftLeft 1 62) .nil)))))))))))))")
          ".cons 717892962441115500 (.cons 961749 (.cons 14 (.cons 100 (.cons 98282295666516288457 (.cons 14 (.cons 0 (.cons 3541774862152233910272 (.cons 652924416219 (.cons 79 (.cons 0 (.cons 1 (.cons 2305843009213693952 (.cons 4611686018427387904 .nil)))))))))))))" },
    { name := "memoised suspensions (memo)", run := fun _ =>
        cRun (llvm := llvm) ("import Prelude\ndef twice (t : Unit → Nat) : Nat := t () + t ()\n" ++
          "def lazyAdd (m n : Nat) : Unit → Nat := memo (fun _ => m + n)\n" ++
          "def main : Nat := twice (lazyAdd 20 1) + twice (memo (fun _ => 0))") "42" }
  ]


def cGroup : Group where
  name := "c"
  exercise := "Exercise 8.2"
  cases := nativeCases false

/-- The same programs, through LLVM (the toolchain's `llc`). -/
def llvmGroup : Group where
  name := "llvm"
  exercise := "Stage 8d"
  cases := nativeCases true

def builtinGroup : Group where
  name := "builtins"
  exercise := "Stage 6b"
  cases := [
    { name := "import the prelude", run := fun _ =>
        okLib "import Prelude\n#check List.append" ["List.append : {A : Type} → List A → List A → List A"] },
    { name := "a stuck number times a big numeral, in a type (nat-pow-blowup)", run := fun _ =>
        okLib ("import Word\naxiom Q : Nat → Type\naxiom y : (n : Nat) → Q (Nat.mod n 18446744073709551616)\n" ++
          "def bump (a : I64) : I64 := match a with\n  | .mk n => .mk (Nat.mod (Nat.add n 1) (Nat.pow 2 64))") },
    { name := "Nat.beq and Nat.lt compute natively on numerals", run := fun _ =>
        okLib ("import Word\ndef t : Nat.beq 9223372036854775808 9223372036854775808 = Bool.true := rfl\n" ++
          "def u : Nat.lt 9223372036854775807 9223372036854775808 = Bool.true := rfl\n" ++
          "def v : Nat.lt 9223372036854775808 9223372036854775807 = Bool.false := rfl\n" ++
          "def w : UIntN.beq (U64.ofNat 9223372036854775808) (U64.ofNat 9223372036854775809) = .false := rfl\n" ++
          "#reduce Nat.beq 3 4\n#reduce Nat.lt 3 4") [".false", ".true"] },
    { name := "numerals and native arithmetic", run := fun _ =>
        okLib "import Prelude\n#eval 100 * 100 * 100 - 1" ["999999"] },
    { name := "recursion over native numbers", run := fun _ =>
        okLib "import Prelude\ndef fact : Nat → Nat\n  | .zero => 1\n  | .succ n => (.succ n) * fact n\n#eval fact 20"
          ["2432902008176640000"] },
    { name := "numerals reduce in the kernel", run := fun _ =>
        okLib "import Prelude\ndef t : 2 + 2 = 4 := refl 4" },
    { name := "native equality", run := fun _ =>
        okLib "import Prelude\n#eval Nat.beq 3 3" [".true"] },
    { name := "division, powers and bits compute natively (#eval)", run := fun _ =>
        okLib ("import Prelude\n#eval Nat.div 100 7\n#eval Nat.mod 100 7\n#eval 100 / 0\n#eval Nat.mod 5 0\n" ++
          "#eval Nat.pow 2 100\n#eval Nat.land 12 10\n#eval Nat.lor 12 10\n#eval Nat.xor 12 10\n" ++
          "#eval Nat.shiftLeft 3 70\n#eval Nat.shiftRight (Nat.pow 2 100) 98\n#eval Nat.log2 1025\n#eval Nat.log2 0\n#eval Nat.testBit 5 2")
          ["14", "2", "0", "5", "1267650600228229401496703205376", "8", "14", "6", "3541774862152233910272", "4", "10", "0", ".true"] },
    { name := "division, powers and bits in the IR interpreter (#run)", run := fun _ =>
        okLib ("import Prelude\n#run Nat.mod (Nat.pow 3 50) 1000007\n#run Nat.land (Nat.pow 2 70) (Nat.pow 2 70 + 5)\n" ++
          "#run Nat.log2 (Nat.pow 2 70)\n#run Nat.shiftRight 1000 3\n#run Nat.xor 5 3")
          ["961749", "1180591620717411303424", "70", "125", "6"] },
    { name := "division, powers and bits compute natively in the kernel", run := fun _ =>
        okLib ("import Prelude\ndef t1 : Nat.mod 300 256 = 44 := refl 44\n" ++
          "def t2 : Nat.xor (Nat.pow 2 64) 1 = 18446744073709551617 := refl 18446744073709551617\n" ++
          "def t3 : Nat.shiftRight (Nat.shiftLeft 5 200) 199 = 10 := refl 10\n" ++
          "def t4 : Nat.log2 (Nat.pow 2 300) = 300 := refl 300\n" ++
          "def t5 : Nat.land (Nat.pow 2 70) (Nat.pow 2 70 + 5) = Nat.pow 2 70 := refl (Nat.pow 2 70)") },
    { name := "the definitions behind the natives compute too (unfolded)", run := fun _ =>
        -- the fuel-driven helpers, applied directly, are not registered: the kernel unfolds them
        okLib ("import Prelude\ndef t1 : Nat.divGo 17 17 5 = 3 := refl 3\n" ++
          "def t2 : Nat.bitwise Bool.xor 30 12 10 = 6 := refl 6\ndef t3 : Nat.bitwise Bool.and 30 12 10 = 8 := refl 8\n" ++
          "def t4 : Nat.log2Go 9 9 = 3 := refl 3\ndef t5 : Nat.powFrom 10 2 = 1024 := refl 1024") },
    { name := "implemented_by: compiled code runs the implementation, the kernel the model", run := fun _ => do
        -- the implementation is trusted: here it deliberately differs, to show which runs
        let src := "import Prelude\ndef model (n : Nat) : Nat := n\ndef impl (n : Nat) : Nat := n + 1\n" ++
          "attribute [implemented_by impl] model\ndef t : model 5 = 5 := refl 5\n"
        okLib (src ++ "#eval model 5\n#run model 5") ["6", "6"]
        cRun (src ++ "def main : Nat := model 5") "6" },
    { name := "implemented_by: a fast implementation of a recursive definition", run := fun _ =>
        okLib ("import Prelude\ndef sumTo : Nat → Nat\n  | .zero => 0\n  | .succ n => .succ n + sumTo n\n" ++
          "def sumToFast (n : Nat) : Nat := n * (n + 1) / 2\nattribute [implemented_by sumToFast] sumTo\n" ++
          "def t : sumTo 4 = 10 := refl 10\n#erase sumTo\n#eval sumTo 1000000") ["sumTo := sumToFast", "500000500000"] },
    { name := "implemented_by: the types must agree", run := fun _ =>
        failsLib "import Prelude\ndef f (n : Nat) : Nat := n\ndef g (b : Bool) : Nat := 0\nattribute [implemented_by g] f"
          "g can't implement f: its type Bool → Nat is not f's type Nat → Nat" },
    { name := "implemented_by: not on a builtin", run := fun _ =>
        failsLib "import Prelude\ndef g (m n : Nat) : Nat := m\nattribute [implemented_by g] Nat.add" "already has an implementation" },
    { name := "the natives agree with the definitions (n / 0 = 0)", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ndef t : Nat.div 7 0 = 7 := refl 7" { loader := fun _ => some prelude }
        check (s.messages.any (·.severity == .error)) "expected an error" },
    { name := "kernel arithmetic on literals is native", run := fun _ =>
        okLib "import Prelude\ndef t : 100000 * 100000 = 10000000000 := refl 10000000000" },
    { name := "literals unfold under eliminators", run := fun _ =>
        okLib ("import Prelude\ndef isZero : Nat → Bool\n  | .zero => .true\n  | .succ _ => .false\n" ++
          "def t : isZero 3 = Bool.false := refl Bool.false\ndef u : Nat.succ 4 = 5 := refl 5") },
    { name := "different literals are not equal", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ndef t : 2 + 2 = 5 := refl 4" { loader := fun _ => some prelude }
        check (s.messages.any (·.severity == .error)) "expected an error" },
    { name := "non-ASCII strings are cheap", run := fun _ =>
        okLib "import Prelude\n#eval \"λ✝\"" ["\"λ✝\""] },
    { name := "do notation (a macro)", run := fun _ =>
        okLib ("import Prelude\n#eval (do x ← TacticM.pure 2; y ← TacticM.pure 3; TacticM.pure (x + y) : TacticM Nat)\n" ++
          "  (fun n => Tac.setGoals (.cons n .nil) Tac.done)") [".setGoals (.cons 5 .nil) .done"] },
    { name := "quotations build Syntax (Exercise 6.2)", run := fun _ =>
        okLib "import Prelude\n#eval `(term| f .x)"
          [".node \"term.app\" (.cons (.node \"term.ident\" (.cons (.ident \"f✝\") .nil)) " ++
           "(.cons (.node \"null\" (.cons (.node \"term.dotIdent\" (.cons (.atom \".\") (.cons (.ident \"x\") .nil))) .nil)) .nil))"] },
    { name := "a procedural macro (Exercise 6.3)", run := fun _ =>
        okLib (procPrelude ++ "#eval twice! 21") ["42"] },
    { name := "procedural macros are hygienic", run := fun _ =>
        okLib (procPrelude ++ "def y : Nat := 5\n#eval twice! y") ["10"] },
    { name := "a procedural macro can fail", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let src := procPrelude ++ "syntax (name := boom) \"boom!\" : term\n" ++
          "def boomMacro : Macro := fun _ => MacroM.throw \"kaboom\"\nattribute [macro term.boom] boomMacro\n#eval (boom! : Nat)"
        let s := runFrontend (R := ZeroOneMany) src { loader := fun _ => some prelude }
        check (s.messages.any (·.text == "kaboom")) s!"expected kaboom, got {s.messages.map (·.text)}" },
    { name := "only a Macro can be a macro", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let s := runFrontend (R := ZeroOneMany) "import Prelude\nattribute [macro term.app] Nat.add" { loader := fun _ => some prelude }
        check (s.messages.any (·.severity == .error)) "expected an error" },
    { name := "infinitary inductive: recursor", run := fun _ =>
        okLib (treePrelude ++ "#check Tree.rec")
          ["Tree.rec : (0 motive : Tree → Sort ?u0) → motive .leaf → ((k : Nat → Tree) → ((x : Nat) → motive (k x)) → " ++
           "motive (.node k)) → (x : Tree) → motive x"] },
    { name := "infinitary inductive: structural recursion through k n", run := fun _ =>
        okLib (treePrelude ++ "#eval Tree.depthAt (.node (fun i => .node (fun j => .leaf))) 3") ["3"] },
    { name := "infinitary inductive: indexed, dependent branching", run := fun _ =>
        okLib ("import Prelude\ninductive W (A : Type) : Nat → Type where\n  | sup (n : Nat) (k : (i : Nat) → W A i) : W A (.succ n)\n" ++
          "#check W.sup") ["W.sup : {A : Type} → (n : Nat) → ((i : Nat) → W A i) → W A (.succ n)"] },
    { name := "infinitary inductive: the domain may not mention the type", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ninductive Bad where\n  | mk (k : Bad → Bad)" { loader := fun _ => some prelude }
        check (s.messages.any (·.severity == .error)) "expected an error" },
    { name := "a match does not shadow the user's variables", run := fun _ =>
        okLib "import Prelude\ndef e (x : Bool) (n : Nat) : Bool := match n with\n  | .zero => x\n  | .succ _ => x" },
    { name := "nested match alternatives line up (colGe)", run := fun _ =>
        okLib ("import Prelude\ndef nth : List Bool → Nat → Bool\n  | .cons x t, n => match n with\n" ++
          "    | .zero => x\n    | .succ m => nth t m\n  | _, _ => .false\n#eval nth (.cons .false (.cons .true .nil)) 1") [".true"] },
    { name := "string literals", run := fun _ =>
        okLib "import Prelude\n#eval String.append \"ab\" \"cd\"" ["\"abcd\""] },
    { name := "a numeral is not a string", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ndef s : String := 3" { loader := fun _ => some prelude }
        check (s.messages.any (·.severity == .error)) "expected an error" }
  ]


/-- `okLib` with `lib/Optic.wiz` importable too. -/
def okOptic (input : String) (infos : List String := []) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let optic ← IO.FS.readFile "lib/Optic.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "Optic" then some optic else none
  let s := runFrontend (R := ZeroOneMany) input { loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr (s.messages.toList.map (·.text))).pretty

def failsOptic (input : String) (fragment : String) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let optic ← IO.FS.readFile "lib/Optic.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "Optic" then some optic else none
  let s := runFrontend (R := ZeroOneMany) input { loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

def opticGroup : Group where
  name := "optic"
  exercise := "lib/Optic.wiz (Rust DSL, RD11)"
  cases := [
    { name := "the optics library checks, with its lens laws", run := fun _ =>
        okOptic "import Optic\n#check List.atL_lawful\n#check Lens.comp_lawful"
          ["List.atL_lawful : {A : Type} → (i : Nat) → PLens.Lawful (List A) A (List.atL A i)",
           "Lens.comp_lawful : {S : Type} → {A : Type} → {B : Type} → (l : Lens S A) → (m : Lens A B) → Lens.Lawful S A l → Lens.Lawful A B m → Lens.Lawful S B (Lens.comp S A B l m)"] },
    { name := "lenses get, put and compose", run := fun _ =>
        okOptic ("import Optic\n#eval Lens.set Pair2.fstL (Pair2.mk 1 2) 5\n" ++
          "#eval Lens.over (Lens.comp Pair2.sndL Pair2.fstL) Nat.succ (Pair2.mk 1 (Pair2.mk 10 20))\n" ++
          "#eval Result.map (fun (st : Store Nat (List Nat)) => st.2 42) (List.atL 1 (List.cons 1 (List.cons 2 (List.cons 3 List.nil))))\n" ++
          "#eval Result.map Store.extract (List.atL 5 (List.cons 1 List.nil))")
          ["(5, 2, ())", "(1, (11, 20, ()), ())", ".ok (.cons 1 (.cons 42 (.cons 3 .nil)))", ".err .outOfBounds"] },
    { name := "zoom, affine borrows and traversals", run := fun _ =>
        okOptic ("import Optic\n#eval zoom Pair2.fstL (fun (n : Nat) => Result.ok (n, n + 1)) (Pair2.mk 7 8)\n" ++
          "#eval Affine.over Nat.succ (Affine.comp (Affine.some (Pair2.mk 1 2) (fun p => p)) (fun p => Affine.some p.fst (fun a => Pair2.mk a p.snd)))\n" ++
          "#eval TraverseMut.traverseM (fun (x : Nat) (acc : Nat) => Result.ok (x * 2, acc + x)) (List.cons 1 (List.cons 2 List.nil)) 0")
          [".ok (7, 8, 8, ())", "(2, 2, ())", ".ok (.cons 2 (.cons 4 .nil), 3)"] },
    { name := "an unlawful lens has no GetPut proof", run := fun _ =>
        failsOptic ("import Optic\ndef bad : Lens (List Nat) Nat := fun s => match s with\n" ++
          "  | .nil => (0, fun a => List.cons a List.nil)\n  | .cons x xs => (x, fun a => List.cons a (List.cons a xs))\n" ++
          "def badGP : Lens.GetPut bad := fun s => refl s") "type mismatch" }
  ]

/-! ## HD8: command macros, reflection, `deriving` -/

/-- Elaborate with `Prelude` and `Deriving` importable; no errors, and these infos. -/
def derivingRun (input : String) : IO (CommandState ZeroOneMany) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let derivingLib ← IO.FS.readFile "lib/Deriving.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "Deriving" then some derivingLib else none
  pure (runFrontend (R := ZeroOneMany) input { loader })

def okDeriving (input : String) (infos : List String := []) : IO Unit := do
  let s ← derivingRun input
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr (s.messages.toList.map (·.text))).pretty

def failsDeriving (input : String) (fragment : String) : IO Unit := do
  let s ← derivingRun input
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

/-- A command macro that defines `T.shape : List String`: the parameters, then each
constructor with its fields (`*` marks a recursive one) and indices. -/
def shapeMacro : String := "import Prelude
def strs : List String → Syntax
  | .nil => `(term| List.nil)
  | .cons s rest => let x := Syntax.mkStr s; let r := strs rest; `(term| List.cons $x $r)
def mark (f : FieldView) : String := match FieldView.recursive f with
  | .true => String.append \"*\" (FieldView.name f)
  | .false => FieldView.name f
def fieldStrs : List FieldView → List String
  | .nil => .nil
  | .cons f fs => .cons (mark f) (fieldStrs fs)
def idxStrs : List Syntax → List String
  | .nil => .nil
  | .cons _ _ => .cons \"(indexed)\" .nil
def ctorStrs : List CtorView → List String
  | .nil => .nil
  | .cons c cs => List.append (.cons (CtorView.name c) (fieldStrs (CtorView.fields c)))
      (List.append (idxStrs (CtorView.indices c)) (ctorStrs cs))
def paramStrs : List ParamView → List String
  | .nil => .nil
  | .cons p ps => .cons (ParamView.name p) (paramStrs ps)
syntax (name := shape) \"shape\" ident : command
def shapeM : CommandMacro := fun stx => do
  n ← Syntax.identName (Syntax.getArg stx 1);
  r ← MacroM.getInductive n;
  match r with
  | .none => MacroM.throw \"not an inductive type\"
  | .some v => do
    let x := Syntax.mkIdent (String.append n \".shape\");
    let kind := match IndView.isStructure v with
      | .true => \"structure\"
      | .false => \"inductive\";
    let l := strs (.cons kind (List.append (paramStrs (IndView.params v)) (ctorStrs (IndView.ctors v))));
    MacroM.pure (.cons `(command| def $x : List String := $l) .nil)
attribute [macro command.shape] shapeM
"

def derivingGroup : Group where
  name := "deriving"
  exercise := "HD8"
  cases := [
    { name := "a command macro expands into several commands", run := fun _ =>
        okLib ("import Prelude\nsyntax (name := two) \"two_defs\" ident ident : command\n" ++
          "def twoM : CommandMacro := fun stx => do\n  let a := Syntax.getArg stx 1;\n  let b := Syntax.getArg stx 2;\n" ++
          "  n ← Syntax.identName a;\n  let av := Syntax.mkVar n;\n  MacroM.pure (.cons `(command| def $a : Nat := 1) (.cons `(command| def $b : Nat := Nat.add $av $av) .nil))\n" ++
          "attribute [macro command.two] twoM\ntwo_defs one two\n#eval two") ["2"] },
    { name := "a `Macro` for a command kind expands to one command", run := fun _ =>
        okLib ("import Prelude\nsyntax (name := one) \"one_def\" ident : command\n" ++
          "def oneM : Macro := fun stx => do\n  let a := Syntax.getArg stx 1;\n  MacroM.pure `(command| def $a : Nat := 7)\n" ++
          "attribute [macro command.one] oneM\none_def seven\n#eval seven") ["7"] },
    { name := "a failing command macro is an error at the command", run := fun _ =>
        failsLib ("import Prelude\nsyntax (name := bad) \"bad_cmd\" : command\n" ++
          "def badM : CommandMacro := fun _ => MacroM.throw \"nope\"\nattribute [macro command.bad] badM\nbad_cmd") "macro badM: nope" },
    { name := "reflection: an inductive type's parameters, constructors and fields", run := fun _ =>
        okLib (shapeMacro ++ "inductive T (A : Type) (n : Nat) where\n  | a\n  | b (x : A) (t : T A n) (k : Nat)\nshape T\n#eval T.shape")
          [".cons \"inductive\" (.cons \"A\" (.cons \"n\" (.cons \"a\" (.cons \"b\" (.cons \"x\" (.cons \"*t\" (.cons \"k\" .nil)))))))"] },
    { name := "reflection: a structure, and an indexed family", run := fun _ =>
        okLib (shapeMacro ++ "structure P where\n  x : Nat\n  y : Bool\nshape P\n#eval P.shape\n" ++
          "inductive V (A : Type) : Nat → Type where\n  | nil : V A 0\n  | cons {n : Nat} (x : A) (xs : V A n) : V A (.succ n)\nshape V\n#eval V.shape")
          [".cons \"structure\" (.cons \"mk\" (.cons \"x\" (.cons \"y\" .nil)))",
           ".cons \"inductive\" (.cons \"A\" (.cons \"nil\" (.cons \"(indexed)\" (.cons \"cons\" (.cons \"n\" (.cons \"x\" (.cons \"*xs\" (.cons \"(indexed)\" .nil))))))))"] },
    { name := "reflection: a declaration's type as syntax", run := fun _ =>
        okLib ("import Prelude\nsyntax (name := alias) \"alias\" ident ident : command\n" ++
          "def aliasM : CommandMacro := fun stx => do\n  let a := Syntax.getArg stx 1;\n  let b := Syntax.getArg stx 2;\n" ++
          "  n ← Syntax.identName b;\n  t ← MacroM.getType n;\n  match t with\n  | .none => MacroM.throw \"unknown\"\n" ++
          "  | .some ty => do\n    let bv := Syntax.mkVar n;\n    MacroM.pure (.cons `(command| def $a : $ty := $bv) .nil)\n" ++
          "attribute [macro command.alias] aliasM\nalias plus Nat.add\n#check plus") ["plus : Nat → Nat → Nat"] },
    { name := "deriving Repr, BEq, Inhabited for an enumeration", run := fun _ =>
        okDeriving ("import Deriving\ninductive C where\n  | r\n  | g\n  deriving Repr, BEq, Inhabited\n" ++
          "#eval Repr.repr C.g\n#eval BEq.beq C.r C.g\n#eval BEq.beq C.g C.g\n#eval Repr.repr (Inhabited.default : C)")
          ["\"C.g\"", ".false", ".true", "\"C.r\""] },
    { name := "deriving with parameters and recursion", run := fun _ =>
        okDeriving ("import Deriving\ninductive Tree (A : Type) where\n  | leaf\n  | node (l : Tree A) (x : A) (r : Tree A)\n" ++
          "  deriving Repr, BEq, Inhabited\ndef t : Tree Nat := .node .leaf 1 (.node .leaf 2 .leaf)\n" ++
          "#eval Repr.repr t\n#eval BEq.beq t t\n#eval BEq.beq t (.node .leaf 1 .leaf)\n#check @instReprTreeA")
          ["\"Tree.node Tree.leaf 1 (Tree.node Tree.leaf 2 Tree.leaf)\"", ".true", ".false",
           "instReprTreeA : {A : Type} → [inst✝ : Repr A] → Repr (Tree A)"] },
    { name := "deriving for a structure, and for the prelude's types", run := fun _ =>
        okDeriving ("import Deriving\nstructure P where\n  x : Nat\n  s : String\n  deriving Repr, BEq, Inhabited\n" ++
          "#eval Repr.repr (List.cons (P.mk 1 \"a\") List.nil)\n#eval BEq.beq (P.mk 1 \"a\") (P.mk 1 \"b\")\n#eval Repr.repr (Inhabited.default : P)")
          ["\"List.cons (P.mk 1 \\\"a\\\") List.nil\"", ".false", "\"P.mk 0 \\\"\\\"\""] },
    { name := "deriving instance … for …, after the fact", run := fun _ =>
        okDeriving ("import Deriving\ninductive S where\n  | c (r : Nat)\n  | d (o : Option Bool) (w : Nat)\n" ++
          "deriving instance Repr, BEq for S\n#eval Repr.repr (S.d (Option.some Bool.true) 3)")
          ["\"S.d (Option.some Bool.true) 3\""] },
    { name := "Repr for an indexed family (implicit fields are not shown)", run := fun _ =>
        okDeriving ("import Deriving\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A 0\n" ++
          "  | cons {n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)\n  deriving Repr\n" ++
          "#eval Repr.repr (Vec.cons 1 (Vec.cons 2 Vec.nil))") ["\"Vec.cons 1 (Vec.cons 2 Vec.nil)\""] },
    { name := "deriving BEq for an indexed family is an error", run := fun _ =>
        failsDeriving ("import Deriving\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A 0\n" ++
          "  | cons {n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)\n  deriving BEq") "indexed families are not supported" },
    { name := "deriving a class without a deriver is an error", run := fun _ =>
        failsDeriving "import Deriving\ninductive X where\n  | x\n  deriving Frob" "no deriver for Frob" },
    { name := "Inhabited needs a non-recursive constructor", run := fun _ =>
        failsDeriving "import Deriving\ninductive I where\n  | more (i : I)\n  deriving Inhabited" "every constructor of I is recursive" },
    { name := "the example runs", run := fun _ => do
        let src ← IO.FS.readFile "examples/deriving.wiz"
        let s ← derivingRun src
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}") }
  ]

/-- Every `lib/*.wiz`, by module name. -/
def libLoader : IO (Name → Option String) := do
  let mut m : List (Name × String) := []
  for e in ← System.FilePath.readDir "lib" do
    if e.path.extension == some "wiz" then
      m := (e.path.fileStem.getD "", ← IO.FS.readFile e.path) :: m
  pure fun n => m.lookup n

/-- No errors, and these messages, with every library importable. -/
def okLibs (input : String) (infos : List String := []) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) input { loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr (s.messages.toList.map (·.text))).pretty

/-- Exactly one error, mentioning `fragment`, with every library importable. -/
def failsLibs (input : String) (fragment : String) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) input { loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

/-- Build `main` with the C backend, with every library importable. -/
def cRunLibs (src : String) (expected : String) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) src { loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal (← toolchain) s "main" dir with
  | .ok v => checkEq expected v
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)

def vecPrelude : String := "import Vec
def v3 : Vec Nat 3 := .cons 10 (.cons 20 (.cons 30 .nil))
def w3 : Vec Nat 3 := .cons 1 (.cons 2 (.cons 3 .nil))
"

def bvPrelude : String := "import BitVec
def b8 (x : Nat) : BitVec 8 := BitVec.ofNat 8 x
"

/-- Index-refining matches on a self-contained `Vec` (no lib/Vec.wiz): the solution rule
casts a function, which erasure used to fail on, and `#eval` then ran a stub. -/
def refinePrelude : String := "import Prelude
inductive V (A : Type) : Nat → Type where
  | nil : V A 0
  | cons {0 n : Nat} (x : A) (xs : V A n) : V A (Nat.succ n)
def V.head {A : Type} {0 n : Nat} : V A (Nat.succ n) → A
  | .cons x _ => x
def V.zipWith {A B C : Type} (f : A → B → C) {0 n : Nat} : V A n → V B n → V C n
  | .nil, .nil => .nil
  | .cons a as, .cons b bs => .cons (f a b) (V.zipWith f as bs)
def V.sum {0 n : Nat} : V Nat n → Nat
  | .nil => 0
  | .cons x xs => x + V.sum xs
def v3 : V Nat 3 := .cons 10 (.cons 20 (.cons 30 .nil))
def w3 : V Nat 3 := .cons 1 (.cons 2 (.cons 3 .nil))
"

def vecGroup : Group where
  name := "vec"
  exercise := "Stage H0c"
  cases := [
    { name := "index-refining matches run: #eval, #run and C (regression: erasing a cast)", run := fun _ => do
        okLib (refinePrelude ++ "#eval V.head v3\n#run V.head v3\n#eval V.sum (V.zipWith Nat.mul v3 w3)\n#run V.sum (V.zipWith Nat.mul v3 w3)")
          ["10", "10", "140", "140"]
        cRun (refinePrelude ++ "def main : Nat := V.head v3 + V.sum (V.zipWith Nat.mul v3 w3)") "150" },
    { name := "the libraries check, theorems included", run := fun _ =>
        okLibs "import Vec\nimport BitVec" },
    { name := "access by Fin, and update", run := fun _ =>
        okLibs (vecPrelude ++ "#eval Vec.get v3 (Fin.of 3 2 rfl)\n#eval Vec.toList (Vec.set v3 (Fin.of 3 1 rfl) 99)\n" ++
          "#eval Vec.head v3\n#eval Vec.toList (Vec.tail v3)\n#eval Vec.last v3\n#eval Vec.toList (Vec.init v3)")
          ["30", ".cons 10 (.cons 99 (.cons 30 .nil))", "10", ".cons 20 (.cons 30 .nil)", "30", ".cons 10 (.cons 20 .nil)"] },
    { name := "an index out of range is rejected", run := fun _ =>
        failsLibs (vecPrelude ++ "def bad : Nat := Vec.get v3 (Fin.of 3 3 rfl)") "kernel rejected bad" },
    { name := "maps, zips and folds", run := fun _ =>
        okLibs (vecPrelude ++ "#eval Vec.toList (Vec.map Nat.succ v3)\n#eval Vec.toList (Vec.zipWith Nat.add v3 w3)\n" ++
          "#eval Vec.foldr Nat.add 0 v3\n#eval Vec.foldl (fun acc x => acc * 10 + x) 0 w3\n#eval Vec.toList (Vec.zip v3 w3)")
          [".cons 11 (.cons 21 (.cons 31 .nil))", ".cons 11 (.cons 22 (.cons 33 .nil))", "60", "123",
           ".cons (10, 1) (.cons (20, 2) (.cons (30, 3) .nil))"] },
    { name := "building and reshaping", run := fun _ =>
        okLibs (vecPrelude ++ "#eval Vec.toList (Vec.append v3 w3)\n#eval Vec.toList (Vec.reverse v3)\n" ++
          "#eval Vec.toList (Vec.replicate 2 7)\n#eval Vec.toList (Vec.splitAt 1 v3).2\n#eval Vec.toList (Vec.ofFn 4 Fin.val)\n" ++
          "#eval Vec.toList (Vec.shiftIn 5 v3)\n#eval Vec.toList (Vec.fromList (.cons 4 (.cons 5 .nil)))")
          [".cons 10 (.cons 20 (.cons 30 (.cons 1 (.cons 2 (.cons 3 .nil)))))", ".cons 30 (.cons 20 (.cons 10 .nil))",
           ".cons 7 (.cons 7 .nil)", ".cons 20 (.cons 30 .nil)", ".cons 0 (.cons 1 (.cons 2 (.cons 3 .nil)))",
           ".cons 5 (.cons 10 (.cons 20 .nil))", ".cons 4 (.cons 5 .nil)"] },
    { name := "the length is erased; Vec.length counts", run := fun _ =>
        okLibs (vecPrelude ++ "#erase Vec.cons\n#eval Vec.length (Vec.append v3 w3)\n" ++
          "def lenMap (n : Nat) (v : Vec Nat n) : Vec.length (Vec.map Nat.succ v) = n := Vec.length_eq (Vec.map Nat.succ v)")
          ["Vec.cons := (λA. (λn. (λx. (λxs. ⟨1 ◾ #1 #0⟩))))", "6"] },
    { name := "the kernel computes on literal lengths", run := fun _ =>
        okLibs (vecPrelude ++ "def t1 : Vec.foldr Nat.add 0 (Vec.replicate 4 5) = 20 := rfl\n" ++
          "def t2 : Vec.toList v3 = .cons 10 (.cons 20 (.cons 30 .nil)) := rfl\n" ++
          "#reduce Vec.foldr Nat.add 0 v3\n#reduce Vec.head v3") ["60", "10"] },
    { name := "rfl at a computed equation between a numeral and a constructor (was a known bug; fixed by equality at μ by constructor, D1)", run := fun _ =>
        okLibs (vecPrelude ++ "def t3 : Vec.length (Vec.map Nat.succ w3) = 3 := rfl") },
    { name := "a cast between Vec Nat (.succ 2) and Vec Nat 3 computes (numeral vs constructor index; elab-bugs 3)", run := fun _ =>
        okLibs (vecPrelude ++ "def u3 : Vec Nat (Nat.succ 2) := v3\n" ++
          "def c3 (e : Vec Nat (Nat.succ 2) = Vec Nat 3) : (cast e u3 : Vec Nat 3) = v3 := rfl\n" ++
          "#reduce fun (e : Vec Nat (Nat.succ 2) = Vec Nat 3) => Vec.toList (cast e u3 : Vec Nat 3)")
          ["fun e => .cons 10 (.cons 20 (.cons 30 .nil))"] },
    { name := "map_map, get_set and get_map, with the castRefl axiom (D1)", run := fun _ =>
        okLibs (vecPrelude ++ "def mm : Vec.map Nat.succ (Vec.map Nat.succ w3) = Vec.map (fun a => Nat.succ (Nat.succ a)) w3 := Vec.map_map Nat.succ Nat.succ w3\n" ++
          "def gs {A : Type} {0 n : Nat} (v : Vec A n) (i : Fin n) (x : A) : Vec.get (Vec.set v i x) i = x := Vec.get_set v i x\n" ++
          "def gm {A B : Type} (f : A → B) {0 n : Nat} (v : Vec A n) (i : Fin n) : Vec.get (Vec.map f v) i = f (Vec.get v i) := Vec.get_map f v i\n") },
    { name := "compiled, through the IR and C", run := fun _ => do
        okLibs (vecPrelude ++ "#run Vec.toList (Vec.reverse v3)\n#run Vec.get (Vec.set v3 (Fin.of 3 2 rfl) 7) (Fin.of 3 2 rfl)\n" ++
          "#run Vec.toList (Vec.zipWith Nat.mul v3 w3)")
          [".cons 30 (.cons 20 (.cons 10 .nil))", "7", ".cons 10 (.cons 40 (.cons 90 .nil))"]
        cRunLibs (vecPrelude ++ "def main : Nat := Vec.foldl Nat.add 0 (Vec.zipWith Nat.mul (Vec.reverse v3) (Vec.init (Vec.snoc w3 9)))") "100" },
    { name := "Nat division, powers and bits (the Prelude natives BitVec uses)", run := fun _ =>
        okLibs ("import Prelude\n#eval Nat.div 1000000007 13\n#eval Nat.mod 1000000007 13\n#eval Nat.pow 2 64\n" ++
          "#eval Nat.land 12 10\n#eval Nat.lor 12 10\n#eval Nat.xor 12 10\n#eval Nat.testBit 5 2\n#eval Nat.div 7 0\n" ++
          "def t : Nat.mod 300 256 = 44 := rfl\n#run Nat.shiftRight (Nat.pow 2 100) 98")
          ["76923077", "6", "18446744073709551616", "8", "14", "6", ".true", "0", "4"] },
    { name := "bit vectors: wrapping arithmetic", run := fun _ =>
        okLibs (bvPrelude ++ "#eval (b8 300).toNat\n#eval (BitVec.add (b8 200) (b8 100)).toNat\n#eval (BitVec.sub (b8 3) (b8 5)).toNat\n" ++
          "#eval (BitVec.neg (b8 1)).toNat\n#eval (BitVec.mul (b8 20) (b8 13)).toNat\n#eval (BitVec.udiv (b8 200) (b8 7)).toNat\n" ++
          "#eval (BitVec.umod (b8 200) (b8 7)).toNat\ndef t : (BitVec.add (b8 200) (b8 100)).toNat = 44 := rfl")
          ["44", "44", "254", "255", "4", "28", "4"] },
    { name := "bit vectors: bitwise, shifts, comparisons", run := fun _ =>
        okLibs (bvPrelude ++ "#eval (BitVec.and (b8 12) (b8 10)).toNat\n#eval (BitVec.or (b8 12) (b8 10)).toNat\n" ++
          "#eval (BitVec.xor (b8 12) (b8 10)).toNat\n#eval (BitVec.not (b8 12)).toNat\n#eval (BitVec.shl (b8 129) 1).toNat\n" ++
          "#eval (BitVec.lshr (b8 128) 3).toNat\n#eval (BitVec.ashr (b8 128) 3).toNat\n#eval BitVec.getBit (b8 5) 2\n" ++
          "#eval BitVec.msb (b8 128)\n#eval BitVec.slt (b8 255) (b8 0)\n#eval BitVec.ult (b8 255) (b8 0)")
          ["8", "14", "6", "243", "2", "16", "240", ".true", ".true", ".true", ".false"] },
    { name := "bit vectors: widths and bits as a Vec", run := fun _ =>
        okLibs (bvPrelude ++ "#eval (BitVec.concat (BitVec.ofNat 4 10) (BitVec.ofNat 4 3)).toNat\n" ++
          "#eval (BitVec.extract 5 2 (b8 60)).toNat\n#eval (BitVec.zeroExtend 16 (b8 200)).toNat\n" ++
          "#eval (BitVec.signExtend 16 (b8 200)).toNat\n#eval (BitVec.signExtend 4 (b8 200)).toNat\n" ++
          "#eval Vec.toList (BitVec.toVec (BitVec.ofNat 4 6))\n#eval (BitVec.ofVec (BitVec.toVec (b8 173))).toNat")
          ["163", "15", "200", "65480", "8", ".cons .false (.cons .true (.cons .true (.cons .false .nil)))", "173"] },
    { name := "bit vectors at 63, 64 and 65 bits, compiled", run := fun _ => do
        okLibs ("import BitVec\n#run (BitVec.mul (BitVec.ofNat 64 18446744073709551615) (BitVec.ofNat 64 3)).toNat\n" ++
          "#run (BitVec.add (BitVec.ofNat 65 36893488147419103231) (BitVec.ofNat 65 2)).toNat\n" ++
          "#run (BitVec.sub (BitVec.ofNat 63 0) (BitVec.ofNat 63 1)).toNat")
          ["18446744073709551613", "1", "9223372036854775807"]
        cRunLibs "import BitVec\ndef main : Nat := (BitVec.ashr (BitVec.ofNat 64 9223372036854775808) 63).toNat" "18446744073709551615" },
    { name := "one type family: a BitVec is a UIntN, both ways, and widths still count", run := fun _ => do
        okLibs ("import BitVec\ndef w (x : U32) : BitVec 32 := BitVec.add x (BitVec.ofNat 32 1)\n" ++
          "def u (x : BitVec 8) : U8 := UIntN.mul x x\n#eval (w (U32.ofNat 4294967295)).toNat\n#eval (u (BitVec.ofNat 8 20)).toNat\n" ++
          "def t : (UIntN.add (BitVec.ofNat 8 200) (U8.ofNat 100)).toNat = 44 := rfl")
          ["0", "144"]
        failsLibs "import BitVec\ndef bad (x : BitVec 8) : U16 := x" "mismatch" },
    { name := "a BitVec compiles to native words: no word object in the IR", run := fun _ => do
        let src := "import BitVec\ndef f (a b : BitVec 64) : BitVec 64 := BitVec.add (BitVec.xor a b) (BitVec.ashr a 3)\n" ++
          "def g (a : BitVec 64) : Bool := BitVec.slt a (BitVec.signExtend 64 (BitVec.extract 7 0 a))\n#ir f\n#ir g\n" ++
          "#ir BitVec.add\n#ir BitVec.ashr\n#ir BitVec.slt\n#ir BitVec.extract\n#ir BitVec.signExtend\n#ir BitVec.concat"
        let s := runFrontend (R := ZeroOneMany) src { loader := ← libLoader }
        let out := String.intercalate "\n" (s.messages.toList.map (·.text))
        check ((out.splitOn "ctor").length == 1 && (out.splitOn "proj").length == 1) s!"a word object in:\n{out}"
        check ((out.splitOn "wiz_word_ashr").length > 1 && (out.splitOn "wiz_word_slt").length > 1) s!"no natives in:\n{out}" }
  ]


/-! ### Phantom parameters

A parameter that no field mentions gets an erased phantom tail (`phantomTail`,
`Elab/Inductive.lean`), so it counts in conversion and unification and costs nothing at
run time. -/

/-- The same program with a phantom parameter (`B`/`Q` are `Box 8`/`Pt 8`) or with a
proof parameter instead, which gets no phantom (`Box (refl 0)`): the only difference is
the phantom tail. -/
def phantomPair (phantom : Bool) : String :=
  let (ps, args) := if phantom then (" (w : Nat)", " 8") else (" (h : 0 = 0)", " (refl 0)")
  s!"import Prelude\ninductive Box{ps} where\n  | mk (n : Nat)\nstructure Pt{ps} where\n  x : Nat\n  y : Nat\n" ++
  s!"def B : Type := Box{args}\ndef Q : Type := Pt{args}\n" ++
  "def get : B → Nat\n  | .mk n => n\ndef sum (p : Q) : Nat := p.x + p.y\n" ++
  "def main : Nat := get (.mk 3) + sum (Pt.mk 1 2)\n#ir get\n#ir sum\n#ir main\n"

/-- Rename the variables `x<n>` of IR or C in order of first occurrence (an erased
argument still takes a variable number). -/
def renumberVars (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out : String := ""
  let mut seen : Array String := #[]
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    let prevOk := i == 0 || !(cs[i-1]!.isAlphanum || cs[i-1]! == '_')
    if c == 'x' && prevOk && i + 1 < cs.size && cs[i+1]!.isDigit then
      let mut j := i + 1
      let mut num := ""
      while j < cs.size && cs[j]!.isDigit do
        num := num.push cs[j]!
        j := j + 1
      if j < cs.size && (cs[j]!.isAlphanum || cs[j]! == '_') then
        out := out.push c
        i := i + 1
      else
        let k := match seen.findIdx? (· == num) with
          | some k => k
          | none => seen.size
        if k == seen.size then seen := seen.push num
        out := out ++ s!"x{k}"
        i := j
    else
      out := out.push c
      i := i + 1
  return out

/-- Q4: description fields live exactly in `Sort (l+1)`; the elaborator lifts smaller
ones with `ULift`, invisibly (`Elab/Inductive.lean`, CoreSpec §4.1, §9.1). -/
def liftPrelude : String := "import Prelude
inductive Pos where
  | mk (n : Nat) (h : n = n)
def Pos.val (p : Pos) : Nat := match p with
  | .mk n _ => n
inductive Prod2.{u, v} (A : Type u) (B : Type v) : Type (max u v) where
  | mk (a : A) (b : B)
def Prod2.snd.{u, v} {A : Type u} {B : Type v} (p : Prod2 A B) : B := match p with
  | .mk _ b => b
inductive T3 : Type 1 where
  | leaf
  | node (f : Nat → T3)
def depth : T3 → Nat
  | .leaf => 0
  | .node f => Nat.succ (depth (f 0))
"

def liftGroup : Group where
  name := "lift"
  exercise := "Q4 (lifted description fields)"
  cases := [
    { name := "a proof field is lifted invisibly: constructor, pattern, printing", run := fun _ =>
        okLib (liftPrelude ++ "#eval Pos.val (Pos.mk 3 rfl)\n#check Pos.mk\n#reduce Pos.mk 3 rfl\n#reduce Pos.val (Pos.mk 3 rfl)")
          ["3", "Pos.mk : (n : Nat) → n = n → Pos", ".mk 3 ()", "3"] },
    { name := "the fields of Prod.{u,v} and the tag of a polymorphic type are lifted invisibly", run := fun _ =>
        okLib (liftPrelude ++ "#check Prod2.mk\n#eval Prod2.snd (Prod2.mk 1 Bool.true)\n#reduce Prod2.mk 1 Bool.false\n" ++
            "#check Prod2.casesOn\n#reduce Prod2.desc Nat Bool")
          ["Prod2.mk : {A : Type ?u0} → {B : Type ?u1} → A → B → Prod2 A B", ".true", ".mk 1 .false",
           "Prod2.casesOn : {A : Type ?u0} → {B : Type ?u1} → (0 motive : Prod2 A B → Sort ?u2) → ((a : A) → (b : B) → motive (.mk a b)) → (x : Prod2 A B) → motive x",
           "Desc.arg ω (ULift Enum [mk]) (fun t => ecase t [Desc.arg ω (ULift Nat) (fun a => Desc.arg ω (ULift Bool) (fun b => Desc.ret ()))])"] },
    { name := "an infinitary field over a smaller domain, in a type in Type 1 (structural recursion through it)", run := fun _ =>
        okLib (liftPrelude ++ "#eval depth (T3.node (fun _ => T3.node (fun _ => T3.leaf)))\n" ++
            "inductive Tr : Type 1 where\n  | leaf\n  | node (T : Type) (f : T → Tr)\n" ++
            "def Tr.size (t : Tr) : Nat := match t with\n  | .leaf => 0\n  | .node _ _ => 1\n#eval Tr.size (Tr.node Nat (fun _ => Tr.leaf))")
          ["2", "1"] },
    { name := "a lifted proof field in a coinductive type", run := fun _ =>
        okLib ("import Prelude\ncoinductive S where\n  hd : Nat\n  ok : True\n  tl : S\n" ++
            "def zs : S\n  | .hd => 0\n  | .ok => ()\n  | .tl => zs\n#eval S.hd (S.tl zs)\n#check S.ok") ["0", "S.ok : S → True"] },
    { name := "lifting is erased: the #ir of a lifted type is the unlifted one's", run := fun _ => do
        let src := "import Prelude\ninductive Box.{u} (A : Type u) : Type u where\n  | box (a : A)\n" ++
          "def unbox.{u} {A : Type u} (b : Box A) : A := match b with\n  | .box a => a\n" ++
          "inductive Box0 (A : Type) : Type where\n  | box (a : A)\n" ++
          "def unbox0 {A : Type} (b : Box0 A) : A := match b with\n  | .box a => a\n#ir unbox\n#ir unbox0\n" ++
          "inductive Pos where\n  | mk (n : Nat) (h : n = n)\ninductive Pos0 where\n  | mk (n : Nat)\n" ++
          "def Pos.val (p : Pos) : Nat := match p with\n  | .mk n _ => n\ndef Pos0.val (p : Pos0) : Nat := match p with\n  | .mk n => n\n" ++
          "#ir Pos.val\n#ir Pos0.val\n"
        let s := runFrontend (R := ZeroOneMany) src { loader := ← preludeLoader }
        match s.messages.toList.map (·.text) with
        | [a, b, c, d] =>
          checkEq (b.replace "unbox0" "unbox") a
          checkEq (d.replace "Pos0" "Pos") c
        | ms => throw (IO.userError s!"unexpected messages {ms}") },
    { name := "the surface Desc.arg takes a field only in exactly its universe", run := fun _ =>
        failsLib "import Prelude\ndef D : Desc Unit := Desc.arg 1 True (fun _ => Desc.ret ())" "type mismatch" }
  ]

def phantomGroup : Group where
  name := "phantom"
  exercise := "Phantom parameters"
  cases := [
    { name := "UIntN 8 and UIntN 16 are different types", run := fun _ =>
        failsLib "import Prelude\ninductive UIntN (w : Nat) where\n  | mk (toNat : Nat)\ndef f (x : UIntN 8) : UIntN 16 := x" "mismatch" },
    { name := "so rfl can't prove UIntN 8 = UIntN 16", run := fun _ =>
        failsLib "import Prelude\ninductive UIntN (w : Nat) where\n  | mk (toNat : Nat)\ndef e : UIntN 8 = UIntN 16 := rfl" "mismatch" },
    { name := "μ equality: UIntN 8 = UIntN 8 computes, UIntN 8 = UIntN 16 stays stuck", run := fun _ => do
        -- equality at μ computes to the index equation only when the descriptions agree,
        -- and a phantom parameter is part of the description, so the inequality is not
        -- refutable for an inductive (it is for a structure, below)
        let ty := "import Prelude\ninductive UIntN (w : Nat) where\n  | mk (toNat : Nat)\n"
        okLib (ty ++ "def same : UIntN 8 = UIntN 8 := fun _ => ()")
        failsLib (ty ++ "def stuck (e : UIntN 8 = UIntN 16) : Nat := e") "inferred: UIntN 8 = UIntN 16" },
    { name := "the width is inferred from the type", run := fun _ =>
        okLib ("import Prelude\ninductive UIntN (w : Nat) where\n  | mk (toNat : Nat)\nstructure S (w : Nat) where\n  x : Nat\n" ++
          "def width {ω w : Nat} (a : UIntN w) : Nat := w\ndef swidth {ω w : Nat} (a : S w) : Nat := w\n" ++
          "#eval width (UIntN.mk 3 : UIntN 8)\n#eval swidth (S.mk 1 : S 16)") ["8", "16"] },
    { name := "structures: S 8 and S 16 are different types", run := fun _ =>
        failsLib "import Prelude\nstructure S (w : Nat) where\n  x : Nat\ndef f (x : S 8) : S 16 := x" "mismatch" },
    { name := "structures: S 8 = S 16 is refutable", run := fun _ =>
        okLib ("import Prelude\nstructure S (w : Nat) where\n  x : Nat\n" ++
          "def ne (e : S 8 = S 16) : Empty := absurd (((e.2 0).1.2 16).1 (refl 16))") },
    { name := "structures: tuples end in (), and η still holds", run := fun _ =>
        okLib ("import Prelude\nstructure P (w : Nat) where\n  x : Nat\n  y : Nat\n" ++
          "def p : P 4 := (1, 2, ())\n#eval p.y\ndef eta {w : Nat} (q : P w) : q = P.mk q.x q.y := refl q") ["2"] },
    { name := "type parameters: Proxy Nat and Proxy Bool are different types", run := fun _ =>
        failsLib "import Prelude\ninductive Proxy (A : Type) where\n  | mk\ndef f (x : Proxy Nat) : Proxy Bool := x" "mismatch" },
    { name := "coinductive: signals in different clock domains are different types", run := fun _ => do
        let sig := "import Prelude\nstructure Domain where\n  period : Nat\ndef System : Domain := Domain.mk 10\ndef Fast : Domain := Domain.mk 1\n" ++
          "coinductive Signal (d : Domain) (A : Type) where\n  head : A\n  tail : Signal d A\n" ++
          "def konst {d : Domain} {A : Type} (a : A) : Signal d A\n  | .head => a\n  | .tail => konst a\n" ++
          "def reg {d : Domain} {A : Type} (init : A) (s : Signal d A) : Signal d A\n  | .head => init\n  | .tail => s\n"
        okLib (sig ++ "def sys : Signal System Nat := reg 1 (konst 2)\n#eval sys.tail.head") ["2"]
        failsLib (sig ++ "def crossDomain (s : Signal System Nat) : Signal Fast Nat := s") "mismatch" },
    { name := "indexed families: matching with index unification, and recursion", run := fun _ =>
        okLib ("import Prelude\ninductive V (w : Nat) (A : Type) : Nat → Type where\n  | nil : V w A .zero\n" ++
          "  | cons {0 n : Nat} (x : A) (xs : V w A n) : V w A (.succ n)\n" ++
          "def V.len {w : Nat} {A : Type} {0 n : Nat} : V w A n → Nat\n  | .nil => 0\n  | .cons _ xs => Nat.succ (V.len xs)\n" ++
          "def V.head {w : Nat} {A : Type} {0 n : Nat} : V w A (.succ n) → A\n  | .cons x _ => x\n" ++
          "def v : V 7 Nat 2 := .cons 5 (.cons 6 .nil)\n#eval V.len v\n#eval V.head v\n#run V.head v") ["2", "5", "5"] },
    { name := "sized recursion on a parameterised (and a phantom) type", run := fun _ =>
        okLib ("import Prelude\ninductive L (A : Type) where\n  | nil\n  | cons (a : A) (t : L A)\n" ++
          "def L.app {A : Type} {i : Size} : (L A)^i → L A → L A\n  | .nil, m => m\n  | .cons a t, m => .cons a (L.app t m)\n" ++
          "inductive N (w : Nat) where\n  | z\n  | s (n : N w)\n" ++
          "def N.add {i : Size} {w : Nat} : (N w)^i → N w → N w\n  | .z, m => m\n  | .s n, m => .s (N.add n m)\n" ++
          "#eval N.add (.s .z : N 3) (.s .z)\n#eval L.app (.cons 1 .nil) (.cons 2 .nil)")
          [".s (.s .z)", ".cons 1 (.cons 2 .nil)"] },
    { name := "deriving still works", run := fun _ =>
        okDeriving ("import Deriving\ninductive Tagged (w : Nat) where\n  | none\n  | some (n : Nat)\n  deriving Repr, BEq, Inhabited\n" ++
          "#eval Repr.repr (Tagged.some 3 : Tagged 8)\n#eval BEq.beq (Tagged.some 3 : Tagged 8) (Tagged.some 3)\n" ++
          "structure P (w : Nat) where\n  x : Nat\n  y : Nat\nderiving instance Repr, BEq for P\n#eval Repr.repr (P.mk 1 2 : P 5)")
          ["\"Tagged.some 3\"", ".true", "\"P.mk 1 2\""] },
    { name := "regions: Mut ρ A and Mut ρ' A are different types", run := fun _ =>
        failsLib ("import Prelude\naxiom Region : Type\nstructure Mut (ρ : Region) (A : Type) where\n  get : A\n" ++
          "def reborrow {ρ : Region} {A : Type} (m : Mut ρ A) : Mut ρ A := m\n" ++
          "def bad {ρ ρ' : Region} {A : Type} (m : Mut ρ A) : Mut ρ' A := m") "mismatch" },
    { name := "erased: the IR and the C don't change", run := fun _ => do
        let loader ← preludeLoader
        let run (phantom : Bool) : IO (List String × String) := do
          let src := phantomPair phantom
          let s := runFrontend (R := ZeroOneMany) src { loader }
          let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
          unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
          match Build.cProgram s "main" with
          | .ok (c, _) => pure (s.messages.toList.map (renumberVars ·.text), renumberVars c)
          | .error e => throw (IO.userError e)
        let (ir1, c1) ← run true
        let (ir0, c0) ← run false
        checkEq (repr ir0).pretty (repr ir1).pretty
        let l0 := c0.splitOn "\n"
        let l1 := c1.splitOn "\n"
        match (l0.zip l1).find? (fun (a, b) => a != b) with
        | some (a, b) => throw (IO.userError s!"the C differs:\n  without: {a}\n  with:    {b}")
        | none => check (l0.length == l1.length) "the C differs in length" },
    { name := "and it runs", run := fun _ => cRun (phantomPair true) "6" },
    { name := "structures: the last field is unboxed, so a one-field structure is its field (22i)", run := fun _ => do
        let src := "import Prelude\nstructure W where\n  val : List Nat\nstructure P (w : Nat) where\n  x : Nat\n  y : List Nat\n" ++
          "def w : W := W.mk (List.cons 1 List.nil)\ndef l : List Nat := List.cons 1 List.nil\n" ++
          "def p : P 3 := P.mk 2 (List.cons 1 List.nil)\ndef q : Nat × List Nat × Unit := (2, List.cons 1 List.nil, ())\n" ++
          "def unW (v : W) : List Nat := v.val\ndef swap (v : P 3) : P 3 := (v.x, v.y, ())\n" ++
          "#eval w\n#run w\n#run p\n#eval swap p\n#run swap p\n" ++
          "def wl : List W := List.cons w List.nil\n#run wl\n"
        let s := runFrontend (R := ZeroOneMany) src { loader := ← preludeLoader }
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
        checkEq ["(.cons 1 .nil, ())", "(.cons 1 .nil, ())", "(2, .cons 1 .nil, ())",
          "(2, .cons 1 .nil, ())", "(2, .cons 1 .nil, ())", ".cons (.cons 1 .nil, ()) .nil"]
          (s.messages.toList.map (·.text))
        let allocs (n : Name) : IO Nat := match (do
            let code ← (compileReachable s.globals s.builtins [n]).mapError toString
            let decls ← IR.lowerProgram code (.global n)
            let (_, a) ← IR.runProgram (decls.map (·.optimize))
            pure a : Except String Nat) with
          | .ok a => pure a
          | .error e => throw (IO.userError e)
        -- `W` is its list; `P` is one pair, as a raw `Nat × List Nat × Unit` is two
        checkEq (← allocs "l") (← allocs "w")
        checkEq ((← allocs "l") + 1) (← allocs "p")
        checkEq ((← allocs "l") + 2) (← allocs "q") }
  ]

/-! ## Regions: borrow checking as typing (lib/Region.wiz, Rust DSL RD12) -/

def regionsPush : String :=
  "def push1 {ρ : Region} (v : Uniq ρ (List Nat)) : Result (Unit × Uniq ρ (List Nat)) :=\n  .ok ((), Uniq.set v (List.cons 1 v.val))\n"
def regionsLongest : String :=
  "def longest {ρa ρb : Region} (0 h : Outlives ρa ρb) (x : Shr ρa Nat) (y : Shr ρb Nat) : Result (Shr ρb Nat) :=\n" ++
  "  match Nat.lt x.val y.val with\n  | .true => .ok y\n  | .false => .ok (Shr.weaken h x)\n"

/-- The front end's state for `src`, with every library importable. -/
def libsState (src : String) : IO (CommandState ZeroOneMany) := do
  let s := runFrontend (R := ZeroOneMany) src { loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure s

/-- The optimised IR of the program computing `n`: `n` and the functions lifted from it. -/
def libsIR (s : CommandState ZeroOneMany) (n : Name) : IO (List String) := do
  match (do
      let code ← (compileReachable s.globals s.builtins [n]).mapError toString
      IR.lowerProgram code (.global n) : Except String (Array IR.Decl)) with
  | .ok decls =>
    pure ((decls.filter (·.name.startsWith n)).toList.map (·.optimize.toString))
  | .error e => throw (IO.userError e)

/-- The objects allocated computing `n` on the checked heap (a leak is an error). -/
def libsAllocs (s : CommandState ZeroOneMany) (n : Name) : IO Nat := do
  match (do
      let code ← (compileReachable s.globals s.builtins [n]).mapError toString
      let decls ← IR.lowerProgram code (.global n)
      let (_, a) ← IR.runProgram (decls.map (·.optimize))
      pure a : Except String Nat) with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{n}: {e}")

def regionsGroup : Group where
  name := "regions"
  exercise := "lib/Region.wiz (Rust DSL lifetimes)"
  cases := [
    { name := "handles in different regions are different types; regions are inferred", run := fun _ => do
        okLibs ("import Region\ndef same {ρ : Region} (m : Mut ρ Nat (List Nat)) : Mut ρ Nat (List Nat) := m\n" ++
          "def get {ρ : Region} (x : Shr ρ Nat) : Nat := x.val\n#eval Shr.borrow Region.static 4 (fun ρ h x => .ok (get x))") [".ok 4"]
        failsLibs "import Region\ndef bad {ρ ρ' : Region} (m : Mut ρ Nat (List Nat)) : Mut ρ' Nat (List Nat) := m" "mismatch"
        failsLibs "import Region\ndef bad {ρ ρ' : Region} (x : Shr ρ Nat) : Shr ρ' Nat := x" "mismatch" },
    { name := "a mutable borrow scope hands the lender back", run := fun _ =>
        okLibs ("import Region\n" ++ regionsPush ++
          "#eval Uniq.borrow Region.static List.nil (fun ρ h v r => push1 r)") [".ok ((), .cons 1 .nil)"] },
    { name := "outlives evidence from nested scopes lets a reference flow outward", run := fun _ =>
        okLibs ("import Region\n" ++ regionsLongest ++
          "#eval Shr.borrow Region.static 3 (fun ρa ha a => Shr.borrow ρa 5 (fun ρb hb b =>\n" ++
          "  match longest hb a b with\n  | .ok r => .ok r.val\n  | .err e => .err e))") [".ok 5"] },
    { name := "without the bound, a &'a is not a &'b", run := fun _ =>
        failsLibs ("import Region\ndef longest {ρa ρb : Region} (x : Shr ρa Nat) (y : Shr ρb Nat) : Result (Shr ρb Nat) :=\n" ++
          "  match Nat.lt x.val y.val with\n  | .true => .ok y\n  | .false => .ok x") "mismatch" },
    { name := "returning a borrow of a local is a type error (E0515)", run := fun _ =>
        failsLibs ("import Region\ndef bad {ρ : Region} (x : Shr ρ Nat) : Result (Shr ρ Nat) :=\n" ++
          "  Shr.borrow ρ 5 (fun ρy hy y => .ok y)") "mismatch" },
    { name := "a borrow can't outlive its scope (E0597)", run := fun _ =>
        failsLibs ("import Region\n" ++ regionsLongest ++
          "def bad : Result Nat := Shr.borrow Region.static 3 (fun ρa ha a =>\n" ++
          "  match Shr.borrow ρa 5 (fun ρb hb b => longest hb a b) with\n  | .ok r => .ok r.val\n  | .err e => .err e)")
          "escapes the scope" },
    { name := "using the lender while it is mutably borrowed is a type error (E0499/E0502)", run := fun _ => do
        failsLibs ("import Region\n" ++ regionsPush ++
          "def bad : Result (Nat × List Nat) := Uniq.borrow Region.static List.nil (fun ρ h v r =>\n" ++
          "  match push1 r with\n  | .ok q => .ok (List.length v, q.2)\n  | .err e => .err e)") "mismatch"
        failsLibs ("import Region\n" ++ regionsPush ++
          "def bad : Result (Unit × List Nat) := Uniq.borrow Region.static List.nil (fun ρ1 h1 v r1 =>\n" ++
          "  match Uniq.borrow ρ1 v (fun ρ2 h2 v r2 => push1 r2) with\n  | .ok q => .ok ((), r1)\n  | .err e => .err e)") "mismatch" },
    { name := "handles can't be forged outside lib/Region.wiz (private constructors, 13b)", run := fun _ => do
        failsLibs "import Region\ndef forge {ρ : Region} : Shr ρ Nat := Shr.mk 5" "'Shr.mk' is private to module Region"
        failsLibs "import Region\ndef forge {ρ : Region} (s : List Nat) : Uniq ρ (List Nat) := Uniq.mk s" "private"
        failsLibs "import Region\ndef forge {ρ : Region} : Lent ρ Nat := .mk ()" "Lent"
        failsLibs "import Region\ndef forge {ρ : Region} : Shr ρ Nat := (5, ())" "Shr"
        failsLibs ("import Region\nstructure MyShr (ρ : Region) (A : Type) where\n  val : A\n" ++
          "def forge {ρ : Region} : Shr ρ Nat := MyShr.mk 5") "mismatch" },
    { name := "a handle is its value at run time, and a scope is its body run in place (22i)", run := fun _ => do
        let s ← libsState ("import Region\n" ++ regionsPush ++
          "def get {ρ : Region} (x : Shr ρ Nat) : Nat := x.val\n" ++
          "def scoped (xs : List Nat) : Result (Unit × List Nat) := Uniq.borrow Region.static xs (fun ρ h v r => push1 r)\n" ++
          "def direct (xs : List Nat) : Result (Unit × List Nat) := .ok ((), List.cons 1 xs)\n" ++
          "def nested (a b : List Nat) : Result (List Nat × List Nat) :=\n" ++
          "  match Uniq.borrow Region.static a (fun ρa ha a ra =>\n" ++
          "    match Uniq.borrow ρa b (fun ρb hb b rb =>\n" ++
          "      match push1 rb with\n      | .ok q => .ok (ra, q.2)\n      | .err e => .err e) with\n" ++
          "    | .ok q => .ok (q.2, q.1)\n    | .err e => .err e) with\n" ++
          "  | .ok p => .ok (p.2, p.1)\n  | .err e => .err e\n" ++
          "def t1 : Result (Unit × List Nat) := scoped List.nil\n" ++
          "def t0 : Result (Unit × List Nat) := direct List.nil\n" ++
          "def t2 : Result (List Nat × List Nat) := nested List.nil List.nil\n#run t1\n#eval t1\n#run t2\n" ++
          "#run Shr.borrow Region.static 4 (fun ρ h x => .ok (get x))")
        let msgs := s.messages.toList.map (·.text)
        checkEq [".ok ((), .cons 1 .nil)", ".ok ((), .cons 1 .nil)", ".ok (.nil, .cons 1 .nil)", ".ok 4"] msgs
        -- `x.val` is `x`: no projection
        let getIR ← libsIR s "get"
        check (getIR.all fun d => (d.splitOn "proj").length == 1) s!"a projection:\n{"\n".intercalate getIR}"
        -- no closure for the scopes' bodies, and nothing lifted
        for n in ["scoped", "nested"] do
          let ir ← libsIR s n
          check (ir.length == 1 && ir.all fun d => (d.splitOn "pap").length == 1 && (d.splitOn "ap x").length == 1)
            s!"{n}: a closure:\n{"\n".intercalate ir}"
        -- a borrow costs no allocation: the same objects as without it
        checkEq (← libsAllocs s "t0") (← libsAllocs s "t1") }
  ]


/-! ## 11m–n: JSON and the infoview's layout (lib/Json.wiz, lib/Infoview.wiz) -/

/-- Elaborate with `Prelude`, `Json` and `Infoview` importable; no errors, and these infos. -/
def okInfoview (input : String) (infos : List String := []) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let json ← IO.FS.readFile "lib/Json.wiz"
  let iv ← IO.FS.readFile "lib/Infoview.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "Json" then some json
    else if m == "Infoview" then some iv else none
  let s := runFrontend (R := ZeroOneMany) input { loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr (s.messages.toList.map (·.text))).pretty

def jsonPrelude : String := r#"import Json
def parsed (s : String) : String := match Json.parse s with
  | .ok j => Json.render j
  | .error e => e
"#

/-- Goals built by hand (`A : Type`, `f : Nat → Nat → Nat → Nat` ⊢ `Nat → A`). -/
def goalPrelude : String := r#"import Infoview
def nat (r : Nat) : TT := .tag r "const" "Nat" (.text "Nat")
def arrow (r : Nat) (a b : TT) : TT := .tag r "pi" "" (.append (.cons a (.cons (.text " → ") (.cons b .nil))))
def hA : Hyp := .mk (.cons "A" .nil) (.tag 1 "sort" "" (.text "Type")) .none
def hf : Hyp := .mk (.cons "f" .nil) (arrow 2 (nat 3) (arrow 4 (nat 5) (arrow 6 (nat 7) (nat 8)))) .none
def g : Goal := .mk "" (.cons hA (.cons hf .nil)) (arrow 9 (nat 10) (.tag 11 "var" "A" (.text "A")))
def v : View := View.ofState 80 (.some (.cons g .nil)) .none
def esc (s : String) : List Char := .cons (Char.mk 27) (String.chars s)
"#

def infoviewGroup : Group where
  name := "infoview"
  exercise := "lib/Json.wiz, lib/Infoview.wiz (stages 11m, 11n)"
  cases := [
    { name := "JSON: printing escapes quotes, newlines; integers keep their sign", run := fun _ =>
        okInfoview (jsonPrelude ++ r#"#eval Json.render (Json.mkArr (.cons (.int .true 42) (.cons (.str "a\"b\nλ") (.cons .null .nil))))"#)
          [r#""[-42,\"a\\\"b\\nλ\",null]""#] },
    { name := "JSON: parse and print again (numbers, escapes, surrogate pairs, empty containers)", run := fun _ =>
        okInfoview (jsonPrelude ++ r#"#eval parsed " {\"a\": [1, -2, 3.5e10, -0.25E-3, true, null, {}], \"b\": \"\\u03bb\\ud83d\\ude00\\/\\t\", \"c\": []} ""#)
          [r#""{\"a\":[1,-2,3.5e10,-0.25E-3,true,null,{}],\"b\":\"λ😀/\\t\",\"c\":[]}""#] },
    { name := "JSON: ASCII output escapes non-ASCII, as surrogate pairs above U+FFFF", run := fun _ =>
        okInfoview (jsonPrelude ++ r#"#eval match Json.parse "\"\\u03bb\\ud83d\\ude00\\u0001\"" with
  | .ok j => Json.renderAscii j
  | .error e => e
#eval parsed "\"\\ud800x\"""#)
          [r#""\"\\u03bb\\ud83d\\ude00\\u0001\"""#, r#""\"�x\"""#] },
    { name := "JSON: errors say what and where", run := fun _ =>
        okInfoview (jsonPrelude ++ "#eval parsed \"[1, 2,]\"\n#eval parsed \"01\"\n#eval parsed \"[1] 2\"\n#eval parsed \"\\\"abc\"\n#eval parsed \"1.e5\"")
          [r#""unexpected character at offset 6""#, r#""bad number at offset 0""#, r#""trailing characters at offset 4""#,
           r#""unterminated string at offset 4""#, r#""bad number at offset 1""#] },
    { name := "JSON: paths into objects; decimal printing", run := fun _ =>
        okInfoview (jsonPrelude ++ r#"def path (s : String) : Option Json := match Json.parse s with
  | .ok j => Json.getPath j (.cons "x" (.cons "y" .nil))
  | .error _ => .none
#eval path "{\"x\": {\"y\": 7}}"
#eval Nat.repr 1234567890123"#)
          [".some (.int .false 7)", r#""1234567890123""#] },
    { name := "tagged text from JSON (the protocol's shape)", run := fun _ =>
        okInfoview (goalPrelude ++ r#"#eval match Json.parse "{\"tag\": [{\"ref\": 4, \"kind\": \"const\", \"name\": \"Nat\"}, {\"append\": [{\"text\": \"N\"}, {\"text\": \"at\"}]}]}" with
  | .ok j => TT.toString (TT.ofJson j)
  | .error e => e"#) [r#""Nat""#] },
    { name := "goals laid out, and wrapped with a hanging indent", run := fun _ =>
        okInfoview (goalPrelude ++ "#eval Infoview.plainLines (View.lines v)\n" ++
          "#eval Infoview.plainLines (View.lines (View.ofState 16 (.some (.cons g .nil)) (.some (.mk \"\" .nil (nat 12)))))")
          [r#".cons "Tactic state" (.cons "A : Type" (.cons "f : Nat → Nat → Nat → Nat" (.cons "⊢ Nat → A" .nil)))"#,
           r#".cons "Tactic state" (.cons "A : Type" (.cons "f : Nat → Nat →" (.cons "    Nat → Nat" (.cons "⊢ Nat → A" (.cons "" (.cons "Expected type" (.cons "⊢ Nat" .nil)))))))"#] },
    { name := "terminal lines: SGR colours by kind, the selection in reverse video", run := fun _ =>
        okInfoview (goalPrelude ++ "#eval Infoview.ansiLines 3 (View.lines (View.ofState 80 (.some .nil) (.some (.mk \"h\" .nil (arrow 1 (nat 2) (nat 3))))))")
          [r#".cons "\x1b[0;1;4mTactic state\x1b[0m" (.cons "\x1b[0;1;32mNo goals\x1b[0m" (.cons "\x1b[0m" (.cons "\x1b[0;1;4mExpected type\x1b[0m" (.cons "\x1b[0;1;4mcase h\x1b[0m" (.cons "\x1b[0;1;35m⊢\x1b[0m \x1b[0;34mNat\x1b[0m \x1b[0m→\x1b[0m \x1b[0;34;7mNat\x1b[0m" .nil)))))"#] },
    { name := "HTML: data-ref and data-idx on every subterm, text escaped", run := fun _ =>
        okInfoview (goalPrelude ++ "#eval Infoview.htmlState 2 .none (.some (.mk \"\" (.cons (.mk (.cons \"x\" .nil) (nat 1) .none) .nil) (.tag 2 \"var\" \"x<y\" (.text \"a&b\"))))")
          [r#""<h3>Expected type</h3><div class=\"goal\"><div class=\"hyp\"><span class=\"names\">x</span> : <span class=\"tt k-const\" data-ref=\"1\" data-idx=\"0\" title=\"Nat\">Nat</span></div><div class=\"target\"><span class=\"turnstile\">⊢</span> <span class=\"tt k-var sel\" data-ref=\"2\" data-idx=\"1\" title=\"x&lt;y\">a&amp;b</span></div></div>""#] },
    { name := "navigation: out, into, previous (wrapping), out at the top", run := fun _ =>
        okInfoview (goalPrelude ++ "#eval View.navigate v 4 .out\n#eval View.navigate v 2 .into\n#eval View.navigate v 0 .prev\n#eval View.navigate v 1 .out")
          ["2", "3", "11", "1"] },
    { name := "framing: Content-Length counts UTF-8 bytes; a partial message waits", run := fun _ =>
        okInfoview (goalPrelude ++ r#"#eval Rpc.frame "{\"a\":\"λ\"}"
#eval Rpc.unframe (String.chars (String.append (Rpc.frame "{\"a\":\"λ\"}") "Content-Le"))
#eval Rpc.unframe (String.chars (String.append "Content-Length: 12" (String.mk (.cons (Char.mk 13) (.cons (Char.mk 10) (.cons (Char.mk 13) (.cons (Char.mk 10) (String.chars "{\"a\":\"λ\"}"))))))))"#)
          [r#""Content-Length: 10\x0d\n\x0d\n{\"a\":\"λ\"}""#,
           r#".some ("{\"a\":\"λ\"}", .cons (.mk 67) (.cons (.mk 111) (.cons (.mk 110) (.cons (.mk 116) (.cons (.mk 101) (.cons (.mk 110) (.cons (.mk 116) (.cons (.mk 45) (.cons (.mk 76) (.cons (.mk 101) .nil))))))))))"#,
           ".none"] },
    { name := "keys: arrows, SGR mouse reports, page keys; terminal widths", run := fun _ =>
        okInfoview (goalPrelude ++ "#eval Key.decode (List.append (esc \"[A\") (List.append (String.chars \"\\tq\") (List.append (esc \"[<0;5;3M\") (esc \"[6~\"))))\n" ++
          "#eval Infoview.width (String.chars \"aλ😀́b\")")
          [".cons .up (.cons (.char 9) (.cons (.char 113) (.cons (.mouse 0 5 3 .true) (.cons .pageDown .nil))))", "5"] },
    { name := "the terminal infoview against a stub server, as text and in a pty (infoview/test.sh)", run := fun _ => do
        let tc ← toolchain
        let env := #[("WIZ_CFLAGS", some (" ".intercalate tc.cflags)), ("WIZ_LDFLAGS", some (" ".intercalate tc.ldflags))]
        let out ← IO.Process.output { cmd := "sh", args := #["infoview/test.sh"], env := env }
        unless out.exitCode == 0 do
          if ((out.stdout ++ out.stderr).splitOn "gmp.h").length > 1 then IO.println "    (skipped: no toolchain)"
          else throw (IO.userError s!"infoview/test.sh failed:\n{out.stdout}{out.stderr}") }
  ]

end Tests.Elab
