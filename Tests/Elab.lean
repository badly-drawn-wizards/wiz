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
def Eq {A : Type 1} (x y : A) : Type 2 := (P : A → Type 1) → P x → P y
def refl {A : Type 1} (x : A) : Eq x x := fun P px => px
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
        ok (church ++ "def p : Eq (add two two) four := refl four") },
    { name := "2 + 2 = 2 is a type mismatch", run := fun _ =>
        fails (church ++ "def p : Eq (add two two) two := refl two") "type mismatch" },
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
