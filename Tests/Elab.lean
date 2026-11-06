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
    { name := "cast along a reflexive equation is the identity (regularity)", run := fun _ =>
        ok "def reg (A : Type) (e : A = A) (a : A) : cast e a = a := rfl" },
    { name := "J from transp and cast", run := fun _ =>
        ok substDef },
    { name := "J computes on refl", run := fun _ =>
        ok (substDef ++ "def substRefl {A : Type} (P : A → Type) (a : A) (pa : P a) : subst P (refl a) pa = pa := rfl") },
    { name := "cast computes on function types", run := fun _ =>
        ok "#reduce fun (A : Type) (e : (A → A) = (A → A)) (f : A → A) => (cast e f : A → A)"
          ["fun A e f x => cast (e.2 x) (f (cast e.1 x))"] },
    { name := "type equality", run := fun _ =>
        ok "def t : Type = Type := refl Type" },
    { name := "equality of proofs is rejected", run := fun _ =>
        fails "def bad (P : Prop) (p q : P) : p = q := rfl" "equality is for types" },
    { name := "wrong equation", run := fun _ =>
        fails "def bad (A : Type) (a b : A) : a = b := rfl" "type mismatch" }
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
        ok "def one : Qty := 1\ndef many : Qty := ω\ndef f {A : Type} (%one x : A) : A := x" }
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
            "  Desc.elim (fun _ => Bool) (fun i => true) (fun q S E ih => false) (fun q j E ih => false) D\n" ++
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
    { name := "unknown constructor via dot", run := fun _ =>
        fails (indPrelude ++ "def bad : Nat := .three") "no constructor three" }
  ]

end Tests.Elab
