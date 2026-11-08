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
    { name := "cast computes on function types (and vanishes between equal types)", run := fun _ =>
        ok "#reduce fun (A : Type) (e : (A → A) = (A → A)) (f : A → A) => (cast e f : A → A)"
          ["fun A e f x => f x"] },
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

def coinductiveGroup : Group where
  name := "copatterns"
  exercise := "stage 4e"
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
        fails (sizedPrelude ++ "def bad {i : Size} : Nat^i → Nat\n  | .zero => .zero\n  | .succ n => bad (.succ n)") "not below" }
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

/-- `ok`, with `lib/` available to `import` (the tests run from the package root). -/
def okLib (input : String) (infos : List String := []) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let loader : Name → Option String := fun m => if m == "Prelude" then some prelude else none
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
    { name := "sized recursion", run := fun _ =>
        okLib (runPrelude ++ "#run fib (.succ (.succ (.succ (.succ (.succ .zero)))))")
          [".succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))"] },
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
    { name := "unused parameters are dropped at once", run := fun _ =>
        okLib "import Prelude\ndef k (x y : List Nat) : List Nat := x\n#ir k"
          ["def k x0 x1 :=\n  drop x1\n  ret x0"] }
  ]

/-- Build `main` with the C backend and compare its printed value. Skipped (passes) if
the C toolchain can't find GMP: set `WIZ_CFLAGS`/`WIZ_LDFLAGS` to run these. -/
def cRun (src : String) (expected : String) (llvm : Bool := false) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let s := runFrontend (R := ZeroOneMany) src { loader := fun m => if m == "Prelude" then some prelude else none }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal s "main" dir llvm with
  | .ok v => checkEq expected v
  | .error e =>
    let missing := ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1
    if missing then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)

/-- Build `main : IO _` with the C backend (and the `IO` library) and compare its output. -/
def ioRun (src : String) (expected : String) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let effLib ← IO.FS.readFile "lib/Eff.wiz"
  let stdLib ← IO.FS.readFile "lib/Std.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Eff" then some effLib
    else if m == "Std" then some stdLib else none
  let headers ← Build.preprocessHeaders src
  let s := runFrontend (R := ZeroOneMany) src { loader, cHeaders := (headers[·]?) }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal s "main" dir (timeout := some 120) with
  | .ok v => checkEq expected v
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)

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

/-- A Wiz string literal. -/
def wizLit (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c => if c == '"' then "\\\"" else if c == '\\' then "\\\\" else if c == '\n' then "\\n" else c.toString) ++ "\""

/-- A grammar descriptor as a Wiz `PD` (`selfhost/Parse.wiz`): sequences become binary. -/
partial def wizPD : ParserDescr → String
  | .atom t => s!"(PD.atom {wizLit t})"
  | .nonReserved t => s!"(PD.nonReserved {wizLit t})"
  | .ident => "PD.ident"
  | .num => "PD.num"
  | .str => "PD.str"
  | .cat c p => s!"(PD.cat {wizLit c} {p})"
  | .seq ps => ps.toList.foldr (fun p acc => if acc == "PD.empty" then wizPD p else s!"(PD.seq {wizPD p} {acc})") "PD.empty"
  | .many p => s!"(PD.many {wizPD p})"
  | .many1 p => s!"(PD.many1 {wizPD p})"
  | .optional p => s!"(PD.optional {wizPD p})"
  | .sepBy p sep t => s!"(PD.sepBy {wizPD p} {wizLit sep} {if t then ".true" else ".false"})"
  | .sepBy1 p sep t => s!"(PD.sepBy1 {wizPD p} {wizLit sep} {if t then ".true" else ".false"})"
  | .orelse p q => s!"(PD.orelse {wizPD p} {wizPD q})"
  | .node k p => s!"(PD.node {wizLit k} {wizPD p})"
  | .withPosition p => s!"(PD.withPosition {wizPD p})"
  | .withoutPosition p => s!"(PD.withoutPosition {wizPD p})"
  | .colGt => "PD.colGt"
  | .colGe => "PD.colGe"
  | .noWs => "PD.noWs"
  | .checkPrec p => s!"(PD.checkPrec {p})"

/-- A Wiz list literal. -/
def wizList (xs : List String) : String := xs.foldr (fun x acc => s!"(.cons {x} {acc})") ".nil"

/-- The parser tables as Wiz definitions: one per category, then `cats`. -/
def wizTables (t : ParserTables) : String := Id.run do
  let names := (t.cats.toList.map (·.1)).toArray.qsort (· < ·)
  let mut out := ""
  let mut i := 0
  for n in names do
    let cat := t.cats[n]!
    let ls := cat.leading.toList.map fun lp => s!"(Leading.mk {wizLit lp.kind} {lp.prec} {lp.priority} {wizPD lp.p})"
    let ts := cat.trailing.toList.map fun tp => s!"(Trailing.mk {wizLit tp.kind} {tp.prec} {tp.lhsPrec} {tp.priority} {wizPD tp.p})"
    out := out ++ s!"def cat{i} : Cat := Cat.mk {wizLit n} {wizList ls} {wizList ts}\n"
    i := i + 1
  out := out ++ s!"def cats : List Cat := {wizList ((List.range names.size).map (s!"cat{·}"))}\n"
  pure out

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

partial def toTerm : MTm → Term ZeroOneMany
  | var i => .var i
  | univ n => .sort (Level.ofNat (n + 1))
  | pi a b => .pi "x" .default (.qlit .many) a.toTerm b.toTerm
  | lam b => .lam "x" b.toTerm
  | app f a => .app f.toTerm a.toTerm
  | letE t v b => .letE "x" (.qlit .many) t.toTerm v.toTerm b.toTerm
  | ann t ty => .ann t.toTerm ty.toTerm
  | sigma a b => .sigma "x" (.qlit .many) a.toTerm b.toTerm
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
  | piq q a b => .pi "x" .default (.qlit q) a.toTerm b.toTerm
  | sigmaq q a b => .sigma "x" (.qlit q) a.toTerm b.toTerm
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

partial def ofTerm : Term ZeroOneMany → Option MTm
  | .var i => some (var i)
  | .sort l => match l.toNat? with
    | some (n + 1) => some (univ n)
    | some 0 => some prop
    | _ => none
  | .pi _ _ (.qlit .many) a b => return pi (← ofTerm a) (← ofTerm b)
  | .pi _ _ (.qlit q) a b => return piq q (← ofTerm a) (← ofTerm b)
  | .lam _ b => return lam (← ofTerm b)
  | .app f a => return app (← ofTerm f) (← ofTerm a)
  | .sigma _ (.qlit .many) a b => return sigma (← ofTerm a) (← ofTerm b)
  | .sigma _ (.qlit q) a b => return sigmaq q (← ofTerm a) (← ofTerm b)
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

/-- Terms the differential test always checks (well-typed ones the generator rarely
builds whole), before the random ones. -/
def samples : List MTm :=
  [natTy, natZero, natSucc natZero, natSucc (natSucc natZero), ann natD (desc 0 (unit 0)),
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
    { name := "a file of definitions, checked in Wiz", run := fun _ => do
        let src ← ["selfhost/Lex.wiz", "selfhost/Parse.wiz", "selfhost/Kernel.wiz", "selfhost/Frontend.wiz"].mapM (fun (f : String) => IO.FS.readFile f)
        let body := "\n".intercalate (src.map fun f => "\n".intercalate ((f.splitOn "\n").filter (!·.startsWith "import")))
        let t := Builtin.tables
        let file := "def N : Type 1 := (A : Type) → (A → A) → A → A\ndef two : N := fun A s z => s (s z)\n" ++
          "def add (m n : N) : N := fun A s z => m A s (n A s z)\n#reduce add two two\n#check add two\n" ++
          "def bad : Type := Type\n#check bad\n"
        let prog := "import IO\nimport Std\n" ++ body ++ "\n" ++ wizTables t ++
          s!"def tokens : List String := {wizList (t.tokens.toList.map wizLit)}\n" ++
          s!"def main : IO Unit := printAll (checkFile cats tokens {wizLit file})\n"
        ioRun prog ("N : U1\ntwo : N\nadd : (x0 : N) → (x1 : N) → N\nλx0. λx1. λx2. (x1 (x1 (x1 (x1 x2))))\n" ++
          "(x0 : N) → N\n" ++
          "error: type mismatch: expected U0, got U1\nerror: unknown identifier bad\n") },
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
        ioRun (kernel ++ "\n" ++ decl ++ printAll ++ main) ("\n".intercalate expected ++ "\n") }
  ]

def languageGroup : Group where
  name := "language"
  exercise := "Stage 13"
  cases := [
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
        okLib "import Prelude\ndef f (first exact : Nat) : Nat := Nat.add first exact\n#eval f 1 2\ndef t : Nat := by exact 3" ["3"] }
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
    { name := "numbers, with GMP for big ones", run := fun _ =>
        cRun (llvm := llvm) "import Prelude\ndef fact : Nat → Nat\n  | .zero => 1\n  | .succ n => (.succ n) * fact n\ndef main : Nat := fact 25"
          "15511210043330985984000000" },
    { name := "strings", run := fun _ =>
        cRun (llvm := llvm) "import Prelude\ndef main : String := String.append \"hello, \" \"world\"" "\"hello, world\"" },
    { name := "closures", run := fun _ =>
        cRun (llvm := llvm) "import Prelude\ndef adder (n : Nat) : Nat → Nat := fun x => x + n\ndef twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)\ndef main : Nat := twice (adder 10) 1" "21" },
    { name := "codata", run := fun _ =>
        cRun (llvm := llvm) (streamPrelude ++ "def main : Nat := (nats .zero).tail.tail.head") ".succ (.succ .zero)" },
    { name := "infinitary data", run := fun _ =>
        cRun (llvm := llvm) (treePrelude ++ "def main : Nat := Tree.depthAt (.node (fun i => .node (fun j => .leaf))) 3") "3" },
    { name := "deep recursion (direct recursion, big stack)", run := fun _ =>
        cRun (llvm := llvm) "import Prelude\ndef sumTo : Nat → Nat\n  | .zero => 0\n  | .succ n => (.succ n) + sumTo n\ndef main : Nat := sumTo 100000"
          "5000050000" },
    { name := "type classes and do", run := fun _ =>
        cRun (llvm := llvm) ("import Prelude\ninstance : Monad Option where\n  pure := fun a => Option.some a\n" ++
          "  bind := fun x f => match x with\n    | .none => Option.none\n    | .some a => f a\n" ++
          "def main : Option Nat := do\n  a ← Option.some 1;\n  b ← Option.some 2;\n  Monad.pure (a + b)") ".some 3" },
    { name := "memoised suspensions (memo)", run := fun _ =>
        cRun (llvm := llvm) ("import Prelude\ndef twice (t : Unit → Nat) : Nat := t () + t ()\n" ++
          "def lazyAdd (m n : Nat) : Unit → Nat := memo (fun _ => m + n)\n" ++
          "def main : Nat := twice (lazyAdd 20 1) + twice (memo (fun _ => 0))") "42" }
  ]


def cGroup : Group where
  name := "c"
  exercise := "Exercise 8.2"
  cases := nativeCases false

/-- The same programs, through LLVM (`$WIZ_LLC`). -/
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
    { name := "numerals and native arithmetic", run := fun _ =>
        okLib "import Prelude\n#eval 100 * 100 * 100 - 1" ["999999"] },
    { name := "recursion over native numbers", run := fun _ =>
        okLib "import Prelude\ndef fact : Nat → Nat\n  | .zero => 1\n  | .succ n => (.succ n) * fact n\n#eval fact 20"
          ["2432902008176640000"] },
    { name := "numerals reduce in the kernel", run := fun _ =>
        okLib "import Prelude\ndef t : 2 + 2 = 4 := refl 4" },
    { name := "native equality", run := fun _ =>
        okLib "import Prelude\n#eval Nat.beq 3 3" [".true"] },
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

end Tests.Elab
