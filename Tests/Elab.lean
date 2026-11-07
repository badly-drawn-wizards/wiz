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
          ["Vec.cons := (λA. (λn. (λx. (λxs. ⟨0 ⟨1⟩ ⟨0 ◾ ⟨0 #1 ⟨0 #0 ⟨0 ◾ ◾⟩⟩⟩⟩⟩))))"] }
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
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Eff" then some effLib else none
  let headers ← Build.preprocessHeaders src
  let s := runFrontend (R := ZeroOneMany) src { loader, cHeaders := (headers[·]?) }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal s "main" dir with
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
    { name := "type classes and do", run := fun _ =>
        cRun (llvm := llvm) ("import Prelude\ninstance : Monad Option where\n  pure := fun a => Option.some a\n" ++
          "  bind := fun x f => match x with\n    | .none => Option.none\n    | .some a => f a\n" ++
          "def main : Option Nat := do\n  a ← Option.some 1;\n  b ← Option.some 2;\n  Monad.pure (a + b)") ".some 3" }
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
