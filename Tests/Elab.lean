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
`wiz-notes/d1-experiment.md`.

`loopy` writes `Omega` out inline (`acOmega`: `δ ω` as lambdas, `unbox` as `ind`), not as
the global: a projection of a glued global stays glued until it is needed (`vFst`), and
the proof is never needed (the cast at `B2` doesn't look at it), so `(Omega …).1` would
never be unfolded. Inline, evaluating the proof is β-reduction and `ind` on the cast,
which loops with regularity. -/
def acDelta : String := "(fun (z : Top) => z T2 id2 z)"

/-- `ω`'s body inline (for `A : Prop`, `a : A`): `unbox (cast … (mk δ))`. The cast is
ascribed on both sides: since 4g `Box T2 = Box A` computes (to the equation of the codes),
so the elaborator can't read the two types off the proof's type. The target is `Box A`;
the source must be written `Box T2`, with the *name* `T2`: the inferred type of `mk δ` is
`Box (Top → Top)`, and the D1 regularity modes compare the two types syntactically
(`sameVal`), so with the inferred type regularity would not fire at `A := T2` and the
program would terminate for a reason that has nothing to do with the loop. -/
def acOmegaBody : String :=
  s!"ind (fun _ _ => A) (fun i xs ih => xs.1.2) (cast (apTy Prop Box T2 A (tautext T2 A id2 a)) (mk {acDelta} : Box T2) : Box A)"

/-- `Ω = δ ω`, inline -/
def acOmega (body : String := acOmegaBody) : String :=
  s!"({acDelta} (fun (A : Prop) (a : A) => {body}))"

def abelCoquand (omega : String := "Omega") (body : String := acOmegaBody) : String :=
  let omegaTm := if omega == "Omega" then acOmega body else omega
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
  s!"def loopy : (cast ({omegaTm} (P2 = P2) (refl P2)) ab : P2).1 = a0 := refl a0\n"

/-- The same program with the box inside a second box (`Box2 P` has a field of type
`Box P`): the outer box's field is not inert (it has a `Prop` field inside), so the cast
at `Box2` stays structural, and the program checks without regularity. -/
def abelCoquandNested : String :=
  ((abelCoquand (body := s!"ind (fun _ _ => A) (fun i xs ih => xs.1.2) (ind (fun _ _ => Box A) (fun i xs ih => xs.1.2) " ++
      s!"(cast (apTy Prop Box2 T2 A (tautext T2 A id2 a)) (mk2 (mk {acDelta}) : Box2 T2) : Box2 A))")).replace
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

/-- (P2) Checking `input` under `mode` (`full+eager`: without `lazyProofs`) finishes, without
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

/-- (P1) The probe of `wiz-notes/inert-regularity-probe.wiz`: an inert indexed family
whose index can hide a proof (`f p`), and statements that need InReg (regularity at inert
types). Each declaration is checked on its own. -/
def p1Prelude : String :=
  "inductive N where\n  | z\n  | s (n : N)\n" ++
  "inductive Fin2 : N → Type where\n  | fz {0 n : N} : Fin2 (.s n)\n  | fs {0 n : N} (k : Fin2 n) : Fin2 (.s n)\n" ++
  "def two : N := .s (.s .z)\n"

def p1Decls : List (String × String) := [
  -- control: no regularity at a type variable
  ("t5", "def t5 (A : Type) (k : A) (e : A = A) : (cast e k : A) = k := rfl"),
  -- InReg at an open index (`f p`)
  ("t1", "def t1 (P : Prop) (f : (0 _ : P) → N) (p : P) (k : Fin2 (f p)) (e : Fin2 (f p) = Fin2 (f p)) : (cast e k : Fin2 (f p)) = k := rfl"),
  -- the same, at convertible but not syntactically equal types
  ("t2", "def t2 (P : Prop) (f : (0 _ : P) → N) (p q : P) (k : Fin2 (f p)) (e : Fin2 (f p) = Fin2 (f q)) : (cast e k : Fin2 (f q)) = k := rfl"),
  -- two casts at convertible types
  ("h", "def h (P : Prop) (f : (0 _ : P) → N) (p q r : P) (k : Fin2 (f p)) (e1 : Fin2 (f p) = Fin2 (f r)) (e2 : Fin2 (f p) = Fin2 (f q)) : (cast e1 k : Fin2 (f r)) = (cast e2 k : Fin2 (f q)) := rfl"),
  -- h's instance r := p, by rfl: the δβ-reduct of h3 (P1: it was rejected)
  ("h2", "def h2 (P : Prop) (f : (0 _ : P) → N) (p q : P) (k : Fin2 (f p)) (e1 : Fin2 (f p) = Fin2 (f p)) (e2 : Fin2 (f p) = Fin2 (f q)) : (cast e1 k : Fin2 (f p)) = (cast e2 k : Fin2 (f q)) := rfl"),
  ("h3", "def h (P : Prop) (f : (0 _ : P) → N) (p q r : P) (k : Fin2 (f p)) (e1 : Fin2 (f p) = Fin2 (f r)) (e2 : Fin2 (f p) = Fin2 (f q)) : (cast e1 k : Fin2 (f r)) = (cast e2 k : Fin2 (f q)) := rfl\n" ++
    "def h3 (P : Prop) (f : (0 _ : P) → N) (p q : P) (k : Fin2 (f p)) (e1 : Fin2 (f p) = Fin2 (f p)) (e2 : Fin2 (f p) = Fin2 (f q)) : (cast e1 k : Fin2 (f p)) = (cast e2 k : Fin2 (f q)) := h P f p q p k e1 e2"),
  -- InReg at a closed index, on a variable
  ("g1", "def g1 (k : Fin2 (.s (.s .z))) (e : Fin2 (.s (.s .z)) = Fin2 (.s (.s .z))) : (cast e k : Fin2 (.s (.s .z))) = k := rfl"),
  -- ... through a definition (a glued name and its unfolding)
  ("g2", "def g2 (k : Fin2 two) (e : Fin2 two = Fin2 (.s (.s .z))) : (cast e k : Fin2 (.s (.s .z))) = k := rfl"),
  -- a generic statement at an open index, and its closed instance (by rfl)
  ("g3", "def g3 (n : N) (k : Fin2 n) (e1 e2 : Fin2 n = Fin2 n) : (cast e1 k : Fin2 n) = (cast e2 k : Fin2 n) := rfl\n" ++
    "def g3i (k : Fin2 two) (e1 e2 : Fin2 two = Fin2 two) : (cast e1 k : Fin2 two) = (cast e2 k : Fin2 two) := rfl")]

/-- The declarations of `p1Decls` that check under the given InReg mode. -/
def p1Accepted (m : InertReg) : List String :=
  p1Decls.filterMap fun (n, d) =>
    let s := runFrontend (R := ZeroOneMany) (p1Prelude ++ d ++ "\n") { globals := { inertReg := m } }
    if s.messages.any (·.severity == .error) then none else some n

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
    -- F2 (`wiz-notes/soundness-audit.md`): `vAbsurd` had no case for a glued value, so
    -- `absurd (lem h)` panicked and evaluated to `Sort 0`: `g h` was `Prop`
    { name := "F2: absurd on a lemma's result is stuck, not Prop", run := fun _ => do
        let p := "def lem (h : False) : False := h\ndef g (h : False) : Type := absurd (lem h)\n"
        ok (p ++ "def r (h : False) (x : g h) : g h := x\n#reduce fun (h : False) => g h") ["fun h => absurd h"]
        fails (p ++ "def u (h : False) : g h := True\n") "mismatch" },
    -- D1: no regularity by default: a cast at a variable type stays a cast
    { name := "cast along a variable `A = A` is not the identity (no regularity; it is with --regularity full)", run := fun _ => do
        let reg := "def reg (A : Type) (e : A = A) (a : A) : cast e a = a := rfl"
        fails reg "rfl: the two sides are not definitionally equal"
        okWith .full reg },
    { name := "J from transp and cast", run := fun _ =>
        ok substDef },
    { name := "J computes on refl at a data type, not at a variable family (no regularity)", run := fun _ => do
        let substRefl := substDef ++ "def substRefl {A : Type} (P : A → Type) (a : A) (pa : P a) : subst P (refl a) pa = pa := rfl"
        fails substRefl "rfl: the two sides are not definitionally equal"
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
          ["fun e => .s .z", "True", "fun n m => (0 e : (0 e : (0 e : True) × (0 e' : (0 e' : True) × ((0 x : Enum [z, s]) → cast (transp (fun y _ => (0 e'' : Unit = y) × ((0 x' : Desc Unit) → Unit = y)) (refl (Desc Unit × Unit)) e).1 (ecase x [Desc.ret (), Desc.rec ω () (Desc.ret ())]) = ecase x [Desc.ret (), Desc.rec ω () (Desc.ret ())])) × True) × ((0 x : N) → True)) × (0 e' : (0 e' : True) × ((0 x : Enum [nil, cons]) → cast (transp (fun y _ => (0 e'' : (N × Unit) = y) × ((0 x' : Desc (N × Unit)) → (N × Unit) = y)) (refl (Desc (N × Unit) × N × Unit)) e).1 (ecase x [Desc.ret (.z, ()), Desc.arg 0 N (fun n' => Desc.arg ω N (fun x' => Desc.rec ω (n', ()) (Desc.ret (.s n', ()))))]) = ecase x [Desc.ret (.z, ()), Desc.arg 0 N (fun n' => Desc.arg ω N (fun x' => Desc.rec ω (n', ()) (Desc.ret (.s n', ()))))])) × (0 e'' : n = m) × True",
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
          ["(0 e : (0 e : True) × (0 e' : (0 e' : True) × ((0 x : Enum [z, s]) → cast (transp (fun y _ => (0 e'' : Unit = y) × ((0 x' : Desc Unit) → Unit = y)) (refl (Desc Unit × Unit)) e).1 (ecase x [Desc.ret (), Desc.rec ω () (Desc.ret ())]) = ecase x [Desc.ret (), Desc.rec ω () (Desc.ret ())])) × True) × ((0 x : N) → (0 e' : True) × (0 e'' : (0 e'' : True) × ((0 x' : Enum [z, s]) → cast (transp (fun y _ => (0 e''' : Unit = y) × ((0 x'' : Desc Unit) → Unit = y)) (refl (Desc Unit × Unit)) e').1 (ecase x' [Desc.ret (), Desc.rec ω () (Desc.ret ())]) = ecase x' [Desc.ret (), Desc.rec ω () (Desc.ret ())])) × True)", "fun e u x => u x"] },
    { name := "a constructor's type carries its sort", run := fun _ =>
        ok (tyOfDef ++ "inductive Box (A : Type) where\n  | mk (a : A)\n" ++
          "#reduce TyOf (@Box.mk Unit) = (Unit → Box Unit)")
          ["(0 e : True) × ((0 x : Unit) → (0 e' : True) × (0 e'' : (0 e'' : True) × ((0 x' : Enum [mk]) → cast (transp (fun y _ => (0 e''' : Unit = y) × ((0 x'' : Desc Unit) → Unit = y)) (refl (Desc Unit × Unit)) e').1 (ecase x' [Desc.arg ω Unit (fun a => Desc.ret ())]) = ecase x' [Desc.arg ω Unit (fun a => Desc.ret ())])) × True)"] },
    { name := "a match on several scrutinees whose types mention a variable", run := fun _ =>
        ok "def pick (A : Type) (x y : A) : A := match x, y with\n  | a, b => b" },
    { name := "equality of proofs is rejected", run := fun _ =>
        fails "def bad (P : Prop) (p q : P) : p = q := rfl" "equality is for types" },
    { name := "wrong equation", run := fun _ =>
        fails "def bad (A : Type) (a b : A) : a = b := rfl" "rfl: the two sides are not definitionally equal" },
    -- D1: regularity is off by default, and the program checks; with `--regularity full`
    -- (or `nonprop`) and an evaluator that runs proofs (`--eager-proofs`, the behaviour
    -- before P2) checking it does not terminate
    { name := "D1 (Abel–Coquand): the program checks (no regularity: the box's cast casts its proof field)", run := fun _ => do
        ok (abelCoquand "omega")
        ok (abelCoquand) },
    { name := "D1 (Abel–Coquand): with regularity and eager proofs, checking the program does not terminate", run := fun _ =>
        checkDiverges (abelCoquand) "full+eager" },
    { name := "D1 (Abel–Coquand): a box in a box is not inert either (checks; loops with regularity and eager proofs)", run := fun _ => do
        unless (abelCoquandNested.splitOn "unbox2").length > 2 do throw (IO.userError "variant not built")
        ok abelCoquandNested
        checkDiverges abelCoquandNested "full+eager" },
    { name := "regularity at inert types: an indexed recursor computes at a data motive (Vec.length)", run := fun _ =>
        ok ("inductive N where\n  | z\n  | s (n : N)\n" ++
          "inductive V (A : Type) : N → Type where\n  | nil : V A .z\n  | cons {0 n : N} (x : A) (xs : V A n) : V A (.s n)\n" ++
          "def len {A : Type} {0 n : N} : V A n → N\n  | .nil => .z\n  | .cons _ xs => .s (len xs)\n" ++
          "def lenCons {A : Type} {0 n : N} (x : A) (xs : V A n) : len (V.cons x xs) = N.s (len xs) := rfl\n" ++
          "def castN (e : N = N) (n : N) : (cast e n : N) = n := rfl\n") },
    { name := "no regularity at a type with a variable parameter", run := fun _ =>
        fails ("inductive L (A : Type) where\n  | nil\n  | cons (x : A) (xs : L A)\n" ++
          "def castL (A : Type) (e : L A = L A) (l : L A) : (cast e l : L A) = l := rfl\n") "rfl: the two sides are not definitionally equal" },
    -- P1: InReg decided by ground equality is stable (h3 checks, and so does its reduct h2)
    { name := "P1: InReg is stable under substitution (the probe's reduct checks iff the term does)", run := fun _ =>
        checkEq (repr ["h", "h2", "h3", "g1", "g2", "g3"]).pretty (repr (p1Accepted .ground)).pretty },
    { name := "P1: with InReg_conv (decided by conversion), open indices too", run := fun _ =>
        checkEq (repr ["t1", "t2", "h", "h2", "h3", "g1", "g2", "g3"]).pretty (repr (p1Accepted .conv)).pretty },
    { name := "P1: the old syntactic InReg rejects the reduct h2 of h3 (documents the bug)", run := fun _ =>
        checkEq (repr ["t1", "h", "h3", "g1", "g3"]).pretty (repr (p1Accepted .syntactic)).pretty },
    { name := "D1: with eager proofs, a cast between propositions applies the equivalence, not regularity", run := fun _ => do
        let s := runFrontend (R := ZeroOneMany) abelCoquandLiteral { globals := { lazyProofs := false } }
        checkEq (repr ["fun x => x"]).pretty (repr (s.messages.toList.map (·.text))).pretty },
    { name := "D1 (R1): regularity only at non-propositions doesn't help with eager proofs (the box is a type)", run := fun _ =>
        checkDiverges (abelCoquand) "nonprop+eager" },
    { name := "D1 (R2, off): regularity only along refl, or none, checks the program", run := fun _ => do
        okWith .refl (abelCoquand)
        okWith .off (abelCoquand) },
    -- P2 (the default): proofs are never evaluated, so the loop, which lives in a proof,
    -- is never run, even with full regularity
    { name := "P2: proofs are never evaluated, so Abel–Coquand checks even with full regularity (and nested)", run := fun _ => do
        checkTerminates (abelCoquand) "full"
        checkTerminates abelCoquandNested "full"
        checkTerminates (abelCoquand) "nonprop"
        checkTerminates (abelCoquand) "off" },
    { name := "P2: a cast between propositions is stuck (a proof), not the equivalence applied", run := fun _ => do
        let s := runFrontend (R := ZeroOneMany) abelCoquandLiteral
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
  let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some prelude else none }
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

/-- `import Prelude`, `import Word`, `import Functor` and `import Logic`. -/
def preludeLoader : IO (Name → Option String) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let word ← IO.FS.readFile "lib/Word.wiz"
  let functor ← IO.FS.readFile "lib/Functor.wiz"
  let logic ← IO.FS.readFile "lib/Logic.wiz"
  pure fun m => if m == "Prelude" then some prelude else if m == "Word" then some word
    else if m == "Functor" then some functor else if m == "Logic" then some logic else none

/-- `ok`, with `lib/` available to `import` (the tests run from the package root). -/

def okLib (input : String) (infos : List String := []) : IO Unit := do
  let loader ← preludeLoader
  let s := runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr (s.messages.toList.map (·.text))).pretty

/-- Every message of `input` (with `lib/` importable), as `severity: text`, in order. -/
def msgsLib (input : String) : IO (List String) := do
  let loader ← preludeLoader
  let s := runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule }
  pure (s.messages.toList.map fun m =>
    s!"{match m.severity with | .error => "error" | .warning => "warning" | .info => "info"}: {m.text}")

/-- A language server with `src` open: the server and what it sent (the diagnostics). -/
def tacticLsp (src : String) : IO (LSP.Server × Array Lean.Json) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let srv : LSP.Server :=
    { libs := ({} : Std.HashMap String (String × String)).insert "Prelude" ("lib/Prelude.wiz", prelude), trusted := ["Prelude"] }
  let json (s : String) : Lean.Json := (Lean.Json.parse s).toOption.get!
  let (srv, _) := LSP.handle srv (json "{\"jsonrpc\":\"2.0\",\"id\":0,\"method\":\"initialize\",\"params\":{}}")
  pure (LSP.handle srv (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didOpen"),
    ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz"), ("version", (1 : Nat)), ("text", src)])])]))

/-- A recursive representation predicate in the style of separation logic, for `unfold`. -/
def unfoldPrelude : String := "import Prelude
def len : List Nat → Nat
  | .nil => 0
  | .cons _ xs => Nat.succ (len xs)
def Wrap (n : Nat) : Prop := n = n
def And' (A B : Prop) : Prop := (R : Prop) → (A → B → R) → R
def Pred : Type := Nat → Prop
def ex (J : Nat → Pred) : Pred := fun h => (R : Prop) → ((n : Nat) → J n h → R) → R
def cell (p x n : Nat) : Pred := fun h => h = Nat.add p (Nat.add x n)
def star (A B : Pred) : Pred := fun h => And' (A h) (B h)
def MList : List Nat → Nat → Pred
  | .nil, p => fun h => p = 0
  | .cons x L, p => ex (fun n => star (cell p x n) (MList L n))
def Ent (A B : Pred) : Prop := (h : Nat) → A h → B h
"

/-- Data in goals, and a tactic `dump` that traces the goal as a tree of head names. -/
def reflectPrelude : String := "import Prelude
inductive Vec (A : Type) : Nat → Type where
  | nil : Vec A 0
  | cons {n : Nat} (x : A) (xs : Vec A n) : Vec A (Nat.succ n)
inductive Prog : Type where
  | ret (n : Nat)
  | get (l : Nat) (k : Nat → Prog)
def swap (p : Nat) : Prog := Prog.get p (fun v => Prog.ret v)
def P (xs : List Nat) : Prop := True
def Q (c : Prog) : Prop := True
def V {n : Nat} (v : Vec Bool n) : Prop := True
def Expr.dumpL : Nat → List Expr → String
  | .zero, _ => \"…\"
  | _, .nil => \"\"
  | .succ f, .cons e es => String.append \" \" (String.append (match Expr.view e with
      | .const n .nil => n
      | .const n args => String.append \"(\" (String.append n (String.append (Expr.dumpL f args) \")\"))
      | .var i .nil => \"#\"
      | .var i args => String.append \"(#\" (String.append (Expr.dumpL f args) \")\")
      | .lit n => \"lit\"
      | .sort u => \"Sort\"
      | .pi _ _ _ _ _ => \"Π\"
      | .lam x b => String.append \"(λ\" (String.append x (String.append \".\" (String.append (Expr.dumpL f (.cons b .nil)) \")\")))
      | .other _ _ => \"?\") (Expr.dumpL f es))
def Expr.dump (e : Expr) : String := Expr.dumpL 1000 (.cons e .nil)
syntax (name := dump) \"dump\" : tactic
def dumpTac : Tactic := fun _ => do
  g ← TacticM.mainGoal;
  ty ← TacticM.goalType g;
  TacticM.trace (Expr.dump ty)
attribute [tactic tactic.dump] dumpTac
"

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
          "def k : Nat → Nat → Nat := by intros2; exact b") },
    -- trace (docs/stages/06-macros.md, 6d)
    { name := "trace is an info message at the tactic; trace_state shows the goals", run := fun _ => do
        let src := "import Prelude\ndef k : Nat → Bool → Nat := by\n  intro n\n  trace \"hello\"\n  trace_state\n  intro b\n  exact n"
        okLib src ["hello", "n : Nat\n⊢ Bool → Nat"]
        let loader ← preludeLoader
        let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
        checkEq ["4:3: info: hello"] ((s.messages.toList.take 1).map (·.render src)) },
    { name := "trace_state: several goals, and none", run := fun _ =>
        okLib ("import Prelude\ndef ap : (A B : Type) → (A → B) → A → B := by\n  intro A; intro B; intro f; intro a\n" ++
          "  apply f\n  trace_state\n  assumption\n  trace_state")
          ["A : Type\nB : Type\nf : A → B\na : A\n⊢ A", "no goals"] },
    { name := "a trace in a branch that fails is dropped with it", run := fun _ =>
        okLib "import Prelude\ndef t : Nat := by\n  try (trace \"dropped\"; exact Bool.true)\n  first | (trace \"dropped too\"; assumption) | (trace \"kept\"; exact 3)"
          ["kept"] },
    { name := "the traces before an error are still shown", run := fun _ => do
        checkEq ["info: one", "error: assumption: no hypothesis matches the goal"]
          (← msgsLib "import Prelude\ndef bad : Nat := by\n  trace \"one\"\n  assumption\n  trace \"never\"")
        let ms ← msgsLib "import Prelude\ndef bad : Nat := by\n  trace \"one\"\n  exact Bool.true"
        checkEq "info: one" (ms.headD "")
        checkEq 2 ms.length },
    { name := "TacticM.trace from a user tactic and from a macro; #check keeps traces", run := fun _ =>
        okLib ("import Prelude\nsyntax (name := say) \"say\" : tactic\n" ++
          "def sayTac : Tactic := fun _ => do\n  g ← TacticM.mainGoal;\n  s ← TacticM.ppGoal g;\n  t ← TacticM.goalType g;\n  u ← TacticM.ppExpr g t;\n" ++
          "  TacticM.trace (String.append \"goal: \" (String.append s (String.append \" / \" u)))\nattribute [tactic tactic.say] sayTac\n" ++
          "def k : Nat → Nat := by intro n; say; exact n\n" ++
          "syntax (name := tw) \"tw!\" term : term\ndef twMacro : Macro := fun stx => do\n  u ← TacticM.trace \"expanding\";\n  MacroM.pure (Syntax.getArg stx 1)\n" ++
          "attribute [macro term.tw] twMacro\ndef z : Nat := tw! 3\n#check (by trace \"checking\"; exact 1 : Nat)")
          ["goal: n : Nat\n⊢ Nat / Nat", "expanding", "checking", "1 : Nat"] },
    -- names (docs/stages/06-macros.md, 6e)
    { name := "intros takes the binders' names, inaccessible; rename_i names them", run := fun _ => do
        okLib ("import Prelude\ndef k : (n : Nat) → (b : Bool) → Nat → Nat := by\n  intros\n  trace_state\n  rename_i c, m\n  trace_state\n  exact m")
          ["n✝ : Nat\nb✝ : Bool\nx✝ : Nat\n⊢ Nat", "n✝ : Nat\nc : Bool\nm : Nat\n⊢ Nat"]
        okLib "import Prelude\ndef k : (n : Nat) → (n : Nat) → Nat := by\n  intros\n  trace_state\n  rename_i a\n  exact a"
          ["n✝ : Nat\nn✝1 : Nat\n⊢ Nat"]
        failsLib "import Prelude\ndef k : Nat → Nat := by\n  intros\n  rename_i a, b\n  exact a" "rename_i: more names than inaccessible hypotheses" },
    { name := "an inaccessible name cannot be written", run := fun _ => do
        let ms ← msgsLib "import Prelude\ndef bad : (n : Nat) → Nat := by\n  intros\n  exact n"
        checkEq ["error: unknown identifier 'n'"] ms },
    { name := "TacticM.introFresh: the binder's name, made fresh, and returned", run := fun _ =>
        okLib ("import Prelude\nsyntax (name := in3) \"in3\" : tactic\n" ++
          "def in3Tac : Tactic := fun _ => do\n  g ← TacticM.mainGoal;\n  p ← TacticM.introFresh g \"\";\n  q ← TacticM.introFresh p.2 \"\";\n  r ← TacticM.introFresh q.2 \"\";\n  s ← TacticM.introFresh r.2 \"n\";\n" ++
          "  u ← TacticM.trace (String.append p.1 (String.append \" \" (String.append q.1 (String.append \" \" (String.append r.1 (String.append \" \" s.1))))));\n" ++
          "  TacticM.replaceMainGoal (.cons s.2 .nil)\nattribute [tactic tactic.in3] in3Tac\n" ++
          "def k : (n : Nat) → (n : Nat) → (1 = 1) → Bool → Nat := by\n  in3\n  trace_state\n  exact n1")
          ["n n1 h n2", "n : Nat\nn1 : Nat\nh : True\nn2 : Bool\n⊢ Nat"] },
    { name := "a hole solved under a binder keeps the binder's name (not x0)", run := fun _ =>
        okLib ("import Prelude\ndef ap0 {B : Nat → Type} (f : (k : Nat) → B k) : B 0 := f 0\ndef g0 (n : Nat) : List Nat := .nil\n#check ap0 g0\n" ++
          "def Ex {A : Type} (P : A → Prop) : Prop := (R : Prop) → ((a : A) → P a → R) → R\n" ++
          "def Ex.elim {A : Type} {P : A → Prop} (R : Prop) (e : Ex P) (k : (a : A) → P a → R) : R := e R k\n" ++
          "def t (e : Ex (fun (n : Nat) => n = 0)) : Ex (fun (m : Nat) => m = 0) := by\n  apply Ex.elim _ e\n  intros\n  trace_state\n" ++
          "  rename_i w, h\n  exact (fun R k => k w h)")
          ["ap0 (fun k => List Nat) g0 : List Nat", "e : Ex Nat (fun n => n = 0)\na✝ : Nat\nh✝ : a✝ = 0\n⊢ Ex Nat (fun m => m = 0)"] },
    -- unfolding and rewriting (docs/stages/06-macros.md, 6f)
    { name := "unfold: a definition once, its match computed, the recursive call folded back", run := fun _ =>
        okLib (unfoldPrelude ++
          "def t2 (x : Nat) (L : List Nat) (p : Nat) : Ent (MList (.cons x L) p) (MList (.cons x L) p) := by\n  unfold MList\n  trace_state\n  unfold Ent\n  intros\n  assumption\n" ++
          "def t (x : Nat) (xs : List Nat) : Wrap (len (.cons x xs)) := by\n  unfold len\n  trace_state\n  unfold Wrap\n  rfl")
          ["x : Nat\nL : List Nat\np : Nat\n⊢ Ent (ex (fun n => star (cell p x n) (MList L n))) (ex (fun n => star (cell p x n) (MList L n)))",
           "x : Nat\nxs : List Nat\n⊢ Wrap (.succ (len xs))"] },
    { name := "unfold: several names; it fails when nothing changes (stuck, or absent); not a definition", run := fun _ => do
        okLib (unfoldPrelude ++
          "def t3 (L : List Nat) (p : Nat) : Ent (star (MList L p) (MList L p)) (MList L p) := by\n  unfold Ent, star\n  trace_state\n  intros\n  rename_i h, a\n  exact (a _ (fun x y => x))")
          ["L : List Nat\np : Nat\n⊢ (h : Nat) → And' (MList L p h) (MList L p h) → MList L p h"]
        failsLib (unfoldPrelude ++ "def t3 (L : List Nat) (p : Nat) : Ent (MList L p) (MList L p) := by\n  unfold MList\n  unfold Ent\n  intros\n  assumption")
          "unfold: nothing to unfold: the goal has no application of MList that computes"
        failsLib (unfoldPrelude ++ "def t3 (L : List Nat) (p : Nat) : Ent (MList L p) (MList L p) := by\n  unfold Ent, star\n  intros\n  assumption")
          "unfold: nothing to unfold: the goal has no application of star that computes"
        okLib (unfoldPrelude ++ "syntax (name := tryUnfold) \"try_unfold\" : tactic\n" ++
          "def tryUnfoldTac : Tactic := fun _ => do\n  g ← TacticM.mainGoal;\n  ty ← TacticM.goalType g;\n  ty' ← TacticM.unfold g \"MList\" ty;\n" ++
          "  s ← TacticM.ppExpr g ty';\n  TacticM.trace s\nattribute [tactic tactic.tryUnfold] tryUnfoldTac\n" ++
          "def t3 (L : List Nat) (p : Nat) : Ent (MList L p) (MList L p) := by\n  try_unfold\n  unfold Ent\n  intros\n  assumption")
          ["Ent (MList L p) (MList L p)"]
        failsLib "import Prelude\ndef t : Nat := by\n  unfold List.cons\n  exact 0" "unfold: List.cons is not a definition"
        failsLib "import Prelude\ndef t : Nat := by\n  unfold nope\n  exact 0" "unfold: unknown constant nope" },
    { name := "whnf computes the goal's head; change restates it (checked by conversion)", run := fun _ => do
        okLib (unfoldPrelude ++
          "def t4 (x : Nat) (L : List Nat) (p : Nat) : Ent (MList (.cons x L) p) (MList (.cons x L) p) := by\n  whnf\n  trace_state\n" ++
          "  change Ent (MList (.cons x L) p) (ex (fun n => star (cell p x n) (MList L n)))\n  trace_state\n  unfold Ent\n  intros\n  assumption")
          ["x : Nat\nL : List Nat\np : Nat\n⊢ (h : Nat) → MList (.cons x L) p h → MList (.cons x L) p h",
           "x : Nat\nL : List Nat\np : Nat\n⊢ Ent (MList (.cons x L) p) (ex (fun n => star (cell p x n) (MList L n)))"]
        failsLib "import Prelude\ndef t : Nat := by\n  change Bool\n  exact 0" "change: the new goal is not convertible with the old one" },
    { name := "rw: rewrite with an equation, left to right and back; the kernel checks the cast", run := fun _ => do
        okLib ("import Prelude\ndef r (a b : Nat) (h : a = b) (P : Nat → Prop) (pb : P b) : P a := by\n  rw h\n  trace_state\n  exact pb\n" ++
          "def r2 (a b : Nat) (h : a = b) (P : Nat → Type) (pa : P a) : P b := by\n  rw ← h\n  exact pa\n" ++
          "def r3 (f : Nat → Nat) (a b : Nat) (h : f a = b) (Q : Nat → Nat → Prop) (q : Q b b) : Q (f a) (f a) := by\n  rw h\n  exact q\n" ++
          "#check r2")
          ["a : Nat\nb : Nat\nh : a = b\nP : Nat → Prop\npb : P b\n⊢ P b",
           "r2 : (a : Nat) → (b : Nat) → a = b → (P : Nat → Type) → P a → P b"]
        failsLib "import Prelude\ndef r (a b c : Nat) (h : a = b) (P : Nat → Prop) (pc : P c) : P c := by\n  rw h\n  exact pc" "rewrite: the goal does not mention a"
        failsLib "import Prelude\ndef r (a : Nat) (P : Nat → Prop) (pa : P a) : P a := by\n  rw pa\n  exact pa" "rewrite: not an equation" },
    -- typed reflection (docs/stages/06-macros.md, 6g)
    { name := "constructor applications are reflected by name, with the type's parameters", run := fun _ =>
        okLib (reflectPrelude ++
          "def t1 (x : Nat) (L : List Nat) : P (.cons x (.cons (Nat.succ x) L)) := by\n  dump\n  exact ()\n" ++
          "def t2 : P (.cons 3 .nil) := by\n  dump\n  exact ()\n" ++
          "def t3 (b : Bool) : V (Vec.cons b (Vec.cons .true Vec.nil)) := by\n  dump\n  exact ()\n" ++
          "def t4 (p : Nat) : Q (Prog.get p (fun v => Prog.ret (Nat.succ v))) := by\n  dump\n  exact ()")
          [" (P (List.cons Nat # (List.cons Nat (Nat.succ #) #)))",
           " (P (List.cons Nat lit (List.nil Nat)))",
           " (V (Nat.succ (Nat.succ lit)) (Vec.cons Bool (Nat.succ lit) # (Vec.cons Bool lit Bool.true (Vec.nil Bool))))",
           " (Q (Prog.get # (λv. (Prog.ret (Nat.succ #)))))"] },
    { name := "a reflected goal reifies to the same goal; two reflections are syntactically equal", run := fun _ =>
        okLib (reflectPrelude ++ "syntax (name := again) \"again\" : tactic\n" ++
          "def againTac : Tactic := fun _ => do\n  g ← TacticM.mainGoal;\n  ty ← TacticM.goalType g;\n  ty2 ← TacticM.goalType g;\n" ++
          "  u ← TacticM.trace (match Expr.beq ty ty2 with\n    | .true => \"equal\"\n    | .false => \"different\");\n" ++
          "  g' ← TacticM.change g ty;\n  TacticM.replaceMainGoal (.cons g' .nil)\nattribute [tactic tactic.again] againTac\n" ++
          "def t (b : Bool) (x : Nat) : (V (Vec.cons b Vec.nil) → P (.cons x .nil)) := by\n  again\n  trace_state\n  intros\n  exact ()")
          ["equal", "b : Bool\nx : Nat\n⊢ V 1 (.cons 0 b .nil) → P (.cons x .nil)"] },
    { name := "whnf, then the constructor: a program is read off by its head (no unification)", run := fun _ =>
        okLib (reflectPrelude ++ "syntax (name := shape) \"shape\" : tactic\n" ++
          "def shapeArg : List Expr → TacticM Unit\n  | .cons c _ => do\n    g ← TacticM.mainGoal;\n    c' ← TacticM.whnf g c;\n    r ← TacticM.ctorApp c';\n" ++
          "    (match r with\n    | .some p => do\n      i ← TacticM.ctorInfo p.1;\n      TacticM.trace (String.append p.1 (String.append \" with fields\" (Expr.dumpL 100 p.2)))\n    | .none => TacticM.trace \"not a constructor\")\n" ++
          "  | .nil => TacticM.fail \"no argument\"\n" ++
          "def shapeTac : Tactic := fun _ => do\n  g ← TacticM.mainGoal;\n  ty ← TacticM.goalType g;\n  match Expr.appOf \"Q\" ty with\n  | .some args => shapeArg args\n  | .none => TacticM.fail \"not Q\"\n" ++
          "attribute [tactic tactic.shape] shapeTac\n" ++
          "def t (p : Nat) : Q (swap p) := by\n  shape\n  exact ()\n" ++
          "def t' (c : Prog) : Q c := by\n  shape\n  exact ()")
          ["Prog.get with fields # (λv. (Prog.ret #))", "not a constructor"] },
    { name := "traces reach the language server (a diagnostic) and the infoview (wiz/plainGoal)", run := fun _ => do
        let src := "import Prelude\ndef k : Nat → Nat := by\n  intro n\n  trace_state\n  exact n\n"
        let (srv, out) ← tacticLsp src
        let ds := match LSP.get? out[0]! ["params", "diagnostics"] with
          | some (.arr ds) => ds.toList
          | _ => []
        checkEq ["3: n : Nat\n⊢ Nat"] (ds.map fun d => s!"{LSP.getNat d ["severity"]}: {LSP.getStr d ["message"]}")
        checkEq [3] (ds.map fun d => LSP.getNat d ["range", "start", "line"])
        let (_, r) := LSP.handle srv ((Lean.Json.parse "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"wiz/plainGoal\",\"params\":{\"textDocument\":{\"uri\":\"file:///t.wiz\"},\"position\":{\"line\":3,\"character\":5}}}").toOption.get!)
        checkEq "```wiz\nn : Nat\n⊢ Nat\n```\n\nn : Nat\n⊢ Nat" (LSP.getStr r[0]! ["result", "rendered"])
        checkEq "[\"n : Nat\\n⊢ Nat\"]" (((LSP.get? r[0]! ["result", "messages"]).map (·.compress)).getD "") }
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

/-- (15c) Folded at compile time: arithmetic on literals (truncated subtraction, `n / 0 = 0`,
a power past 64 bits), a match on a constructor built in place, a test on a known number,
a second match on the same list. -/
def foldSrc : String := "import Prelude
def known (b : Bool) : Nat := match (List.cons 5 List.nil : List Nat) with
  | .nil => 0
  | .cons x _ => x + 1
def isTen (n : Nat) : Nat := match Nat.beq n 10 with
  | .true => n + 1
  | .false => 0
def again (xs : List Nat) : Nat := match xs with
  | .nil => 0
  | .cons x _ => match xs with
    | .nil => 7
    | .cons _ _ => x
def main : List Nat := .cons (3 * 4 + 10 - 20) (.cons (Nat.div 7 0) (.cons (Nat.sub 3 5) (.cons (known .true)
  (.cons (isTen 10) (.cons (isTen 3) (.cons (again (.cons 4 .nil)) (.cons (Nat.pow 2 70) (.cons (Nat.mod 7 0) .nil))))))))
"

def foldExpected : String :=
  ".cons 2 (.cons 0 (.cons 0 (.cons 6 (.cons 11 (.cons 0 (.cons 4 (.cons 1180591620717411303424 (.cons 7 .nil))))))))"

/-- (15g) Numerals around the boundaries of the representation: small numbers are 62-bit
immediates, bigger ones GMP objects (`2^62` is the first), and a few operations on them. -/
def bigLitSrc : String := "import Prelude
def a : Nat := 2147483648
def b : Nat := 4294967296
def c : Nat := 4611686018427387904
def d : Nat := 9223372036854775808
def e : Nat := 18446744073709551616
def f : Nat := 18446744073709551617
def g : Nat := 1000000000000000000000000000000
def h : Nat := 4611686018427387903
def main : List Nat := .cons a (.cons b (.cons c (.cons d (.cons e (.cons f (.cons g (.cons h (.cons (f - e)
  (.cons (Nat.div g 1000000000) (.cons (c + c) (.cons (Nat.mod (d + d) 1000) (.cons (h + 1) .nil))))))))))))
"

def bigLitExpected : String :=
  ".cons 2147483648 (.cons 4294967296 (.cons 4611686018427387904 (.cons 9223372036854775808 " ++
  "(.cons 18446744073709551616 (.cons 18446744073709551617 (.cons 1000000000000000000000000000000 " ++
  "(.cons 4611686018427387903 (.cons 1 (.cons 1000000000000000000000 (.cons 9223372036854775808 (.cons 616 " ++
  "(.cons 4611686018427387904 .nil))))))))))))"

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

/-- (15h) Calls of case-shaped definitions: a search that stops (`Bool.or`), a test of
every element (`Bool.and`), a second argument that never returns, a breadth-first
search whose next level is only built if the test fails, and a user function of that
shape (`orElse`). -/
def caseShapeSrc : String := "import Prelude
def range : Nat → List Nat → List Nat
  | .zero, acc => acc
  | .succ n, acc => range n (.cons n acc)
def mem (n : Nat) : List Nat → Bool
  | .nil => .false
  | .cons x xs => Bool.or (Nat.beq x n) (mem n xs)
def allLt (n : Nat) : List Nat → Bool
  | .nil => .true
  | .cons x xs => Bool.and (Nat.lt x n) (allLt n xs)
def double : List Nat → List Nat
  | .nil => .nil
  | .cons x xs => .cons (x + x) (double xs)
def reach (n : Nat) : Nat → List Nat → Bool
  | .zero, _ => .false
  | .succ fuel, xs => Bool.or (mem n xs) (reach n fuel (.cons 1 (double xs)))
partial def loop (n : Nat) : Bool := loop (n + 1)
partial def upFrom (n i : Nat) : Bool := Bool.or (Nat.beq i n) (upFrom n (i + 1))
def orElse (o : Option Nat) (d : Nat) : Nat := match o with
  | .some x => x
  | .none => d
def pick (o : Option Nat) (xs : List Nat) : Nat := orElse o (List.length (range 50 xs))
def s1 : Bool := mem 3 (range 1000 .nil)
def s2 : Bool := reach 8 100 (.cons 1 .nil)
def s3 : Bool := Bool.and (mem 2000 (range 1000 .nil)) (mem 5 (range 1000 .nil))
def s4 : Nat := pick (.some 4) (range 100 .nil)
def b2n : Bool → Nat
  | .true => 1
  | .false => 0
def foldB (f : Bool → Bool → Bool) : List Bool → Bool
  | .nil => .true
  | .cons b bs => f b (foldB f bs)
def rest : List Nat := .cons (b2n (Bool.and (mem 7 (range 5 .nil)) (loop 0))) (.cons (b2n (Bool.or (mem 3 (range 5 .nil)) (loop 0)))
  (.cons (b2n s1) (.cons (b2n s2) (.cons (b2n s3) (.cons s4 (.cons (b2n (allLt 5 (range 1000 .nil)))
  (.cons (pick .none (range 3 .nil)) (.cons (b2n (foldB Bool.and (.cons .true (.cons .false .nil)))) .nil))))))))
def main : List Nat := .cons (b2n (upFrom 10000000 0)) rest
"

def caseShapeRest : String :=
  ".cons 0 (.cons 1 (.cons 1 (.cons 1 (.cons 0 (.cons 4 (.cons 0 (.cons 53 (.cons 0 .nil))))))))"

def caseShapeExpected : String := s!".cons 1 ({caseShapeRest})"

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
        let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := fun _ => some prelude }
        let texts := s.messages.toList.map (·.text)
        check (texts.any fun t => (t.splitOn "reuse").length > 1) s!"no reuse in {texts}"
        check (texts.contains ".cons 2 (.cons 3 .nil)") s!"wrong result: {texts}" },
    { name := "unused parameters are borrowed (the caller drops them)", run := fun _ =>
        okLib "import Prelude\ndef k (x y : List Nat) : List Nat := x\n#ir k"
          ["def k x0 @&x1 :=\n  ret x0"] },
    { name := "constant folding and known constructors in the IR (15c)", run := fun _ => do
        let s := runFrontend (R := ZeroOneMany) (foldSrc ++ "#ir known\n#ir isTen\n#ir again\n#run main\n") { loader := ← preludeLoader }
        match (s.messages.toList.filter (·.severity == .info)).map (·.text) with
        | [known, isTen, again, run] =>
          -- a match on a constructor built in place: its field, plus one
          check ((known.splitOn "case").length == 1 && (known.splitOn ":= 6\n").length == 2) known
          -- in the `true` branch `n` is `10`, so `n + 1` is `11`
          check ((isTen.splitOn ":= 11\n").length == 2 && (isTen.splitOn "nat.add").length == 1) isTen
          -- the second match on the same list is gone
          checkEq 2 (again.splitOn "case").length
          checkEq foldExpected run
        | ms => throw (IO.userError s!"unexpected messages {ms}") },
    { name := "a self tail call is a jump to a join point (15f)", run := fun _ => do
        let src := "import Prelude\npartial def count (n acc : Nat) : Nat := match n with\n  | .zero => acc\n" ++
          "  | .succ m => count m (acc + 1)\n#ir count\n#run count 100000 0\n"
        let s := runFrontend (R := ZeroOneMany) src { loader := ← preludeLoader }
        match (s.messages.toList.filter (·.severity == .info)).map (·.text) with
        | [ir, run] =>
          check ((ir.splitOn "join").length > 1 && (ir.splitOn "jmp").length > 2) ir
          checkEq "100000" run
        | ms => throw (IO.userError s!"unexpected messages {ms}") },
    { name := "numerals at 2^31 … 2^64+1 and 10^30, interpreted and through the IR (15g)", run := fun _ =>
        okLib (bigLitSrc ++ "#eval main\n#run main\n") [bigLitExpected, bigLitExpected] },
    { name := "Bool.and/Bool.or calls are cases: the search is a loop that stops (15h)", run := fun _ => do
        let s := runFrontend (R := ZeroOneMany) (caseShapeSrc ++ "#ir mem\n#ir allLt\n#ir pick\n#run rest\n") { loader := ← preludeLoader }
        let errs := (s.messages.filter (·.severity == .error)).map (·.text)
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {errs}")
        match (s.messages.toList.filter (·.severity == .info)).map (·.text) with
        | [mem, allLt, pick, run] =>
          for ir in [mem, allLt] do
            -- no call of `Bool.or`/`Bool.and`: a case on the test, and the recursion a jump
            check ((ir.splitOn "Bool.or x").length == 1 && (ir.splitOn "Bool.and x").length == 1) ir
            check ((ir.splitOn "case").length == 3 && (ir.splitOn "jmp").length == 3) ir
          -- the default is computed in the `none` branch only
          check ((pick.splitOn "orElse").length == 1) pick
          match pick.splitOn "case" with
          | [before, after] => check ((before.splitOn "range").length == 1 && (after.splitOn "range").length == 2) pick
          | _ => throw (IO.userError pick)
          -- (`#run` is the IR's interpreter: the arguments that never return are not computed)
          checkEq caseShapeRest run
        | ms => throw (IO.userError s!"unexpected messages {ms}") },
    { name := "allocations of a short-circuiting search, before and after (15h)", run := fun _ => do
        let s := runFrontend (R := ZeroOneMany) caseShapeSrc { loader := ← preludeLoader }
        let allocs (n : Name) (caseShapes : Bool) : IO Nat := match (do
            let code ← (compileReachable s.globals s.builtins [n] (caseShapes := caseShapes)).mapError toString
            let decls ← IR.lowerProgram code (.global n)
            let (_, a) ← IR.runProgram (IR.optimizeProgram decls)
            pure a : Except String Nat) with
          | .ok a => pure a
          | .error e => throw (IO.userError s!"{n}: {e}")
        -- a search in a list that exists already: the same cells (but a loop, and it stops)
        checkEq [1000, 1000] [← allocs "s1" false, ← allocs "s1" true]
        -- the next level of the search is built only when the test failed
        checkEq [101, 4] [← allocs "s2" false, ← allocs "s2" true]
        -- the second list is not built when the first test fails
        checkEq [2000, 1000] [← allocs "s3" false, ← allocs "s3" true]
        -- the default of `orElse` is not computed for `some`
        checkEq [151, 101] [← allocs "s4" false, ← allocs "s4" true] }
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
  let s := runFrontend (R := ZeroOneMany) reuseSrc { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some prelude else none }
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
-- (not a bare constructor: that would be inlined, and the match on it folded away, 15c)
def split (xs : List Nat) : List Nat × List Nat := (xs, List.append xs .nil)
def both (xs : List Nat) : Nat := match split xs with
  | (a, b) => Nat.add (len a) (len b)
def t3 : Tree := Tree.node 2 (Tree.node 1 .leaf .leaf) (Tree.node 3 .leaf .leaf)
"

/-- The optimised IR of a function of `borrowSrc`, as lines. -/
def borrowIR (n : Name) : IO (List String) := do
  let s := runFrontend (R := ZeroOneMany) borrowSrc { trustedModule := Tests.libModule, loader := ← preludeLoader }
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
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← preludeLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal (← toolchain) s "main" dir llvm with
  | .ok v => checkEq expected v
  | .error e =>
    let missing := ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1
    if missing then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)

/-- (15f) Build `main` with the C compiler's optimiser off (`-O0`: it does no tail calls of
its own) and run it on a 1 MB stack (`WIZ_STACK_MB`): deep recursion overflows it, a loop
doesn't. -/
def cRunSmallStack (src : String) (expected : String) (llvm : Bool := false) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) src { loader := ← preludeLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let tc ← toolchain
  let tc := { tc with cflags := tc.cflags ++ ["-O0"] }
  let dir ← IO.FS.createTempDir
  let exe := dir / "wiz_main"
  let (decls, ty) ← match Build.irProgram s "main" with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  let built ← if llvm then Build.compileLLVM tc (LLVM.program decls false) exe (Build.extraC s ++ "\n" ++ C.glue (C.externs decls))
    else Build.compileC tc (C.program decls false (Build.extraC s)) exe
  match built with
  | .error e =>
    let missing := ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1
    if missing then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)
  | .ok () =>
    let out ← IO.Process.output { cmd := exe.toString, env := #[("WIZ_STACK_MB", some "1")] }
    unless out.exitCode == 0 do throw (IO.userError s!"the program failed ({out.exitCode}): {out.stderr.take 500}")
    match Build.parseValue out.stdout with
    | none => throw (IO.userError s!"could not read the result: {out.stdout}")
    | some v => checkEq expected (readback s.globals s.builtins (eval s.globals [] ty) v).pretty

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
    { name := "a left fold borrows the list (and its tail call is a loop)", run := fun _ => do
        borrowedUncounted "sumAcc" 1
        let ls ← borrowIR "sumAcc"
        -- (a self tail call is a jump to a loop, 15f)
        check (ls.any fun l => l.startsWith "jmp ") s!"no loop:\n{"\n".intercalate ls}" },
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
        let s := runFrontend (R := ZeroOneMany) (borrowSrc ++ "def lens : List Nat := mapL len (.cons .nil .nil)\n") { trustedModule := Tests.libModule, loader := ← preludeLoader }
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

/-- (L-1) Diverging terms in 0 positions the kernel checks erased: a constructor field at
0 (`Tagged.mk`, and the implicit one of `L.cons`), and a 0 field of a structure, with other fields
(`S`) and alone (`S1`; whatever the structure's layout, boxed or not). -/
def zeroFieldDecls : String :=
  "partial def loop (u : Unit) : Nat := loop u\n" ++
  "inductive L where\n  | nil\n  | cons {0 ghost : Nat} (x : Nat) (xs : L)\n" ++
  "def len : L → Nat\n  | .nil => 0\n  | .cons x xs => len xs + 1\n" ++
  "inductive Tagged where\n  | mk (0 ghost : Nat) (val : Nat)\ndef Tagged.get : Tagged → Nat\n  | .mk _ v => v\n" ++
  "structure S where\n  0 ghost : Nat\n  val : Nat\nstructure S1 where\n  0 ghost : Nat\n" ++
  "def e1 : Nat := Tagged.get (Tagged.mk (loop ()) 7)\ndef e2 : Nat := (S.mk (loop ()) 8).val\n" ++
  "def e3 : Nat := match S1.mk (loop ()) with\n  | _ => 9\n" ++
  "def e4 : Nat := len (L.cons (ghost := loop ()) 1 (L.cons (ghost := loop ()) 2 L.nil))\n"

/-- Build `main : IO _` with the C backend (and the `IO` library), run it, and hand its
output to `k`. -/
def ioRunWith (src : String) (k : String → IO Unit) (args : Array String := #[]) (llvm : Bool := false) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let effLib ← IO.FS.readFile "lib/Eff.wiz"
  let stdLib ← IO.FS.readFile "lib/Std.wiz"
  let functorLib ← IO.FS.readFile "lib/Functor.wiz"
  let sysLib ← IO.FS.readFile "lib/Sys.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Eff" then some effLib
    else if m == "Std" then some stdLib else if m == "Sys" then some sysLib else if m == "Functor" then some functorLib else none
  let headers ← Build.preprocessHeaders (← toolchain) src
  let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule, cHeaders := (headers[·]?) }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal (← toolchain) s "main" dir llvm (timeout := some 120) (args := args) with
  | .ok v => k v
  | .error e =>
    let missing := ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1
    if missing then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)

/-- Build `main : IO _` with the C backend (and the `IO` library) and compare its output. -/
def ioRun (src : String) (expected : String) (args : Array String := #[]) (llvm : Bool := false) : IO Unit :=
  ioRunWith src (checkEq expected ·) args llvm

def ioFails (src : String) (fragment : String) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let effLib ← IO.FS.readFile "lib/Eff.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Eff" then some effLib else none
  let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

/-- (9f) Elaborate `main.wiz` in a fresh directory holding `files` (modules under it are
importable), resolving `link_c` files as `wiz` does, relative to each file. -/
def elabTree (files : List (String × String)) : IO (CommandState ZeroOneMany × String × System.FilePath) := do
  let dir ← IO.FS.createTempDir
  for (p, text) in files do
    let f := dir / p
    if let some d := f.parent then IO.FS.createDirAll d
    IO.FS.writeFile f text
  let src ← IO.FS.readFile (dir / "main.wiz")
  let mods ← Module.loadClosure ["lib", dir] src
  let sources ← Module.cSourceTable dir src mods
  let s := runFrontend (R := ZeroOneMany) src
    { loader := fun m => (mods[m]?).map (·.2), cSources := some (Module.cSourceResolver sources) }
  pure (s, src, dir)

/-- `elabTree`, then build and run `main` (through C, or LLVM) and compare its output. -/
def linkRun (files : List (String × String)) (expected : String) (llvm : Bool := false) : IO Unit := do
  let (s, src, dir) ← elabTree files
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  match ← Build.runGlobal (← toolchain) s "main" dir llvm (timeout := some 120) with
  | .ok v => checkEq expected v
  | .error e =>
    let missing := ["gmp.h", "llc:"].any fun m => (e.splitOn m).length > 1
    if missing then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)

/-- A program that links a C file (with a static helper and a header the FFI can't bind)
and the maths library. -/
def linkFiles : List (String × String) :=
  [("main.wiz", "import IO\nlink_c \"c/twice.c\"\nlink_lib \"m\"\n" ++
      "extern \"twice\" twice : Nat → Nat\nextern \"root_of\" rootOf : Nat → IO Nat\n" ++
      "def main : IO Unit := do\n  IO.println (Nat.toString (twice 21));\n  r ← rootOf 1764;\n  IO.println (Nat.toString r)\n"),
   ("c/twice.c", "#include <stdint.h>\n#include <math.h>\nstruct box { uint64_t v; };\n" ++
      "static uint64_t unbox(struct box *b) { return b->v; }\n" ++
      "uint64_t twice(uint64_t n) { struct box b = { 2 * n }; return unbox(&b); }\n" ++
      "uint64_t root_of(uint64_t n) { volatile double d = (double)n; return (uint64_t)sqrt(d); }\n")]

def ffiGroup : Group where
  name := "ffi"
  exercise := "Stage 9a"
  cases := [
    { name := "IO actions run in order", run := fun _ =>
        ioRun "import IO\ndef main : IO Unit := do\n  IO.println \"one\";\n  IO.println \"two\"" "one\ntwo\n" },
    { name := "the world is linear: it can't be duplicated", run := fun _ =>
        ioFails "import IO\ndef bad (x : IO Unit) : IO Unit := fun w =>\n  let 1 (a, w') := x w; x w" "quantity 1" },
    { name := "linear sequencing: IO.bind, IO.then1 and do1 take an action and a continuation that use a linear value (L6)", run := fun _ => do
        ioFails ("import IO\naxiom Tok : Type\naxiom Tok.close : (1 t : Tok) → IO Unit\n" ++
          "def seqs (1 t : Tok) : IO Nat := do1\n  IO.println \"closing\";\n  Tok.close t;\n  IO.pure 3\n" ++
          "def seq2 (1 t : Tok) : IO Nat := IO.then1 (Tok.close t) (IO.pure 3)\n" ++
          "def seq3 (1 t : Tok) : IO Nat := IO.bind (IO.println \"x\") (fun _ => IO.bind (Tok.close t) (fun _ => IO.pure 3))\n" ++
          "def bad (1 t : Tok) : IO Nat := do\n  IO.println \"closing\";\n  Tok.close t;\n  IO.pure 3")
          "kernel rejected bad: variable t declared with quantity 1 but used ω"
        ioRun ("import IO\ndef main : IO Unit := do1\n  IO.println \"one\";\n  n ← IO.pure 2;\n  let m := n + n;\n  IO.println (Nat.toString m)") "one\n4\n" },
    { name := "... and a linear value is still used exactly once", run := fun _ =>
        ioFails ("import IO\naxiom Tok : Type\naxiom Tok.close : (1 t : Tok) → IO Unit\n" ++ "def bad (1 t : Tok) : IO Unit := do1\n  Tok.close t;\n  Tok.close t")
          "quantity 1 but used ω" },
    { name := "an action's result is split, not projected: (x w).1 would drop the world (R1)", run := fun _ => do
        ioFails ("import IO\ndef peek {A : Type} (1 x : IO A) (1 w : World) : A := (x w).1") "cannot project (x w).1"
        ioFails ("import IO\ndef peek {A : Type} (1 x : IO A) (1 w : World) : A := (x w).1") "which has quantity 1; take the pair apart with `let 1 (x, y) := x w; …`"
        ioFails ("import IO\ndef keep {A : Type} (1 x : IO A) (1 w : World) : World := (x w).2") "a projection needs an unrestricted pair"
        ioRun ("import IO\ndef twice (1 x : IO Nat) : IO Nat := fun w => let 1 (a, w') := x w; (a + a, w')\n" ++
          "def main : IO Unit := do\n  n ← twice (IO.pure 4);\n  IO.println (Nat.toString n)") "8\n" },
    { name := "... and compiled code never evaluates a 0 position (a let at 0, a 0 field, a split at 0, a 0 argument)", run := fun _ =>
        ioRun ("import IO\npartial def loop (u : Unit) : Nat × Nat := loop u\n" ++
          "def a : Nat := let 0 x : Nat := (loop ()).1; 1\ndef b : (0 x : Nat) × Nat := ((loop ()).1, 2)\n" ++
          "def c : Nat := let 0 (x, y) := loop (); 3\ndef d (f : (0 x : Nat) → Nat) : Nat := f (loop ()).1\n" ++
          "def main : IO Unit := IO.println (Nat.toString (a + b.2 + c + d (fun _ => 4)))") "10\n" },
    -- erasure used to bind `let s := <scrutinee>` for every split, so the action below ran
    -- (its usage of `w` is multiplied by 0, so the kernel accepted the second use of `w`)
    { name := "... nor performs an effect in the scrutinee of a split at 0 (C and LLVM)", run := fun _ => do
        let src := "import IO\ndef main : IO Unit := fun w =>\n  let 0 (a, w0) := IO.println \"ghost\" w;\n  IO.println \"real\" w"
        ioRun src "real\n"
        ioRun src "real\n" (llvm := true)
        let loop := "import IO\npartial def loop (u : Unit) : Nat × Nat := loop u\n" ++
          "def c : Nat := let 0 (x, y) := loop (); 3\ndef main : IO Unit := IO.println (Nat.toString c)"
        ioRun loop "3\n" (llvm := true) },
    { name := "... nor a constructor field at 0, a 0 field of a structure, a 0 argument of an extern (C and LLVM)", run := fun _ => do
        let src := "import IO\n" ++ zeroFieldDecls ++
          "extern \"strlen\" (header := \"string.h\") slen : (0 ghost : Nat) → String → Nat\n" ++
          "def e5 : Nat := slen (loop ()) \"abc\"\n" ++
          "def main : IO Unit := IO.println (Nat.toString (e1 + e2 + e3 + e4 + e5))"
        ioRun src "29\n"
        ioRun src "29\n" (llvm := true) },
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
        ioFails "import IO\nextern \"f\" f : ((Nat → Nat) → Nat) → Nat" "foreign function" },
    { name := "link_c: a C file and a library linked with the program (C backend)", run := fun _ =>
        linkRun linkFiles "42\n42\n" },
    { name := "link_c: the same with the LLVM backend", run := fun _ =>
        linkRun linkFiles "42\n42\n" (llvm := true) },
    { name := "link_c: a module's file is relative to the module", run := fun _ =>
        linkRun [("main.wiz", "import IO\nimport Lib.Glue\ndef main : IO Unit := IO.println (Nat.toString (three 0))\n"),
                 ("Lib/Glue.wiz", "import Prelude\nlink_c \"glue.c\"\nextern \"three\" three : Nat → Nat\n"),
                 ("Lib/glue.c", "#include <stdint.h>\nuint64_t three(uint64_t n) { return n + 3; }\n")] "3\n" },
    { name := "link_c: a missing file is an error at the command", run := fun _ => do
        let (s, src, _) ← elabTree [("main.wiz", "import IO\nlink_c \"nowhere.c\"\ndef main : IO Unit := IO.println \"x\"\n")]
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
        checkEq #["2:8: error: link_c: no file nowhere.c (paths are relative to the .wiz file)"] errs
        let (s, src, _) ← elabTree [("main.wiz", "import Prelude\nlink_lib \"-lm\"\n")]
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
        checkEq 1 errs.size },
    { name := "link_c: a file is linked once, however often it is named", run := fun _ => do
        let (s, _, _) ← elabTree [("main.wiz", "import Prelude\nlink_c \"a.c\"\nlink_c \"./a.c\"\nlink_lib \"m\"\nlink_lib \"m\"\n"), ("a.c", "")]
        checkEq 1 s.linkC.size
        checkEq #["m"] s.linkLibs }
  ]

/-- A `Sys` program, on the C backend and on the LLVM backend: `body` is the lines of an
`EIO` do block. -/
def sysRun (body : List String) (expected : String) (defs : String := "") : IO Unit := do
  let src := "import Sys\n" ++ defs ++ "def main : IO Unit := EIO.toIO (do\n" ++
    ";\n".intercalate (body.map ("  " ++ ·)) ++ ")"
  ioRun src expected
  ioRun src expected (llvm := true)

def sysShow : String :=
  "def showList : List String → String\n  | .nil => \"\"\n  | .cons x xs => String.append x (String.append \";\" (showList xs))\n" ++
  "def say (s : String) : EIO Unit := EIO.lift (IO.println s)\n" ++
  "def yesNo : Bool → String\n  | .true => \"yes\"\n  | .false => \"no\"\n" ++
  "def orUnset : Option String → String\n  | .some s => s\n  | .none => \"(unset)\"\n"

def sysGroup : Group where
  name := "sys"
  exercise := "Stage 9h"
  cases := [
    { name := "spawn echo and collect its output", run := fun _ =>
        sysRun ["o ← Process.output \"echo\" (.cons \"hello\" (.cons \"world\" .nil)) \"\"",
          "EIO.lift (IO.print o.stdout)", "say (ExitStatus.toString o.status)",
          "say (yesNo (ExitStatus.success o.status))"]
          "hello world\nexit code 0\nyes\n" sysShow },
    { name := "a pipe through cat, and stderr apart", run := fun _ =>
        sysRun ["o ← Process.output \"cat\" .nil \"piped through cat\\nline two\\n\"", "EIO.lift (IO.print o.stdout)",
          "e ← Process.output \"sh\" (.cons \"-c\" (.cons \"echo out; echo err >&2; exit 3\" .nil)) \"\"",
          "say (String.append \"stdout: \" e.stdout)", "say (String.append \"stderr: \" e.stderr)",
          "say (ExitStatus.toString e.status)"]
          "piped through cat\nline two\nstdout: out\n\nstderr: err\n\nexit code 3\n" sysShow },
    { name := "communicate doesn't deadlock on big output", run := fun _ =>
        -- 200 KB on stdout and 100 KB on stderr: more than a pipe buffer each
        sysRun ["o ← Process.output \"sh\" (.cons \"-c\" (.cons \"yes abcdefghi | head -c 200000; yes x | head -c 100000 >&2\" .nil)) \"\"",
          "say (Nat.toString (strLen o.stdout))", "say (Nat.toString (strLen o.stderr))"]
          "200000\n100000\n" (sysShow ++ "def strLen : String → Nat\n  | .mk cs => List.length cs\n") },
    { name := "a child, step by step", run := fun _ =>
        sysRun ["c ← Process.spawn \"cat\" .nil .piped .piped .inherit", "Child.write c \"one\\n\"",
          "Child.write c \"two\\n\"", "Child.closeStdin c", "out ← Child.readStdout c", "EIO.lift (IO.print out)",
          "st ← Child.wait c", "say (ExitStatus.toString st)",
          "k ← Process.spawn \"sleep\" (.cons \"10\" .nil) .null .null .null", "Child.kill k 9",
          "ks ← Child.wait k", "say (ExitStatus.toString ks)",
          "r ← Process.run \"true\" .nil", "say (ExitStatus.toString r)"]
          "one\ntwo\nexit code 0\nsignal 9\nexit code 0\n" sysShow },
    { name := "spawning a missing program is an error", run := fun _ =>
        sysRun ["r ← EIO.lift (Process.spawn \"wiz-no-such-program\" .nil .null .null .null)",
          "say (match r with | .ok c => \"spawned\" | .error e => e)"]
          "wiz-no-such-program: No such file or directory\n" sysShow },
    { name := "environment variables round-trip", run := fun _ =>
        sysRun ["Env.set \"WIZ_SYS_TEST\" \"v1\"", "a ← EIO.lift (Env.get \"WIZ_SYS_TEST\")", "say (orUnset a)",
          "Env.set \"WIZ_SYS_TEST\" \"v2 = λ\"", "b ← EIO.lift (Env.get \"WIZ_SYS_TEST\")", "say (orUnset b)",
          "all ← EIO.lift Env.list", "say (orUnset (lookup all))",
          "o ← Process.output \"sh\" (.cons \"-c\" (.cons \"echo $WIZ_SYS_TEST\" .nil)) \"\"", "EIO.lift (IO.print o.stdout)",
          "Env.unset \"WIZ_SYS_TEST\"", "c ← EIO.lift (Env.get \"WIZ_SYS_TEST\")", "say (orUnset c)",
          "r ← EIO.lift (Env.set \"A=B\" \"x\")", "say (match r with | .ok u => \"set\" | .error e => e)"]
          "v1\nv2 = λ\nv2 = λ\nv2 = λ\n(unset)\nsetenv A=B: Invalid argument\n"
          (sysShow ++ "def chEq : List Char → List Char → Bool\n  | .nil, .nil => .true\n  | .cons a xs, .cons b ys => Bool.and (Nat.beq (Char.code a) (Char.code b)) (chEq xs ys)\n  | _, _ => .false\n" ++
            "def strEq : String → String → Bool\n  | .mk a, .mk b => chEq a b\n" ++ "def lookup : List (String × String) → Option String\n  | .nil => .none\n" ++
            "  | .cons (k, v) rest => match strEq k \"WIZ_SYS_TEST\" with\n    | .true => .some v\n    | .false => lookup rest\n") },
    { name := "a temporary directory: files, links, stat, listing, removal", run := fun _ =>
        sysRun ["d ← FS.createTempDir", "FS.createDir (Path.join d \"sub\")",
          "FS.writeFile (Path.join d \"a.txt\") \"alpha\\n\"", "FS.appendFile (Path.join d \"a.txt\") \"beta\\n\"",
          "FS.rename (Path.join d \"a.txt\") (Path.join d \"b.txt\")", "FS.symlink \"b.txt\" (Path.join d \"link\")",
          "FS.writeFile (Path.join (Path.join d \"sub\") \"deep\") \"x\"",
          "t ← FS.readLink (Path.join d \"link\")", "say t",
          "xs ← FS.listDir d", "say (showList xs)",
          "s ← FS.stat (Path.join d \"link\")", "say (Nat.toString s.size)",
          "l ← FS.linkStat (Path.join d \"link\")", "say (match l.kind with | .symlink => \"link\" | _ => \"not a link\")",
          "say (yesNo (Nat.lt 1600000000 s.mtime))",
          "txt ← FS.readFile (Path.join d \"link\")", "EIO.lift (IO.print txt)",
          "a ← EIO.lift (FS.isDir (Path.join d \"sub\"))", "b ← EIO.lift (FS.isFile (Path.join d \"sub\"))",
          "say (String.append (yesNo a) (yesNo b))",
          "r ← EIO.lift (FS.removeDir (Path.join d \"sub\"))", "say (match r with | .ok u => \"removed\" | .error e => \"not empty\")",
          "FS.setMode (Path.join d \"b.txt\") 384", "m ← FS.stat (Path.join d \"b.txt\")", "say (Nat.toString m.mode)",
          "FS.removeFile (Path.join d \"link\")", "ys ← FS.listDir d", "say (showList ys)",
          "FS.removeAll d", "e ← EIO.lift (FS.exists d)", "say (yesNo e)"]
          "b.txt\nb.txt;link;sub;\n11\nlink\nyes\nalpha\nbeta\nyesno\nnot empty\n384\nb.txt;sub;\nno\n" sysShow },
    { name := "the working directory", run := fun _ =>
        sysRun ["d ← FS.createTempDir", "FS.setCurrentDir d", "FS.writeFile \"here.txt\" \"hi\"",
          "c ← FS.currentDir", "x ← FS.readFile (Path.join c \"here.txt\")", "say x",
          "o ← Process.output \"ls\" .nil \"\"", "EIO.lift (IO.print o.stdout)",
          "FS.setCurrentDir \"/\"", "FS.removeAll d"]
          "hi\nhere.txt\n" sysShow },
    { name := "errors carry errno messages", run := fun _ =>
        sysRun ["r ← EIO.lift (FS.readFile \"/nonexistent/x\")", "say (match r with | .ok s => s | .error m => m)",
          "q ← EIO.lift (FS.listDir \"/nonexistent\")", "say (match q with | .ok s => \"listed\" | .error m => m)",
          "w ← EIO.lift (FS.createDir \"/\")", "say (match w with | .ok s => \"made\" | .error m => m)"]
          "/nonexistent/x: No such file or directory\n/nonexistent: No such file or directory\n/: File exists\n" sysShow },
    { name := "file handles and bytes", run := fun _ =>
        sysRun ["d ← FS.createTempDir", "let p := Path.join d \"f.txt\"",
          "f ← File.open p \"w\"", "File.write f \"first\\n\"", "File.write f \"second\\n\"", "File.close f",
          "g ← File.open p \"r\"", "a ← File.readLine g", "b ← File.readLine g", "c ← File.readLine g",
          "say (String.append (orUnset a) (String.append \",\" (String.append (orUnset b) (String.append \",\" (orUnset c)))))",
          "FS.writeBytes (Path.join d \"bin\") (Bytes.push (Bytes.push (Bytes.push Bytes.empty 0) 255) 7)",
          "bs ← FS.readBytes (Path.join d \"bin\")",
          "say (String.append (Nat.toString (Bytes.size bs)) (String.append \" \" (Nat.toString (Bytes.get bs 1))))",
          "o ← EIO.lift File.stdout", "File.write o \"to stdout\\n\"", "File.flush o",
          "FS.removeAll d"]
          "first,second,(unset)\n3 255\nto stdout\n" sysShow }
  ]

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
        IO.println "    (skipped: no toolchain)"
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
        IO.println "    (skipped: no toolchain)"
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

/-- (9i) A header of our own: structs by value (nested, with a string and a byte array),
an opaque pointer type with a constructor and a finalizer, and a buffer function. -/
def pointHeader : String := "#ifndef WIZ_POINT_H
#define WIZ_POINT_H
#include <stdio.h>
#include <stddef.h>
struct point { double x; double y; };
typedef struct { struct point lo; struct point hi; const char *name; unsigned char tag[4]; int flags; } box;
struct packed { unsigned a : 3; unsigned b : 5; };
static inline struct point point_add(struct point a, struct point b) { struct point r = { a.x + b.x, a.y + b.y }; return r; }
static inline double box_area(box b) { return (b.hi.x - b.lo.x) * (b.hi.y - b.lo.y); }
static inline box box_make(struct point lo, struct point hi) {
  box b; b.lo = lo; b.hi = hi; b.name = \"made in C\"; b.tag[0] = 'w'; b.tag[1] = 'i'; b.tag[2] = 'z'; b.tag[3] = '!'; b.flags = 7; return b;
}
static inline size_t box_name_len(box b) { size_t n = 0; while (b.name[n]) n++; return n + b.tag[0]; }
static inline int packed_sum(struct packed p) { return p.a + p.b; }
typedef struct counter counter;
struct counter { int n; };
static struct counter wiz_the_counter;
static inline counter *counter_new(void) { wiz_the_counter.n = 0; return &wiz_the_counter; }
static inline int counter_bump(counter *c) { return ++c->n; }
static inline void counter_free(counter *c) { printf(\"freed at %d\\n\", c->n); fflush(stdout); }
static inline size_t sum_bytes(const void *buf, size_t n) { const unsigned char *p = buf; size_t s = 0; for (size_t i = 0; i < n; i++) s += p[i]; return s; }
#endif
"

/-- Write `pointHeader` to a fresh directory; its absolute path. -/
def writePointHeader : IO String := do
  let dir ← IO.FS.createTempDir
  let h := dir / "wiz_point.h"
  IO.FS.writeFile h pointHeader
  pure h.toString

/-- The errors of a program that imports headers (preprocessed like `ioRun` does). -/
def ffiErrors (src : String) : IO (Array String) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else none
  let headers ← Build.preprocessHeaders (← toolchain) src
  let s := runFrontend (R := ZeroOneMany) src { loader, cHeaders := (headers[·]?) }
  pure ((s.messages.filter (·.severity == .error)).map fun m => m.render src)

def divSrc : String :=
  "import IO\nc_struct \"div_t\" (header := \"stdlib.h\") DivT where\n  quot : Nat\n  rem : Nat\n" ++
  "extern \"div\" (header := \"stdlib.h\") cdiv : Nat → Nat → DivT\n" ++
  "def main : IO Unit := do\n  let d := cdiv 17 5;\n  IO.println (Nat.toString d.quot);\n  IO.println (Nat.toString d.rem)"

def ffiStructGroup : Group where
  name := "ffi-structs"
  exercise := "Stage 9i"
  cases := [
    { name := "a C struct by value: div_t from div()", run := fun _ => ioRun divSrc "3\n2\n" },
    { name := "a C struct by value, LLVM backend", run := fun _ => ioRun divSrc "3\n2\n" (llvm := true) },
    { name := "a struct argument: inet_ntoa (struct in_addr)", run := fun _ =>
        ioRun ("import IO\nc_struct \"struct in_addr\" (header := \"arpa/inet.h\") InAddr where\n  s_addr : Nat\n" ++
          "extern \"inet_ntoa\" (header := \"arpa/inet.h\") ntoa : InAddr → String\n" ++
          "def main : IO Unit := IO.println (ntoa (InAddr.mk 16777343))") "127.0.0.1\n" },
    { name := "struct timespec from clock_gettime, through glue", run := fun _ =>
        ioRun ("import IO\nimport_c \"time.h\"\nc_struct \"struct timespec\" (header := \"time.h\") Timespec where\n  tv_sec : Nat\n  tv_nsec : Nat\n" ++
          "glue monotonic : IO Timespec := \"struct timespec t; clock_gettime(1, &t); return t;\"\n" ++
          "def showB : Bool → String\n  | .true => \"true\"\n  | .false => \"false\"\nglue later (t : Timespec) : Timespec := \"t.tv_sec = t.tv_sec + 1; return t;\"\n" ++
          "def main : IO Unit := do\n  t ← monotonic;\n  let u := later t;\n" ++
          "  IO.println (showB (Nat.lt t.tv_nsec 1000000000));\n" ++
          "  IO.println (Nat.toString (u.tv_sec - t.tv_sec))") "true\n1\n" },
    { name := "a struct defined in Wiz (generated C definition)", run := fun _ =>
        ioRun ("import IO\nc_struct \"struct pair\" Pair where\n  a : Nat\n  b : Float64\n  ok : Bool\n" ++
          "def showB : Bool → String\n  | .true => \"true\"\n  | .false => \"false\"\nglue bump (p : Pair) : Pair := \"p.a = p.a + 1; p.b = p.b * 2; p.ok = !p.ok; return p;\"\n" ++
          "def main : IO Unit := do\n  let p := bump (Pair.mk 41 (Float64.ofNat 3) .false);\n" ++
          "  IO.println (Nat.toString p.a);\n  IO.println (Float64.toString p.b);\n" ++
          "  IO.println (showB p.ok)") "42\n6\ntrue\n" },
    { name := "import_c binds functions on structs: div, ldiv", run := fun _ =>
        ioRun ("import IO\nimport_c \"stdlib.h\" (pure)\n" ++
          "def main : IO Unit := do\n  let d := C.div 100 7;\n  IO.println (Nat.toString d.quot);\n" ++
          "  IO.println (Nat.toString (C.ldiv 100 7).rem)") "14\n2\n" },
    { name := "a header's structs: nested, strings, byte arrays, pointers, buffers", run := fun _ => do
        let h ← writePointHeader
        ioRun (s!"import IO\nimport_c \"{h}\"\n" ++
          "def pt (x y : Nat) : C.struct_point := C.struct_point.mk (Float64.ofNat x) (Float64.ofNat y)\n" ++
          "def main : IO Unit := do\n  p ← C.point_add (pt 1 2) (pt 10 20);\n" ++
          "  IO.println (Float64.toString p.x);\n  IO.println (Float64.toString p.y);\n" ++
          "  b ← C.box_make (pt 0 0) (pt 3 4);\n  a ← C.box_area b;\n  IO.println (Float64.toString a);\n" ++
          "  IO.println b.name;\n  IO.println (Bytes.toString b.tag);\n  IO.println (Nat.toString b.flags);\n" ++
          "  n ← C.box_name_len (C.box.mk (pt 0 0) (pt 1 1) \"four\" (Bytes.ofString \"A\") 0);\n  IO.println (Nat.toString n);\n" ++
          "  c ← C.counter_new;\n  k ← C.counter_bump c;\n  k ← C.counter_bump c;\n  IO.println (Nat.toString k);\n" ++
          "  s ← C.sum_bytes (Bytes.ofString \"AB\");\n  IO.println (Nat.toString s)")
          "11\n22\n12\nmade in C\nwiz!\n7\n69\n2\n131\n" },
    { name := "foreign_type (c := …) takes over a header's pointer type, with a finalizer", run := fun _ => do
        let h ← writePointHeader
        ioRun (s!"import IO\nforeign_type Counter (finalizer := \"counter_free\") (c := \"counter\")\nimport_c \"{h}\"\n" ++
          "def main : IO Unit := do\n  c ← C.counter_new;\n  k ← C.counter_bump c;\n  k ← C.counter_bump c;\n  k ← C.counter_bump c;\n" ++
          "  IO.println (Nat.toString k)") "freed at 3\n3\n" },
    { name := "c_struct takes over a header's struct (only the fields it names)", run := fun _ => do
        let h ← writePointHeader
        ioRun (s!"import IO\nc_struct \"box\" (header := \"{h}\") Box where\n  name : String\n  flags : Nat\nimport_c \"{h}\"\n" ++
          "def main : IO Unit := do\n  b ← C.box_make (C.struct_point.mk (Float64.ofNat 0) (Float64.ofNat 0)) (C.struct_point.mk (Float64.ofNat 1) (Float64.ofNat 1));\n" ++
          "  IO.println b.name;\n  IO.println (Nat.toString b.flags)") "made in C\n7\n" },
    { name := "opt-outs: no_auto and skip", run := fun _ => do
        let h ← writePointHeader
        let errs ← ffiErrors s!"import IO\nimport_c \"{h}\" (no_auto)\n#check C.point_add"
        check (errs.size == 1) s!"{errs}"
        let errs ← ffiErrors s!"import IO\nimport_c \"{h}\" (skip := \"counter box_area\")\n#check C.counter_new\n#check C.box_area\n#check C.point_add"
        check (errs.size == 2) s!"{errs}"
        -- a struct with bit fields isn't mapped
        let errs ← ffiErrors s!"import IO\nimport_c \"{h}\"\n#check C.packed_sum"
        check (errs.size == 1) s!"{errs}" },
    { name := "glue: struct addresses only for struct pointer parameters", run := fun _ => do
        let errs ← ffiErrors ("import IO\nimport_c \"time.h\"\nc_struct \"struct timespec\" (header := \"time.h\") Timespec where\n  tv_sec : Nat\n  tv_nsec : Nat\n" ++
          "glue bad (n : Nat) : Nat := \"return clock_gettime(1, &n);\"")
        check (errs.size == 1 && (errs[0]!.splitOn "struct variable").length > 1) s!"{errs}"
        let errs ← ffiErrors ("import IO\nimport_c \"string.h\"\nc_struct \"struct timespec\" (header := \"time.h\") Timespec where\n  tv_sec : Nat\n  tv_nsec : Nat\n" ++
          "glue bad (n : Nat) : Nat := \"struct timespec t; return strlen(&t);\"")
        check (errs.size == 1 && (errs[0]!.splitOn "address").length > 1) s!"{errs}"
        let errs ← ffiErrors ("import IO\nc_struct \"struct named\" Named where\n  s : String\n" ++
          "glue bad (n : Nat) : Named := \"struct named t; return t;\"")
        check (errs.size == 1 && (errs[0]!.splitOn "initialised").length > 1) s!"{errs}" },
    { name := "c_struct fields are checked", run := fun _ =>
        ioFails "import IO\nc_struct Bad where\n  f : Nat → Nat" "c_struct field f" },
    { name := "the C subset parser reads struct definitions", run := fun _ => do
        let (_, sts) := FFI.parseHeaderFull "struct a { int x; double y[3]; char n[8]; };\ntypedef struct { struct a in; const char *s; } b_t;\ntypedef struct a a_t;\nstruct c { unsigned f : 1; };\nstruct d;"
        checkEq "[struct a, b_t, struct c]" (toString (sts.toList.map (·.spelling)))
        checkEq "[a_t]" (toString (sts[0]!.aliases))
        checkEq "true" (toString (sts[2]!.fields.isNone))
        checkEq "true" (toString ((sts[0]!.fields.getD []).map (·.2) == [.int "int", .array (.float "double") (some 3), .array (.int "char") (some 8)])) }
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
     pi (sortParam "u") (pi (sortParam "v") (pi (var 1) (pi (var 1) (var 3))))),
   -- (W1, `wiz-notes/kernel-lint.md`) a proposition that is a theorem at level 0 and false
   -- at level 1, and a case that is stuck on its scrutinee with `A` in its environment
   ("dLv", ["u"], some (pi (sortParam "u") (pi (var 0) (pi (var 1) (pi (pi (var 2) prop)
     (pi (app (var 0) (var 2)) (app (var 1) (var 2))))))), prop),
   ("caseF", [], some (lam (lam (ecase prop (var 0) [var 1]))), pi prop (pi (enum 1) prop))]

/-- (W1) `fun x p => p : (x : Enum 1) → caseF dLv.{l} x → caseF dLv.{l'} x`: the two types
are stuck cases with the same motive and branch terms, whose environments hold `dLv` at
the two levels. Well typed only when `l = l'`. -/
def levelInEnv (l l' : Nat) : MTm :=
  ann (lam (lam (var 0))) (pi (enum 1)
    (pi (app (app (const "caseF") (const "dLv" [l])) (var 0)) (app (app (const "caseF") (const "dLv" [l'])) (var 1))))

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

/-- (R1) Projections are available only on unrestricted pairs, and positions at 0 are
erased positions: each term with whether the kernels accept it. -/
def projRule : List (MTm × Bool) := [
   -- (R1) projections need an unrestricted pair, whatever the fields' quantities:
   -- a linear pair is rejected (the last one has a bare second component: the audit's
   -- probe), an unrestricted one and a closed one are accepted
   (ann (lam (snd (var 0))) (piq .one (sigmaq .one (univ 0) (univ 0)) (univ 0)), false),
   (ann (lam (snd (var 0))) (piq .one (sigmaq .many (univ 0) (univ 0)) (univ 0)), false),
   (ann (lam (snd (var 0))) (piq .many (sigmaq .one (univ 0) (univ 0)) (univ 0)), true),
   (snd (ann (pair (enum 2) (enum 2)) (sigmaq .one (univ 0) (univ 0))), true),
   (ann (lam (fst (var 0))) (piq .one (sigma (univ 0) (sigmaq .one (univ 0) (univ 0))) (univ 0)), false),
   (ann (lam (fst (var 0))) (piq .many (sigma (univ 0) (sigmaq .one (univ 0) (univ 0))) (univ 0)), true),
   (ann (lam (fst (var 0))) (piq .one (sigma (univ 0) (sigma (univ 0) (univ 0))) (univ 0)), false),
   (ann (lam (fst (var 0))) (piq .one (sigmaq .one (univ 0) (univ 0)) (univ 0)), false),
   (ann (lam (fst (snd (var 0)))) (piq .one (sigma (univ 0) (sigma (univ 0) (univ 0))) (univ 0)), false),
   (ann (lam (fst (snd (var 0)))) (piq .many (sigma (univ 0) (sigma (univ 0) (univ 0))) (univ 0)), true),
   -- a projection of an expression uses the expression ω times: `(f x).1` with `x` at 1
   -- is rejected, with `x` at ω accepted
   (ann (lam (lam (fst (app (var 1) (var 0))))) (pi (piq .one (univ 0) (sigma (univ 0) (univ 0))) (piq .one (univ 0) (univ 0))), false),
   (ann (lam (lam (fst (app (var 1) (var 0))))) (pi (piq .one (univ 0) (sigma (univ 0) (univ 0))) (piq .many (univ 0) (univ 0))), true),
   -- positions at 0 are erased positions, where a projection is free: the value of a
   -- `let` at 0, the first part of a pair at a 0 field, an argument to a 0 binder
   -- (accepted: the linear pair is then used once, by the body)
   (ann (lam (letq .zero (univ 0) (fst (var 0)) (var 1))) (piq .one (sigma (univ 0) (univ 0)) (sigma (univ 0) (univ 0))), true),
   (ann (lam (pair (fst (var 0)) (var 0))) (piq .one (sigma (univ 0) (univ 0)) (sigmaq .zero (univ 0) (sigma (univ 0) (univ 0)))), true),
   (ann (lam (lam (app (app (var 1) (fst (var 0))) (var 0))))
     (pi (piq .zero (univ 0) (piq .one (sigma (univ 0) (univ 0)) (univ 0))) (piq .one (sigma (univ 0) (univ 0)) (univ 0))), true),
   -- an erased field can be read there (accepted), and not in a `let` at 1 or ω (rejected)
   (ann (lam (letq .zero (univ 0) (fst (var 0)) (snd (var 1)))) (piq .many (sigmaq .zero (univ 0) (univ 0)) (univ 0)), true),
   (ann (lam (letq .one (univ 0) (fst (var 0)) (var 0))) (piq .many (sigmaq .zero (univ 0) (univ 0)) (univ 0)), false),
   -- what a `let` at 0 binds can't be used (rejected), nor can the linear pair go unused
   (ann (lam (letq .zero (univ 0) (fst (var 0)) (var 0))) (piq .many (sigma (univ 0) (univ 0)) (univ 0)), false),
   (ann (lam (letq .zero (univ 0) (fst (var 0)) (enum 2))) (piq .one (sigma (univ 0) (univ 0)) (univ 0)), false)]

/-- The eliminators bind what they take apart at ω, so the scrutinee (the seed) counts ω
times: at 1 it is rejected (the method below ignores it: a linear value would be
dropped), at ω accepted. `ind`, `scase`, `sfix`, `coit`, `scofix`. -/
def elimRule : List (MTm × Bool) :=
  let step := lams 2 (pair (var 0) (pair (ecase (enum 2) (var 0) [tag 2 1, tag 2 0]) (pair star star)))
  let zerosF := lams 4 (cocon (pair (tag 2 0) (pair (app (app (var 2) (var 1)) (var 0)) (pair star star))))
  [ZeroOneMany.one, ZeroOneMany.many].flatMap fun q =>
    let ok := q == ZeroOneMany.many
    [(ann (lam (ind 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (tag 2 0)) star (var 0))) (piq q natTy (enum 2)), ok),
     (ann (lam (scase 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (tag 2 0)) szInf star (var 0))) (piq q natTy (enum 2)), ok),
     (ann (lam (sfix 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 4 (tag 2 0)) szInf star (var 0))) (piq q natTy (enum 2)), ok),
     (ann (lam (coit 0 (unit 0) streamD (lam (enum 2)) step star (var 0))) (piq q (enum 2) streamTy), ok),
     (ann (lam (scofix 0 (unit 0) streamD (lam (unit 0)) zerosF szInf star (var 0))) (piq q (unit 0) streamTy), ok)]

/-- Usage checking at the edges (kernel-lint's findings in Kernel.wiz, whose usage lists
drop trailing zeros): a variable that is never used has usage 0, which a binder at 1 does
not allow; and branches that disagree about a linear variable join to ω, also when one of
them uses no variable at all. -/
def usageRule : List (MTm × Bool) :=
  let caseOn (q : ZeroOneMany) (bs : List MTm) :=
    ann (lam (lam (ecase (enum 2) (var 1) bs))) (pi (enum 2) (piq q (enum 2) (enum 2)))
  [(ann (lam star) (piq .one (unit 0) (unit 0)), false),
   (ann (lam star) (piq .many (unit 0) (unit 0)), true),
   (ann (lam star) (piq .zero (unit 0) (unit 0)), true),
   (ann (lam (lam (var 1))) (pi (enum 2) (piq .one (enum 2) (enum 2))), false),
   (letq .one (enum 2) (tag 2 0) (tag 2 1), false),
   (letq .many (enum 2) (tag 2 0) (tag 2 1), true),
   (caseOn .one [var 0, tag 2 0], false),
   (caseOn .one [tag 2 0, var 0], false),
   (caseOn .one [var 0, var 0], true),
   (caseOn .one [tag 2 0, tag 2 1], false),
   (caseOn .many [var 0, tag 2 0], true)]

/-- The five eliminators that name the index type `I`, at level `l`, on the smallest
descriptions (`ret i`, and `rec i (ret i)` for `ν`), in this order: `ind`, `sfix`,
`scase`, `coit`, `scofix`. All five are well typed when `I` is in `Sort (l+1)`. -/
def elimsAt (l : Nat) (I i : MTm) : List MTm :=
  let uD := dret i
  let sD := drec i (dret i)
  let x := con (pair star star)
  let P := lams 2 (enum 2)
  [ind l I uD 1 P (lams 3 (tag 2 0)) i x,
   sfix l I uD 1 P (lams 4 (tag 2 0)) szInf i x,
   scase l I uD 1 P (lams 3 (tag 2 0)) szInf i x,
   coit l I sD (lam (unit l)) (lams 2 (pair star (pair star star))) i star,
   scofix l I sD (lam (unit l)) (lams 4 (cocon (pair (app (app (var 2) (var 1)) (var 0)) (pair star star)))) szInf i star]

/-- Audit F3 (fixed): an eliminator checks that its index type is in `Sort (l+1)`, as the
type formers `μ`/`ν` do. The eliminators check the scrutinee against `μ.{l} I D i` (or
return `ν.{l} I D i`) without the type former, so they used to accept an index type at
any level: a term could have a type that is not a type. In order: the five eliminators
with the index type one level too high (rejected), one level too low (rejected), then at
level 0 and at level 1 (accepted); last, the result of an ill-levelled `ind` used in an
equation, and the type of an ill-levelled `coit` observed (both rejected). -/
def elimLevels : List MTm :=
  elimsAt 0 (unit 1) star ++ elimsAt 1 (unit 0) star ++ elimsAt 0 (unit 0) star ++ elimsAt 1 (unit 1) star ++
  [ann star (eq (enum 2) (ind 0 (unit 1) (dret star) 1 (lams 2 (enum 2)) (lams 3 (tag 2 0)) star (con (pair star star))) (tag 2 0)),
   fst (out (coit 0 (unit 1) (drec star (dret star)) (lam (unit 0)) (lams 2 (pair star (pair star star))) star star))]

/-- `transp` is for types in `Type u`, like `eq` and `refl` (audit-2): its motive's type
`(0 b : A) → (0 _ : a = b) → Prop` and the type of its proof are equations at `A`, which
the `eq` rule rejects at a proposition. Rejected: `transp` at `True` and at an equation;
accepted: the same at `Unit` and at `Enum2`. -/
def transpProp : List MTm :=
  let e2 := eq (enum 2) (tag 2 0) (tag 2 0)
  [transp ptrue star (lams 2 ptrue) star star star,
   transp e2 star (lams 2 ptrue) star star star,
   transp (unit 0) star (lams 2 ptrue) star star star,
   transp (enum 2) (tag 2 0) (lams 2 ptrue) star (tag 2 0) (refl (enum 2) (tag 2 0))]

/-- Terms the differential test always checks (well-typed ones the generator rarely
builds whole), before the random ones. -/
def samples : List MTm :=
  propShapes ++ qtyApart ++ elimLevels ++ transpProp ++ sizeInf ++ sizeEq ++ sizeArgs ++ smallField ++ projRule.map (·.1) ++ elimRule.map (·.1) ++ usageRule.map (·.1) ++ [levelInEnv 0 0, levelInEnv 1 1, levelInEnv 0 1, levelInEnv 1 0,
   natTy, natZero, natSucc natZero, natSucc (natSucc natZero), ann natD (desc 0 (unit 0)),
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
  note "uses checker"
  if ← exe.pathExists then return .ok exe
  let start ← IO.monoMsNow
  IO.FS.createDirAll dir
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let stdLib ← IO.FS.readFile "lib/Std.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Std" then some stdLib else none
  let s := runFrontend (R := ZeroOneMany) prog { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render prog
  unless errs.isEmpty do return .error s!"unexpected errors:\n{"\n".intercalate errs.toList}"
  match Build.irProgram s "main" with
  | .error e => return .error e
  | .ok (decls, _) =>
    -- built under another name and renamed: tests may run at the same time
    let tmp := dir / s!"checker-{← IO.monoNanosNow}"
    match ← Build.compileC (← toolchain) (C.program decls true (Build.extraC s)) tmp with
    | .error e => return .error e
    | .ok () =>
      IO.FS.rename tmp exe
      note s!"built checker {showMs ((← IO.monoMsNow) - start)}"
      return .ok exe

/-- The self-hosted compiler (stage 21): the frontend and `Backend.wiz`, printing the C
program for `input.wiz` (the frontend's own output as comments). -/
def selfhostCompiler : IO (Except String System.FilePath) := do
  let src ← Selfhost.compilerFiles.mapM (fun (f : String) => IO.FS.readFile f)
  let prog := Selfhost.compilerSource src
  let stamp := toString (← (← IO.appPath).metadata).modified.sec
  let dir : System.FilePath := s!"/tmp/wiz-selfhost-{hash (prog ++ stamp)}"
  let exe := dir / "compiler"
  note "uses compiler"
  if ← exe.pathExists then return .ok exe
  let start ← IO.monoMsNow
  IO.FS.createDirAll dir
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let stdLib ← IO.FS.readFile "lib/Std.wiz"
  -- (the driver ends with `Process.exit` on a frontend error)
  let sysLib ← IO.FS.readFile "lib/Sys.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Std" then some stdLib
    else if m == "Sys" then some sysLib else none
  let s := runFrontend (R := ZeroOneMany) prog { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render prog
  unless errs.isEmpty do return .error s!"unexpected errors:\n{"\n".intercalate errs.toList}"
  match Build.irProgram s "main" with
  | .error e => return .error e
  | .ok (decls, _) =>
    let tmp := dir / s!"compiler-{← IO.monoNanosNow}"
    match ← Build.compileC (← toolchain) (C.program decls true (Build.extraC s)) tmp with
    | .error e => return .error e
    | .ok () =>
      IO.FS.rename tmp exe
      note s!"built compiler {showMs ((← IO.monoMsNow) - start)}"
      return .ok exe

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
    if (e.splitOn "gmp.h").length > 1 then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)
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
    let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
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
  "Nat : U0\nEmpty : U0\nBox : (x0 : U0) → U0\nunbox : (x0 : U0) → (x1 : (Box x0)) → x0\nT : U0\na : (Box T)\n" ++
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
          "leaf : Syntax\nkindOf : (x0 : Syntax) → String\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nargCount : (x0 : Bool) → (x1 : (SyntaxF x0)) → Nat\ncon((#1, (tt, tt)))\nCat : U0\nfind : (x0 : (List Cat)) → (x1 : String) → (Option Cat)\nm : (StrMap Nat)\n" },
    { name := "function fields and catch-alls on mutual types, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\nmutual\ninductive Tm where\n  | lit (n : Nat)\n  | app (f : Tm) (a : Tm)\n  | many (ts : Tms)\ninductive Tms where\n  | nil\n  | cons (t : Tm) (ts : Tms)\nend\ndef litOr : Tm → Tm\n  | .lit n => .lit (n + 1)\n  | t => t\n#reduce litOr (.lit 1)\n#reduce litOr (.many .nil)\nmutual\ninductive Val where\n  | vnat (n : Nat)\n  | vlazy (v : Unit → Val)\n  | vbox (b : Box)\ninductive Box where\n  | mk (v : Val)\nend\npartial def force : Val → Val\n  | .vlazy v => force (v ())\n  | v => v\ndef unwrap : Val → Val\n  | .vlazy v => v ()\n  | v => v\n#reduce unwrap (Val.vlazy (fun _ => Val.vnat 3))\ndef big (n : Nat) : Nat := Nat.max n 3\n#reduce Nat.beq (big 1) 3\n"
          "Tm : U0\nTms : U0\nlitOr : (x0 : Tm) → Tm\ncon((#0, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (refl(Enum2, #0), tt))))\ncon((#2, (con((#3, (refl(Enum2, #1), tt))), (refl(Enum2, #0), tt))))\nVal : U0\nBox : U0\nforce : (x0 : Val) → Val\nunwrap : (x0 : Val) → Val\ncon((#0, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (refl(Enum2, #0), tt))))\nbig : (x0 : Nat) → Nat\ncon((#1, (tt, tt)))\n" },
    { name := "recursion through function fields, reordered parameters, big numerals, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\nmutual\ninductive Val where\n  | vnat (n : Nat)\n  | vsuc (v : Val)\n  | vlazy (v : Unit → Val)\n  | vbox (b : Box)\ninductive Box where\n  | mk (v : Val)\nend\ndef whnf : Val → Val\n  | .vlazy v => whnf (v ())\n  | v => v\ndef depth : Val → Nat\n  | .vsuc v => depth v + 1\n  | .vlazy v => depth (v ())\n  | _ => 0\n#reduce Nat.beq (depth (whnf (Val.vlazy (fun _ => Val.vlazy (fun _ => Val.vnat 3))))) 0\n#reduce Nat.beq (depth (Val.vsuc (Val.vlazy (fun _ => Val.vsuc (Val.vnat 0))))) 2\ndef apps : Nat → List Nat → Nat\n  | f, .nil => f\n  | f, .cons a rest => apps (f + a) rest\n#reduce Nat.beq (apps 1 (List.cons 2 (List.cons 3 .nil))) 6\ndef big : Nat := 100000\n#check big\ndef bigger : Nat := 1000000000\n#reduce Nat.beq (Nat.sub 1000 999) 1\n"
          "Val : U0\nBox : U0\nwhnf : (x0 : Val) → Val\ndepth : (x0 : Val) → Nat\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\napps : (x0 : Nat) → (x1 : (List Nat)) → Nat\ncon((#1, (tt, tt)))\nbig : Nat\nNat\nbigger : Nat\ncon((#1, (tt, tt)))\n" },
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
          "error: a foreign function's arguments and result must be Nat, UInt64, Float64, String, Bool, Unit or a Wiz data type (the result may be in IO)\nT : U0\ng : (x0 : U0) → (x1 : x0) → (x2 : T) → (IO x0)\n" },
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

/-- A term language with identifiers, juxtaposition and `if … then … else`, run by macros
(13j); `decl` follows `declare_syntax_cat` (a keyword scope, or nothing). The file also
defines `then` and `else` as Wiz names. -/
def calcDsl (decl : String) : String := "import Prelude\ndeclare_syntax_cat calc_e" ++ decl ++ "
syntax (name := var) ident : calc_e
syntax (name := host) \"[\" term \"]\" : calc_e
syntax:lead (name := app) calc_e:max calc_e:max : calc_e
syntax:20 (name := ifE) \"if\" calc_e \"then\" calc_e:20 \"else\" calc_e:20 : calc_e
syntax (name := calc) \"run_calc\" calc_e \"done\" : term
macro_rules
  | `(term| run_calc [ $t ] done) => `(term| $t)
macro_rules
  | `(term| run_calc $f $a done) => `(term| (run_calc $f done) (run_calc $a done))
macro_rules
  | `(term| run_calc if $c then $a else $b done) => `(term| match run_calc $c done with | .true => run_calc $a done | .false => run_calc $b done)
def then : Nat := 1
def else (if : Nat) : Nat := Nat.succ if
def isZero : Nat → Bool
  | .zero => .true
  | .succ _ => .false
"

/-- (R1) A linear token, for the projection tests. -/
def r1Header : String := "import Prelude\naxiom Tok : Type\n"

def languageGroup : Group where
  name := "language"
  exercise := "Stage 13"
  cases := [
    { name := "linear transport: Eq.subst, Eq.substBack and Eq.cast take a linear value (L4)", run := fun _ =>
        okLib ("import Prelude\naxiom Tok : Nat → Type\naxiom Tok.close : (1 t : Tok 0) → Unit\n" ++
          "def closeAt (0 n : Nat) (0 e : n = 0) (1 t : Tok n) : Unit := Tok.close (Eq.subst Tok e t)\n" ++
          "def closeBack (0 n : Nat) (0 e : 0 = n) (1 t : Tok n) : Unit := Tok.close (Eq.substBack Tok e t)\n" ++
          "def closeCast (0 n : Nat) (0 e : Tok n = Tok 0) (1 t : Tok n) : Unit := Tok.close (Eq.cast e t)\n" ++
          "def listCast (0 A B : Type) (0 e : A = B) (v : List A) : List B := Eq.subst List e v\n") },
    { name := "... still used exactly once", run := fun _ =>
        failsLib ("import Prelude\naxiom Tok : Nat → Type\naxiom Tok.close : (1 t : Tok 0) → Unit\n" ++
          "def twice (0 n : Nat) (0 e : n = 0) (1 t : Tok n) : Unit × Unit := (Tok.close (Eq.subst Tok e t), Tok.close (Eq.subst Tok e t))")
          "quantity 1 but used ω" },
    { name := "... where a transport with an unrestricted argument can't carry a linear value", run := fun _ =>
        failsLib ("import Prelude\naxiom Tok : Nat → Type\naxiom Tok.close : (1 t : Tok 0) → Unit\n" ++
          "def substω (0 P : Nat → Type) {0 a b : Nat} (0 e : a = b) (pa : P a) : P b := cast (transp (fun b _ => P a = P b) (refl (P a)) e) pa\n" ++
          "def closeAt (0 n : Nat) (0 e : n = 0) (1 t : Tok n) : Unit := Tok.close (substω Tok e t)")
          "quantity 1 but used ω" },
    -- (R1) projections are available only on unrestricted pairs
    { name := "p.1 and p.2 on a linear pair are rejected, whatever the components (R1: the audit's probes)", run := fun _ => do
        let needs := "a projection needs an unrestricted pair"
        failsLib (r1Header ++ "def drop1 {A : Type} (1 p : A × Tok) : A := p.1") needs
        failsLib (r1Header ++ "def drop2 {A : Type} (1 p : (1 a : A) × Tok) : A := p.1") needs
        failsLib (r1Header ++ "def drop3 {A : Type} (1 p : (1 t : Tok) × A) : A := p.2") needs
        -- the error says what to write
        failsLib (r1Header ++ "def drop1 {A : Type} (1 p : A × Tok) : A := p.1") "take the pair apart with `let 1 (x, y) := p; …`"
        -- a `let` at 1 of a projection is no better, and a pair in the middle of a tuple neither
        failsLib (r1Header ++ "def let1 {A : Type} (1 p : A × Tok) : A := let 1 a : A := p.1; a") needs
        failsLib (r1Header ++ "def mid {A : Type} (1 p : A × Tok × Tok) : Tok := p.2.1") needs },
    { name := "... a projection of an expression uses the expression ω times (R1)", run := fun _ => do
        failsLib (r1Header ++ "def bad {A : Type} (f : (1 t : Tok) → A × Tok) (1 t : Tok) : A := (f t).1")
          "cannot project (f t).1"
        okLib (r1Header ++ "def fine {A : Type} (f : (1 t : Tok) → A × Tok) (t : Tok) : A := (f t).1\n" ++
          "def split {A : Type} (f : (1 t : Tok) → A × Tok) (1 t : Tok) : (1 u : Tok) × A := let 1 (a, u) := f t; (u, a)") },
    { name := "... a linear pair is taken apart with let 1 (x, y) := p, which accounts for both components", run := fun _ => do
        okLib (r1Header ++ "def swap {A : Type} (1 p : A × Tok) : (1 t : Tok) × A := let 1 (a, t) := p; (t, a)\n" ++
          "def nest {A : Type} (1 p : A × Tok × Tok) : (1 t : Tok) × (1 u : Tok) × A := let 1 (a, r) := p; let 1 (t, u) := r; (u, t, a)\n" ++
          "def inTy (1 p : (A : Type) × A) (f : (0 A : Type) → (1 x : A) → Nat) : Nat := let 1 (A, x) := p; f A x")
        -- the split may not drop the bare second component either
        failsLib (r1Header ++ "def dropSplit {A : Type} (1 p : A × Tok) : A := let 1 (a, t) := p; a") "variable t declared with quantity 1 but used 0"
        -- and without a quantity it is a split at ω
        failsLib (r1Header ++ "def atω {A : Type} (1 p : A × Tok) : (1 t : Tok) × A := let (a, t) := p; (t, a)") "quantity 1 but used ω" },
    { name := "... an unrestricted pair has both projections, whatever its fields' quantities", run := fun _ =>
        okLib (r1Header ++ "def fstω {A : Type} (p : A × Tok) : A := p.1\ndef sndω {A : Type} (p : (1 a : A) × Tok) : Tok := p.2\n" ++
          "def both {A : Type} (p : A × Tok) : Tok × A := (p.2, p.1)\ndef mid {A : Type} (p : A × (1 t : Tok) × Tok) : Tok := p.2.1") },
    { name := "... a pair at a quantity variable can't be projected, but it can be split at that quantity", run := fun _ => do
        failsLib (r1Header ++ "def polyq {A : Type} {q : Qty} (%q p : A × Tok) : A := p.1") "a projection needs an unrestricted pair"
        okLib (r1Header ++ "def poly {A : Type} {q : Qty} (%q p : A × Tok) (k : (%q a : A) → (%q t : Tok) → Nat) : Nat := let %q (a, t) := p; k a t") },
    { name := "... erased positions project freely: a 0 argument, a let at 0, a 0 field, a split at 0", run := fun _ => do
        okLib (r1Header ++ "def erasedArg {A : Type} (0 p : A × Tok) (g : (0 a : A) → Nat) : Nat := g p.1\n" ++
          "def peek {A : Type} (1 p : A × Tok) (g : (0 a : A) → (1 p : A × Tok) → Nat) : Nat := g p.1 p\n" ++
          "def let0 {A : Type} (1 p : A × Tok) : A × Tok := let 0 a : A := p.1; p\n" ++
          "def field0 {A : Type} (1 p : A × Tok) : ((0 a : A) × Unit) × (A × Tok) := ((p.1, ()), p)\n" ++
          "def split0 {A : Type} (1 p : A × Tok) : A × Tok := let 0 (a, t) := p; p")
        -- what is bound at 0 there can't be used at runtime, and an erased variable has no runtime projection
        failsLib (r1Header ++ "def use0 {A : Type} (1 p : A × Tok) : A × (A × Tok) := let 0 a : A := p.1; (a, p)") "variable a declared with quantity 0"
        failsLib (r1Header ++ "def use00 {A : Type} (1 p : A × Tok) : A × (A × Tok) := let 0 (a, t) := p; (a, p)") "variable a declared with quantity 0"
        failsLib (r1Header ++ "def run0 {A : Type} (0 p : A × Tok) : A := p.1") "a projection needs an unrestricted pair" },
    { name := "... a 0 position is never evaluated: #eval of a let at 0, a 0 field, a split at 0, a 0 argument", run := fun _ =>
        okLib ("import Prelude\npartial def loop (u : Unit) : Nat × Nat := loop u\n" ++
          "def a : Nat := let 0 x : Nat := (loop ()).1; 1\ndef b : (0 x : Nat) × Nat := ((loop ()).1, 2)\n" ++
          "def c : Nat := let 0 (x, y) := loop (); 3\ndef d (f : (0 x : Nat) → Nat) : Nat := f (loop ()).1\n" ++
          "#eval a\n#eval b.2\n#eval c\n#eval d (fun _ => 4)") ["1", "2", "3", "4"] },
    { name := "... a structure can't be held at quantity 1 yet: no field access, no match, no nested split (R1)", run := fun _ => do
        let guard := r1Header ++ "structure Guard where\n  n : Nat\n  tok : Tok\n"
        okLib (guard ++ "def readω (g : Guard) : Nat × Tok := (g.n, g.tok)\ndef pass (1 g : Guard) : Guard := g")
        failsLib (guard ++ "def s1 (1 g : Guard) : Nat := g.n") "a structure can't be held at a quantity other than ω yet"
        failsLib (guard ++ "def s2 (1 g : Guard) : Tok := g.tok") "use a tuple `A × B` instead"
        failsLib (guard ++ "def s3 (1 g : Guard) : Nat × Tok := match g with\n  | .mk n t => (n, t)") "cannot match on a value of type"
        failsLib (guard ++ "def s4 (1 g : Guard) : (1 t : Tok) × Nat := let 1 (n, rest) := g; let 1 (t, tail) := rest; (t, n)")
          "variable tail declared with quantity 1 but used 0"
        -- a tuple pattern in `match` is two projections: not for a linear pair
        failsLib (r1Header ++ "def m1 (1 p : Nat × Tok) : (1 t : Tok) × Nat := match p with\n  | (n, t) => (t, n)") "quantity 1 but used ω" },
    -- (linear-case p05) raw `ind` binds the payload at ω, so its scrutinee counts ω times
    { name := "ind on a linear scrutinee is rejected: it could duplicate or drop the payload", run := fun _ => do
        let box := r1Header ++ "def BoxD : Desc Unit := Desc.arg 1 Tok (fun _ => Desc.ret ())\ndef Box : Type := μ BoxD ()\n" ++
          "def box (1 t : Tok) : Box := con (t, (), ())\n"
        failsLib (box ++ "def dup (1 b : Box) : Tok × Tok := ind (fun _ _ => Tok × Tok) (fun i xs ih => (xs.1, xs.1)) b")
          "variable b declared with quantity 1 but used ω"
        failsLib (box ++ "def dropTok (1 t : Tok) : Unit := ind (fun _ _ => Unit) (fun i xs ih => ()) (box t)")
          "variable t declared with quantity 1 but used ω"
        okLib (box ++ "def dupω (b : Box) : Tok × Tok := ind (fun _ _ => Tok × Tok) (fun i xs ih => (xs.1, xs.1)) b") },
    { name := "a 0 position is never evaluated: a constructor field at 0, a 0 field of a structure (#eval)", run := fun _ =>
        okLib ("import Prelude\n" ++ zeroFieldDecls ++ "#eval e1\n#eval e2\n#eval e3\n#eval e4") ["7", "8", "9", "2"] },
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
          "no witness found" },
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
          "#eval depthA (.a1 (fun _ => .a1 (fun _ => .a0)))") ["2"] },
    { name := "13c: if, &&, || and ! in the Prelude", run := fun _ =>
        okLib ("import Prelude\ndef f (b : Bool) (n : Nat) : Nat := if b then n + 1 else 0\n#eval f .true 3\n" ++
          "#eval if Nat.beq 1 1 && !(Nat.beq 2 3) then \"yes\" else \"no\"\n" ++
          "#eval Nat.beq 1 1 && !(Nat.beq 2 3) || Bool.false\n#eval (Bool.false || Bool.true) && Bool.false\n" ++
          "def nested (n : Nat) : Nat := match n with\n  | .zero => if Nat.beq n 0 then 1 else 2\n  | .succ m => m\n#eval nested 0\n" ++
          "def t1 (b : Bool) : (Bool.true && b) = b := rfl\ndef t2 (b : Bool) : (Bool.false || b) = b := rfl\n")
          ["4", "\"yes\"", ".true", ".false", "1"] },
    { name := "13c: && and || short-circuit in compiled code", run := fun _ =>
        ioRun ("import IO\npartial def spin (n : Nat) : Bool := spin n\n" ++
          "def main : IO Unit := IO.println (if Bool.false && spin 0 then \"bad\" else if Bool.true || spin 1 then \"lazy ok\" else \"bad\")")
          "lazy ok\n" },
    { name := "13d: Functor and Applicative (import Functor)", run := fun _ =>
        okLib ("import Functor\n#eval Nat.add <$> Option.some 1 <*> Option.some 2\n" ++
          "#eval (fun (a b : Nat) => (a, b)) <$> List.cons 1 (List.cons 2 .nil) <*> List.cons 3 .nil\n" ++
          "#eval Nat.succ <$> List.cons 1 (List.cons 2 .nil)\n#eval Nat.succ <$> (Except.error \"e\" : Except String Nat)\n" ++
          "def addOpt (x y : Option Nat) : Option Nat := do\n  a ← x;\n  b ← y;\n  Monad.pure (a + b)\n#eval addOpt (.some 1) (.some 2)\n" ++
          "def pairT : TacticM (Nat × Nat) := (fun (a b : Nat) => (a, b)) <$> TacticM.pure 1 <*> TacticM.pure 2\n")
          [".some 3", ".cons (1, 3) (.cons (2, 3) .nil)", ".cons 2 (.cons 3 .nil)", ".error \"e\"", ".some 3"] },
    { name := "13d: <$> and <*> for IO, from its Monad instance", run := fun _ =>
        ioRun ("import IO\nimport Functor\ndef main : IO Unit := do\n  n ← Nat.add <$> IO.pure 40 <*> IO.pure 2;\n" ++
          "  IO.println (Nat.toString n)") "42\n" },
    { name := "13e: ∃ binders, ¬, and ASCII spellings (import Logic)", run := fun _ =>
        okLib ("import Logic\ndef t1 : ∃ n, n = 3 := Ex.intro (fun n => n = 3) 3 rfl\n" ++
          "def t2 : ∃ n : Nat, n + n = 4 := Ex.intro _ 2 rfl\ndef t3 : ∃ (n : Nat), n = 3 := Ex.intro _ 3 rfl\n" ++
          "def t5 : ∃ (n : Nat) m, n = m ∧ m = n := Ex.intro (fun n => ∃ m, n = m ∧ m = n) 3 (Ex.intro (fun m => 3 = m ∧ m = 3) 3 (rfl, rfl))\n" ++
          "def same {A : Type} (P : A → A → Prop) : (∃ x y : A, P x y) → @Ex A (fun x => @Ex A (fun y => P x y)) := fun h => h\n" ++
          "def swap {A : Type} {P : A → A → Prop} (h : ∃ x y, P x y) : ∃ y x, P x y :=\n" ++
          "  Ex.elim h (fun x h' => Ex.elim h' (fun y p => Ex.intro (fun y => ∃ x, P x y) y (Ex.intro (fun x => P x y) x p)))\n" ++
          "def nope : ¬ (exists (b : Bool), b = .true ∧ b = .false) :=\n  fun h => Ex.elim h (fun b p => Bool.trueNeFalse (Eq.trans (Eq.symm p.1) p.2))\n" ++
          "def t7 : forall (n : Nat), n = n := fun n => rfl\n" ++
          "def t8 {P Q : Prop} (h : P <-> Q) (p : P) : (Q /\\ P) \\/ False := Or.inl (h.1 p, p)\n#check t5")
          ["t5 : Ex Nat (fun n => Ex Nat (fun m => And (n = m) (m = n)))"] },
    { name := "13f: let with a tuple pattern of three or more names", run := fun _ =>
        okLib ("import Prelude\ndef f (p : Nat × Nat × Nat) : Nat := let (a, b, c) := p; a + b * c\n#eval f (1, 2, 3)\n" ++
          "def g (p : Nat × Bool × Nat × Nat) : Nat := let (a, b, c, d) := p; match b with\n  | .true => a + c + d\n  | .false => 0\n" ++
          "#eval g (1, .true, 3, 4)\ndef tuple : Nat := 7\ndef noCapture (p : Nat × Nat × Nat) : Nat := let (a, b, c) := p; tuple\n" ++
          "#eval noCapture (1, 2, 3)\naxiom Tok : Type\naxiom Tok.close : (1 t : Tok) → Unit\n" ++
          "def lin (1 p : Nat × Tok × Tok) : Unit × Unit :=\n  let 1 (n, s, t) := p;\n  (Tok.close s, Tok.close t)\n")
          ["7", "8", "7"] },
    { name := "... and a linear one still binds each component once", run := fun _ =>
        failsLib ("import Prelude\naxiom Tok : Type\naxiom Tok.close : (1 t : Tok) → Unit\n" ++
          "def lin (1 p : Nat × Tok × Tok) : Unit × Unit :=\n  let 1 (n, s, t) := p;\n  (Tok.close s, Tok.close s)\n")
          "quantity 1 but used" },
    -- keyword scopes (13j): `if`/`then`/`else` are keywords inside `run_calc … done` only
    { name := "keyword scope: a DSL's keywords are identifiers outside it (13j)", run := fun _ =>
        okLib (calcDsl " (keywords := calc_kw)" ++
          "#eval run_calc if [isZero] [0] then [else] [then] else [else (else then)] done\n" ++
          "#eval run_calc if [isZero] [then] then [5] else [else 7] done") ["2", "8"] },
    { name := "... and not its own identifiers", run := fun _ =>
        failsLib (calcDsl " (keywords := calc_kw)" ++ "#eval run_calc [else] then done")
          "identifier ('then' is a keyword here)" },
    { name := "... without the scope the DSL's `if` is an application", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let input := calcDsl "" ++ "#eval run_calc if [isZero] [0] then [else] [then] else [else (else then)] done"
        let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some prelude else none }
        check ((s.messages.filter (·.severity == .error)).size > 0) "expected errors" }
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
        let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
        let out := String.intercalate "\n" (s.messages.toList.map (·.text))
        check ((out.splitOn "wiz_word_add").length > 1) s!"no native call in:\n{out}" },
    { name := "the width is part of the type, and is inferred", run := fun _ => do
        okLib "import Word\ndef w {ω n : Nat} (a : UIntN n) : Nat := n\n#check w (U8.ofNat 3)\n#eval w (U8.ofNat 3)"
          ["w 8 (U8.ofNat 3) : Nat", "8"]
        let loader ← preludeLoader
        let s := runFrontend (R := ZeroOneMany) "import Word\ndef bad (x : U8) : U16 := x" { loader, trustedModule := Tests.libModule }
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
        let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
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
    { name := "one-shot effects: a continuation may hold a linear value; Eff programs run under one-shot handlers", run := fun _ =>
        ioRun "import Eff\ndef Coin : Type := Nat\ndef Coin.mk (n : Nat) : Coin := n\ndef Coin.spend (1 c : Coin) : Nat := c\ndef prog {R : Type} (1 c : Coin) : Eff1 1 (Row.cons (State Nat) Row.nil) R Coin :=\n  Eff1.bind (do1 n ← get1; put1 (n + 1)) (fun u => Eff1.pure c)\ndef spent : Nat := Coin.spend (Eff1.run1 (evalState1 (prog (Coin.mk 5)) 10))\ndef count {R : Type} : Eff1 ω (Row.cons (State Nat) (Row.cons Console Row.nil)) R Nat := do1\n  n ← get1;\n  println1 \"counting\";\n  put1 (n + 1);\n  get1\ndef old : Eff (Row.cons (State Nat) Row.nil) Nat := do\n  n ← get;\n  put (n * 2);\n  get\ndef runOld : Nat := (Eff1.run (runState1 (Eff.toEff1 old) 21)).1\ndef main : IO Unit := do1\n  p ← runConsole1 (runState1 count 10);\n  IO.println (Nat.toString p.1);\n  IO.println (Nat.toString spent);\n  IO.println (Nat.toString runOld)" "counting\n11\n5\n42\n" },
    { name := "... which a multi-shot continuation can't", run := fun _ =>
        ioFails "import Eff\ndef Coin : Type := Nat\ndef Coin.mk (n : Nat) : Coin := n\ndef Coin.spend (1 c : Coin) : Nat := c\ndef prog (1 c : Coin) : Eff (Row.cons (State Nat) Row.nil) Coin :=\n  Eff.bind (do n ← get; put (n + 1)) (fun u => Eff.pure c)" "quantity 1 but used ω" },
    { name := "a one-shot handler resumes exactly once: not twice, not never", run := fun _ => do
        ioFails "import Eff\ndef twice {r : Row} {R A : Type} (1 m : Eff1 ω (Row.cons Console r) (Eff1 ω r R A) A) : Eff1 ω r R A :=\n  Eff1.handle (fun a => Eff1.pure a) (fun o k => Eff1.bind (k ()) (fun x => k ())) m" "variable k declared with quantity 1 but used ω"
        ioFails "import Eff\ndef abort {r : Row} {R A : Type} (d : A) (1 m : Eff1 ω (Row.cons (Exn String) r) (Eff1 ω r R A) A) : Eff1 ω r R A :=\n  Eff1.handle (fun a => Eff1.pure a) (fun o k => Eff1.pure d) m" "variable k declared with quantity 1 but used 0"
        ioRun "import Eff\ndef quiet {r : Row} {R A : Type} (1 m : Eff1 ω (Row.cons Console r) (Eff1 ω r R A) A) : Eff1 ω r R A :=\n  Eff1.handle (fun a => Eff1.pure a) (fun o k => k ()) m\ndef main : IO Unit := IO.println \"ok\"" "ok\n" },
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
          "instance {S : Type} : Commute (State S) (State S) (StateM S) where\n  comm := fun o₁ o₂ B f => rfl")
          -- (13b) the elaborator compares the two sides of `rfl` itself, before the kernel
          "rfl: the two sides are not definitionally equal" }
  ]

def toolingGroup : Group where
  name := "tooling"
  exercise := "Stage 11"
  cases := [
    { name := "queries: an edit re-elaborates only what follows it", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some prelude else none }
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
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some prelude else none }
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
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some prelude else none }
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
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some prelude else none }
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
        let st := runFrontend (R := ZeroOneMany) "import Prelude" { trustedModule := Tests.libModule, loader := fun _ => some prelude }
        for n in ["List.append", "Nat.rec", "SyntaxF.casesOn", "Tac.rec", "Monad.bind"] do
          let some d := st.globals.find? n | throw (IO.userError s!"no {n}")
          let text := (Cache.term d.type).render
          match (Cache.Sx.parse text).bind (Cache.dterm (R := ZeroOneMany)) with
          | some t => check (t == d.type) s!"{n}: the type changed in the round trip"
          | none => throw (IO.userError s!"{n}: could not read back {text.take 200}") },
    { name := "the language server answers requests", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let srv : LSP.Server := { libs := ({} : Std.HashMap String (String × String)).insert "Prelude" ("lib/Prelude.wiz", prelude), trusted := ["Prelude"] }
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
    { name := "self tail calls are loops: 10M iterations on a 1 MB stack, at -O0 (15f)", run := fun _ =>
        cRunSmallStack (llvm := llvm) ("import Prelude\npartial def count (n acc : Nat) : Nat := match n with\n  | .zero => acc\n" ++
          "  | .succ m => match Nat.beq (Nat.mod m 3) 0 with\n    | .true => count m (acc + 2)\n    | .false => count m acc\n" ++
          "def main : Nat := count 10000000 0") "6666668" },
    { name := "constant folding and known constructors behave as before (15c)", run := fun _ =>
        cRun (llvm := llvm) foldSrc foldExpected },
    { name := "numerals at 2^31 … 2^64+1 and 10^30 are constants (15g)", run := fun _ =>
        cRun (llvm := llvm) bigLitSrc bigLitExpected },
    { name := "Bool.and/Bool.or don't compute an argument they don't need: one that never returns, 10M steps on a 1 MB stack at -O0 (15h)", run := fun _ =>
        cRunSmallStack (llvm := llvm) caseShapeSrc caseShapeExpected },
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
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ndef t : Nat.div 7 0 = 7 := refl 7" { trustedModule := Tests.libModule, loader := fun _ => some prelude }
        check (s.messages.any (·.severity == .error)) "expected an error" },
    { name := "kernel arithmetic on literals is native", run := fun _ =>
        okLib "import Prelude\ndef t : 100000 * 100000 = 10000000000 := refl 10000000000" },
    { name := "literals unfold under eliminators", run := fun _ =>
        okLib ("import Prelude\ndef isZero : Nat → Bool\n  | .zero => .true\n  | .succ _ => .false\n" ++
          "def t : isZero 3 = Bool.false := refl Bool.false\ndef u : Nat.succ 4 = 5 := refl 5") },
    { name := "different literals are not equal", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ndef t : 2 + 2 = 5 := refl 4" { trustedModule := Tests.libModule, loader := fun _ => some prelude }
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
        let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := fun _ => some prelude }
        check (s.messages.any (·.text == "kaboom")) s!"expected kaboom, got {s.messages.map (·.text)}" },
    { name := "only a Macro can be a macro", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let s := runFrontend (R := ZeroOneMany) "import Prelude\nattribute [macro term.app] Nat.add" { trustedModule := Tests.libModule, loader := fun _ => some prelude }
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
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ninductive Bad where\n  | mk (k : Bad → Bad)" { trustedModule := Tests.libModule, loader := fun _ => some prelude }
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
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ndef s : String := 3" { trustedModule := Tests.libModule, loader := fun _ => some prelude }
        check (s.messages.any (·.severity == .error)) "expected an error" },
    -- S1 (`wiz-notes/soundness-audit.md`): `Term.mapChildrenM` had no case for `natOp`, so
    -- the variable captured by `Nat.add x` was invisible to `Val.lvlBound`, `sameVal` quoted
    -- below it, and `μ D_x () = μ D_y ()` computed to `() = ()`. With `T (Nat.add 0)`
    -- inhabited and `T (Nat.add 1)` empty, `cast (e 0 1)` then gave a closed proof of False.
    { name := "S1: a variable captured by a native operation counts in syntactic equality (it proved False)", run := fun _ => do
        let t := "import Prelude\ndef T (f : Nat → Nat) : Type := match f 0 with\n  | .zero => Unit\n  | .succ _ => Empty\n"
        failsLib (t ++ "def Box (x : Nat) : Type := μ (Desc.arg 1 (T (Nat.add x)) (fun _ => Desc.ret ()) : Desc Unit) ()\n" ++
          "def e (x y : Nat) : Box x = Box y := ()\n") "mismatch"
        failsLib (t ++ "inductive Box (f : Nat → Nat) where\n  | mk (t : T f)\n" ++
          "def e (x y : Nat) : Box (Nat.add x) = Box (Nat.add y) := ()\n") "mismatch"
        failsLib (t ++ "inductive Box (f : Nat → Nat) where\n  | mk (t : T f)\n" ++
          "def e (x y : Nat) : Box (Nat.mul x) = Box (Nat.sub y) := ()\n") "mismatch" },
    { name := "S1: the same family at the same partial application is still one family", run := fun _ =>
        okLib ("import Prelude\ndef T (f : Nat → Nat) : Type := match f 0 with\n  | .zero => Unit\n  | .succ _ => Empty\n" ++
          "inductive Box (f : Nat → Nat) where\n  | mk (t : T f)\n" ++
          "def e (x : Nat) : Box (Nat.add x) = Box (Nat.add x) := rfl\n") }
  ]


/-- `okLib` with `lib/Optic.wiz` importable too. -/
def okOptic (input : String) (infos : List String := []) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let optic ← IO.FS.readFile "lib/Optic.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "Optic" then some optic else none
  let s := runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr (s.messages.toList.map (·.text))).pretty

def failsOptic (input : String) (fragment : String) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let optic ← IO.FS.readFile "lib/Optic.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "Optic" then some optic else none
  let s := runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule }
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
  pure (runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule })

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
    { name := "deriving with proof fields: not shown, not compared, no default (F5)", run := fun _ =>
        okDeriving ("import Deriving\nstructure Pos where\n  n : Nat\n  h : Nat.lt 0 n = Bool.true\n  deriving Repr, BEq\n" ++
          "#eval Repr.repr (Pos.mk 3 (refl Bool.true))\n#eval BEq.beq (Pos.mk 3 (refl Bool.true)) (Pos.mk 4 (refl Bool.true))\n" ++
          "inductive W where\n  | a (n : Nat) (h : n = n)\n  | b\n  deriving Repr, BEq, Inhabited\n" ++
          "#eval Repr.repr (W.a 2 (refl 2))\n#eval BEq.beq (W.a 2 (refl 2)) (W.a 2 (refl 2))\n#eval Repr.repr (Inhabited.default : W)")
          ["\"Pos.mk 3 _\"", ".false", "\"W.a 2 _\"", ".true", "\"W.b\""] },
    { name := "Inhabited skips a constructor with a proof field", run := fun _ =>
        failsDeriving "import Deriving\ninductive I where\n  | p (h : 0 = 0)\n  deriving Inhabited" "every constructor of I is recursive or has a proof field" },
    { name := "deriving for a universe-polymorphic type (no signature: Type u is inferred)", run := fun _ =>
        okDeriving ("import Deriving\ninductive Box.{u} (A : Type u) where\n  | mk (x : A)\n  deriving Repr, BEq, Inhabited\n" ++
          "structure P.{u} (A : Type u) where\n  x : A\n  n : Nat\n  deriving Repr, BEq, Inhabited\n" ++
          "#eval Repr.repr (Box.mk (P.mk 1 2))\n#eval BEq.beq (Box.mk 1) (Box.mk 2)\n#eval Repr.repr (Inhabited.default : P Nat)\n" ++
          "#check @instReprBoxA")
          ["\"Box.mk (P.mk 1 2)\"", ".false", "\"P.mk 0 0\"",
           "instReprBoxA : {A : Type ?u0} → [inst✝ : Repr A] → Repr (Box A)"] },
    { name := "deriving for a type above Type: lifted fields are seen through down (F5)", run := fun _ =>
        okDeriving ("import Deriving\ninstance : Repr Type := Repr.mk (fun _ _ => \"<type>\")\n" ++
          "instance : Inhabited Type := Inhabited.mk Nat\n" ++
          "inductive Big where\n  | b (n : Nat) (h : n = n)\n  | c (T : Type)\n  deriving Repr, Inhabited\n" ++
          "#eval Repr.repr (Big.b 3 (refl 3))\n#eval Repr.repr (Big.c Nat)\n#eval Repr.repr (Inhabited.default : Big)")
          ["\"Big.b 3 _\"", "\"Big.c <type>\"", "\"Big.c <type>\""] },
    { name := "the example runs", run := fun _ => do
        let src ← IO.FS.readFile "examples/deriving.wiz"
        let s ← derivingRun src
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}") }
  ]

/-- Messages of `input` (with `lib/` importable), without positions, errors marked. -/
def messagesLib (input : String) : IO (List String) := do
  let loader ← preludeLoader
  let s := runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule }
  pure (s.messages.toList.map fun m => (match m.severity with
    | .error => "error: " | .warning => "warning: " | .info => "") ++ m.text)

/-- Some error mentions `fragment` (others may follow from it). -/
def failsWith (input : String) (fragment : String) : IO Unit := do
  let errs := errors input
  unless errs.any (fun e => (e.splitOn fragment).length > 1) do
    throw (IO.userError s!"no error mentions '{fragment}': {errs}")

def familyTF : String := "inductive B where\n  | t\n  | f\ninductive T : B → Type where\n  | mk : T .t\n"

/-- A type the witness search can't reach: its only value is five constructors deep. -/
def deepType : String :=
  "inductive A5 where\n  | mk\ninductive A4 where\n  | mk (x : A5)\ninductive A3 where\n  | mk (x : A4)\n" ++
  "inductive A2 where\n  | mk (x : A3)\ninductive A1 where\n  | mk (x : A2)\n"

/-- A number type of one's own, with an addition that disagrees with the native one. -/
def ownNat : String :=
  "inductive N where\n  | zero\n  | succ (n : N)\ndef K (a b : N) : N := a\nbuiltin nat := N\n" ++
  "builtin nat.zero := N.zero\nbuiltin nat.succ := N.succ\nbuiltin nat.add := K\n"

/-- Some error (with `lib/` importable) mentions `fragment`. -/
def failsWithLib (input : String) (fragment : String) : IO Unit := do
  let errs := (← messagesLib input).filter (·.startsWith "error: ")
  unless errs.any (fun e => (e.splitOn fragment).length > 1) do
    throw (IO.userError s!"no error mentions '{fragment}': {errs}")

/-- O3: a registration outside the library that disagrees with native addition. -/
def badAdd : String :=
  ownNat ++
  "def h (n : N) : K n 3 = n := refl n\ndef bad : False := absurd (h 2)\n#print axioms bad\n"

/-- The trusted base: partial definitions need a kernel-checked witness (O2), and
`builtin` registrations outside the library are tracked axioms (O3). -/
def trustGroup : Group where
  name := "trust"
  exercise := "—"
  cases := [
    { name := "O2: a partial definition at an empty index is rejected", run := fun _ =>
        failsWith (familyTF ++ "partial def bad : T .f := bad\ndef boom : False := match bad with\n  | .mk => absurd ()\n")
          "no witness found" },
    { name := "O2: a partial function into an empty index is rejected", run := fun _ =>
        fails (familyTF ++ "partial def bad : T .t → T .f := bad\n") "no witness found" },
    { name := "O2: a wrong witness is rejected", run := fun _ =>
        fails (familyTF ++ "partial (default := T.mk) def bad : T .f := bad\n") "type mismatch" },
    { name := "partial definitions with inferred witnesses", run := fun _ =>
        ok (familyTF ++ "inductive Nat where\n  | zero\n  | succ (n : Nat)\n" ++
            "inductive List (A : Type) where\n  | nil\n  | cons (x : A) (xs : List A)\n" ++
            "partial def p1 : T .t := p1\npartial def p2 (b : B) (x : T b) : T b := p2 b x\n" ++
            "partial def p3 : Nat → List Nat := p3\npartial def p4 : (A : Type) × A := p4\n" ++
            "partial def p5 (A : Type) : A → Unit × A := p5 A\npartial def p6 : Type := p6\n" ++
            "axiom World : Type\naxiom w0 : World\npartial def p7 : World × B := p7\n" ++
            "mutual\ndef ev : Nat → B\n  | .zero => .t\n  | .succ n => od n\ndef od : Nat → B\n  | .zero => .f\n  | .succ n => ev n\nend\n" ++
            "#print axioms p2\n#print axioms p7\n")
          ["'p2' does not depend on any axioms", "'p7' depends on axioms: [w0, World]"] },
    { name := "a witness the search can't find, given with `default`", run := fun _ => do
        fails (deepType ++ "partial def f : Unit → A1 := f\n") "no witness found"
        ok (deepType ++ "partial (default := fun _ => A1.mk (A2.mk (A3.mk (A4.mk A5.mk)))) def f : Unit → A1 := f\n" ++
            "mutual\npartial (default := A1.mk (A2.mk (A3.mk (A4.mk A5.mk)))) def g : A1 := h ()\ndef h (u : Unit) : A1 := g\nend\n") },
    { name := "the kernel checks a partial definition's witness", run := fun _ => do
        let ty : Term ZeroOneMany := .unit 1
        let bad : Term ZeroOneMany := .empty 1
        check ((addPartialDecl (R := ZeroOneMany) {} { name := "f", type := ty, value := none }) matches .error _)
          "no witness accepted"
        check ((addPartialDecl (R := ZeroOneMany) {} { name := "f", type := .empty 1, value := none, witness := some .tt }) matches .error _)
          "ill-typed witness accepted"
        check ((addPartialDecl (R := ZeroOneMany) {} { name := "f", type := ty, value := none, witness := some .tt }) matches .ok _)
          "good witness rejected"
        check ((addDecl (R := ZeroOneMany) {} { name := "f", type := ty, value := none }) >>= (addPartialImpl · "f" .tt) matches .error _)
          "an axiom took an implementation"
        let _ := bad },
    { name := "the kernel checks a definition's implementation for the compiler (Decl.impl)", run := fun _ => do
        -- `f : Unit := tt`, with the term compiled code runs given by hand
        let ty : Term ZeroOneMany := .unit 1
        let f (impl : Term ZeroOneMany) (levelParams : List Name := []) : Decl ZeroOneMany :=
          { name := "f", levelParams, type := ty, value := some .tt, impl := some impl }
        let rejected (d : Decl ZeroOneMany) (fragment : String) : Bool :=
          match addDecl {} d with
          | .error e => ((toString e).splitOn fragment).length > 1
          | .ok _ => false
        check ((addDecl {} (f .tt)) matches .ok _) "a good implementation was rejected"
        -- it may call the definition (a recursive definition's does): checked with `f` declared
        check ((addDecl {} (f (.const "f" []))) matches .ok _) "an implementation calling its definition was rejected"
        check (rejected (f (.const "g" [])) "implementation of f") "an implementation with an unknown constant was accepted"
        -- ill-typed, and well-typed at another type
        check (rejected (f (.app .tt .tt)) "implementation of f") "an ill-typed implementation was accepted"
        check (rejected (f (.unit 1)) "implementation of f") "an implementation of another type was accepted"
        check (rejected (f (.pair .tt .tt)) "implementation of f") "an implementation of another type was accepted"
        -- a `Π` noted to be in a sort it is not in (erasure reads the note): `let T : Type := Π… in tt`
        let piNoted (s : Option Level) : Term ZeroOneMany :=
          .letE "T" (.qlit .zero) (.sort 1) (.pi "_" .default (.qlit .many) (.unit 1) (.unit 1) s) .tt
        check ((addDecl {} (f (piNoted none))) matches .ok _) "an implementation without sort notes was rejected"
        check ((addDecl {} (f (piNoted (some 1)))) matches .ok _) "a right sort note was rejected"
        check (rejected (f (piNoted (some 0))) "marked as in sort") "a wrong sort note in an implementation was accepted"
        check (rejected { f .tt with value := some (piNoted (some 0)), impl := none } "marked as in sort")
          "a wrong sort note in a value was accepted"
        -- quantities: a linear variable used twice
        let lin (body : Term ZeroOneMany) : Decl ZeroOneMany :=
          { name := "f", type := .pi "x" .default (.qlit .one) ty (.sigma "_" (.qlit .one) ty ty none) none,
            value := some (.lam "x" (.pair (.var 0) .tt)), impl := some (.lam "x" body) }
        check ((addDecl {} (lin (.pair .tt (.var 0)))) matches .ok _) "a linear implementation was rejected"
        check (rejected (lin (.pair (.var 0) (.var 0))) "implementation of f") "an implementation using a linear variable twice was accepted"
        -- universe level parameters
        check (rejected (f (.ann .tt (.unit (.param "u")))) "unknown universe level parameter u")
          "an implementation with an undeclared level parameter was accepted"
        -- `attribute [implemented_by g] f` goes through the kernel too (`setImpl`)
        let g ← match addDecls (R := ZeroOneMany) {} [{ name := "f", type := ty, value := some .tt },
            { name := "g", type := ty, value := some .tt }, { name := "h", type := .sort 2, value := some (.sort 1) }] with
          | .ok g => pure g
          | .error e => throw (IO.userError s!"setup rejected: {e}")
        check ((setImpl g "f" (.const "g" [])) matches .ok _) "a native implementation of the same type was rejected"
        check ((setImpl g "f" (.const "h" [])) matches .error _) "a native implementation of another type was accepted" },
    { name := "recursive definitions: the compiled equations are kernel-checked terms", run := fun _ => do
        let src := "inductive N where\n  | z\n  | s (n : N)\n" ++
          "def add : N → N → N\n  | .z, m => m\n  | .s n, m => .s (add n m)\n" ++
          "def double : N → N\n  | .z => .z\n  | .s n => .s (.s (double n))\n" ++
          "inductive V (A : Type) : N → Type where\n  | nil : V A .z\n  | cons {n : N} (x : A) (xs : V A n) : V A (.s n)\n" ++
          "def vlen {A : Type} {0 n : N} : V A n → N\n  | .nil => .z\n  | .cons _ xs => .s (vlen xs)\n" ++
          "#eval double (add (.s .z) (.s .z))\n"
        let s := runFrontend (R := ZeroOneMany) src
        check (s.messages.all (·.severity != .error)) s!"errors: {s.messages.toList.map (·.text)}"
        for n in ["add", "double", "vlen"] do
          let some d := s.globals.find? n | throw (IO.userError s!"{n} is missing")
          let some impl := d.impl | throw (IO.userError s!"{n} has no implementation")
          -- what `addDecl` did: the implementation checks at the declared type, with `n` declared
          let ctx : Ctx ZeroOneMany := { globals := s.globals }
          check ((Wiz.check ctx impl (ctx.eval d.type)) matches .ok _) s!"{n}'s implementation does not check"
          -- and the declaration can't be re-added with a broken one
          let g0 : Globals ZeroOneMany := { s.globals with decls := s.globals.decls.erase n }
          check ((addDecl g0 d) matches .ok _) s!"{n} is rejected when added again"
          check ((addDecl g0 { d with impl := some .tt }) matches .error _)
            s!"{n} was accepted with an implementation of another type" },
    { name := "recursive definitions: a local variable named like the definition doesn't capture its calls in compiled code", run := fun _ =>
        -- `f n` is a recursive call (the kernel's definition recurses, so `f 2 = 0`); the
        -- compiled equations called the local `f`, and `#eval f 2` was `3`
        ok ("inductive N where\n  | z\n  | s (n : N)\n" ++
            "def f : N → N\n  | .z => .z\n  | .s n => (fun (f : N → N) => f n) (fun x => .s (.s x))\n" ++
            "def fThm : f (.s (.s .z)) = .z := refl N.z\n#eval f (.s (.s .z))\n#run f (.s (.s .z))\n" ++
            "def g : N → N\n  | .z => .z\n  | .s n => let g : N → N := fun x => .s (.s x); g n\n" ++
            "def gThm : g (.s (.s .z)) = .z := refl N.z\n#eval g (.s (.s .z))\n" ++
            -- a pattern variable too
            "def h : N → (N → N) → N\n  | .z, _ => .z\n  | .s n, h => h n (fun x => .s x)\n" ++
            "def hThm : h (.s (.s .z)) (fun x => .s x) = .z := refl N.z\n#eval h (.s (.s .z)) (fun x => .s x)\n")
          [".z", ".z", ".z", ".z"] },
    { name := "O3: an unchecked registration is an axiom", run := fun _ => do
        let msgs ← messagesLib badAdd
        let expect := ["warning: builtin nat := N is not checked: it is an axiom of every declaration that depends on N (see `#print axioms`)",
          "warning: builtin nat.zero := N.zero is not checked: it is an axiom of every declaration that depends on N.zero (see `#print axioms`)",
          "warning: builtin nat.succ := N.succ is not checked: it is an axiom of every declaration that depends on N.succ (see `#print axioms`)",
          "warning: builtin nat.add := K is not checked: it is an axiom of every declaration that depends on K (see `#print axioms`)",
          "'bad' depends on axioms: [builtin nat.add := K, builtin nat := N, builtin nat.zero := N.zero, builtin nat.succ := N.succ]"]
        checkEq (repr expect).pretty (repr msgs).pretty },
    { name := "O3: numerals at a registered empty type are an error, not a crash", run := fun _ => do
        failsWith "def E : Type := Empty\nbuiltin nat := E\ndef bad : False := absurd (0 : E)\n" "inductive type"
        fails "inductive E where\n  | z\nbuiltin nat := E\ndef x : E := 0\n" "numerals need"
        fails "inductive N where\n  | z\naxiom Z : N\nbuiltin nat := N\nbuiltin nat.zero := Z\n" "must be a definition"
        fails "inductive N where\n  | z\ndef f (a : N) : N := a\nbuiltin nat := N\nbuiltin nat.add := f\n" "2 arguments" },
    { name := "O3: a registration in a module from an -I directory is an axiom", run := fun _ => do
        let dir : System.FilePath := s!"/tmp/wiz-trust-{← IO.monoNanosNow}"
        IO.FS.createDirAll dir
        IO.FS.writeFile (dir / "Mine.wiz") ownNat
        -- a `Prelude` in the directory doesn't replace the library's
        IO.FS.writeFile (dir / "Prelude.wiz") "builtin nat := Nat\n"
        let roots : List System.FilePath := ["lib", dir]
        let cl ← Wiz.Module.loadClosure roots "import Prelude\nimport Mine\n"
        let own := Wiz.Module.fromFirstRoot roots cl
        check (own.contains "Prelude" && !own.contains "Mine") s!"trusted modules: {own}"
        let init : CommandState ZeroOneMany := { loader := fun m => (cl.get? m).map (·.2), trustedModule := own.contains }
        let s := runFrontend (R := ZeroOneMany) "import Mine\ndef x : N := K 1 2\n#print axioms x\n" init
        let warns := (s.messages.toList.filter (·.severity == .warning)).map (·.text)
        let infos := (s.messages.toList.filter (·.severity == .info)).map (·.text)
        check (s.messages.all (·.severity != .error)) s!"errors: {s.messages.toList.map (·.text)}"
        checkEq 4 warns.length
        check (warns.all (·.startsWith "module Mine: ")) s!"warnings: {warns}"
        checkEq 1 infos.length
        for r in ["builtin nat.add := K", "builtin nat := N", "builtin nat.zero := N.zero", "builtin nat.succ := N.succ"] do
          check (infos.any fun l => (l.splitOn r).length > 1) s!"{r} is not listed: {infos}"
        -- the module and the Prelude both register `nat`: an error at the import, also
        -- when the module's commands are replayed from the cache
        let both := "import Prelude\nimport Mine\n"
        let once (s : CommandState ZeroOneMany) : Bool :=
          s.messages.any fun m => m.severity == .error && (m.text.splitOn "already registered").length > 1
        check (once (runFrontend (R := ZeroOneMany) both init)) "the frontend took a second `builtin nat`"
        let cache ← IO.FS.createTempDir
        for _ in [0:2] do
          let (s, _) ← Cache.elaborateCached cache both init 0
          check (once s) s!"the cache took a second `builtin nat`: {s.messages.toList.map (·.text)}"
          check (s.globals.builtins.lookup "nat" == some "Nat") "`nat` was redirected"
        IO.FS.removeDirAll dir },
    { name := "a builtin key is registered once (soundness audit T14)", run := fun _ => do
        -- the probe: a second `nat.add` redirected how the Prelude's `Nat.add` unfolds, and
        -- `boom : False` showed no axioms
        failsWithLib ("import Prelude\ndef K (a b : Nat) : Nat := a\nbuiltin nat.add := K\n" ++
          "def h (n : Nat) : Nat.add n 1 = n := refl n\ndef boom : False := absurd (h 0)\n") "builtin nat.add is already registered (as Nat.add)"
        -- the same for the numerals' constructors and type
        failsWithLib "import Prelude\ndef Z : Nat := 1\nbuiltin nat.zero := Z\n" "builtin nat.zero is already registered"
        failsWithLib "import Prelude\ndef S (n : Nat) : Nat := n\nbuiltin nat.succ := S\n" "builtin nat.succ is already registered"
        failsWithLib "import Prelude\ninductive M where\n  | z\nbuiltin nat := M\n" "builtin nat is already registered"
        -- one key per constant too
        failsWith (ownNat ++ "builtin nat.sub := K\n") "K is already registered as builtin nat.add"
        -- numerals unfold through `nat.zero` and `nat.succ`: constructors only
        failsWith ("inductive N where\n  | zero\n  | succ (n : N)\ndef S (n : N) : N := .zero\n" ++
          "builtin nat := N\nbuiltin nat.zero := N.zero\nbuiltin nat.succ := S\n") "must be a constructor of N"
        failsWith ("inductive N where\n  | zero\n  | succ (n : N)\ndef Z : N := .succ .zero\n" ++
          "builtin nat := N\nbuiltin nat.zero := Z\n") "must be a constructor of N" },
    { name := "a registered operation depends on the numerals' registrations", run := fun _ => do
        -- `P z z` is the numeral `1` (0 ^ 0) with no literal in the term: it unfolds
        -- through `nat.succ`
        let msgs ← messagesLib ("inductive N where\n  | zero\n  | succ (n : N)\ndef P (a b : N) : N := a\n" ++
          "builtin nat := N\nbuiltin nat.zero := N.zero\nbuiltin nat.succ := N.succ\nbuiltin nat.pow := P\n" ++
          "def x : N := P .zero .zero\n#print axioms x\n")
        let some l := msgs.getLast? | throw (IO.userError "no output")
        for r in ["builtin nat.pow := P", "builtin nat := N", "builtin nat.zero := N.zero", "builtin nat.succ := N.succ"] do
          check ((l.splitOn r).length > 1) s!"{r} is not listed: {l}" },
    { name := "Prelude registrations are trusted and compute natively", run := fun _ =>
        okLib "import Prelude\ndef t : 2 + 2 = 4 := refl 4\n#print axioms t\n#eval 3 * 7 + Nat.pow 2 10\n"
          ["'t' does not depend on any axioms", "1045"] },
    { name := "#print axioms: the Prelude's castRefl", run := fun _ =>
        okLib ("import Prelude\n#print axioms castRefl\n" ++
            "def r (A : Type) (e : A = A) (a : A) : (cast e a : A) = a := castRefl e a\n#print axioms r\n")
          ["'castRefl' depends on axioms: [castRefl]", "'r' depends on axioms: [castRefl]"] },
    { name := "#print axioms lists native implementations (implemented_by)", run := fun _ => do
        let note := "\n(native: an implementation that compiled code runs, trusted to agree with its definition)"
        okLib ("import Prelude\ndef slow (n : Nat) : Nat := n + 0\ndef fast (n : Nat) : Nat := n\n" ++
            "attribute [implemented_by fast] slow\ndef use (n : Nat) : Nat := slow n\n" ++
            "#print axioms use\n#print axioms fast\n" ++
            -- a recursive definition's own compiled equations and a partial one's body are not natives
            "def len : List Nat → Nat\n  | .nil => 0\n  | .cons _ t => len t + 1\n#print axioms len\n" ++
            "partial def spin (n : Nat) : Nat := fast n\n#print axioms spin\n")
          ["'use' depends on axioms: [native slow := fast]" ++ note, "'fast' does not depend on any axioms",
           "'len' does not depend on any axioms", "'spin' does not depend on any axioms"]
        -- the library's are listed too: words run natively, in a native representation
        okLib ("import Prelude\nimport Word\ndef idW (x : UIntN 8) : UIntN 8 := x\n#print axioms idW\n" ++
            "def w : UIntN 8 := UIntN.add (UIntN.ofNat 8 3) (UIntN.ofNat 8 4)\n#print axioms w\n")
          ["'idW' depends on axioms: [native UIntN := UIntN.ofBits/UIntN.toBits]" ++ note,
           "'w' depends on axioms: [native UIntN.ofNat := UIntN.ofNatNative, native UIntN := UIntN.ofBits/UIntN.toBits, " ++
             "native UIntN.add := UIntN.addNative, native UIntN.toNat := UIntN.toBits]" ++ note] },
    { name := "O2 in the self-hosted frontend", run := fun _ =>
        selfhostCheckFile (familyTF ++ "inductive Nat where\n  | zero\n  | succ (n : Nat)\n" ++
            "partial def bad : T .f := bad\npartial def bad2 : T .t → T .f := bad2\n" ++
            "partial def ok1 : T .t := ok1\npartial def ok2 (n : Nat) : Nat := ok2 n\n" ++
            "partial (default := T.mk) def ok3 : T .t := ok3\npartial (default := T.mk) def bad3 : T .f := bad3\n")
          ("B : U0\nT : (x0 : B) → U0\nNat : U0\n" ++
           "error: partial definition bad: no witness found for its type; give one with `partial (default := w) def`\n" ++
           "error: partial definition bad2: no witness found for its type; give one with `partial (default := w) def`\n" ++
           "ok1 : (T B.t)\nok2 : (x0 : Nat) → Nat\nok3 : (T B.t)\nerror: type mismatch: expected (T B.f), got (T B.t)\n") }
  ]

/-- Every `lib/*.wiz` and `lib/D/*.wiz` (as `D.X`), by module name. -/
def libLoader : IO (Name → Option String) := do
  let mut m : List (Name × String) := []
  for e in ← System.FilePath.readDir "lib" do
    if e.path.extension == some "wiz" then
      m := (e.path.fileStem.getD "", ← IO.FS.readFile e.path) :: m
    else if ← e.path.isDir then
      for f in ← System.FilePath.readDir e.path do
        if f.path.extension == some "wiz" then
          m := (e.fileName ++ "." ++ f.path.fileStem.getD "", ← IO.FS.readFile f.path) :: m
  pure fun n => m.lookup n

/-- No errors, and these messages, with every library importable. -/
def okLibs (input : String) (infos : List String := []) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr (s.messages.toList.map (·.text))).pretty

/-- Exactly one error, mentioning `fragment`, with every library importable. -/
def failsLibs (input : String) (fragment : String) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

/-- Build `main` with the C backend, with every library importable. -/
def cRunLibs (src : String) (expected : String) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← libLoader }
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
        -- (13b) the elaborator compares the two sides of `rfl` itself (`3 < 3` is `.false`)
        failsLibs (vecPrelude ++ "def bad : Nat := Vec.get v3 (Fin.of 3 3 rfl)") "rfl: the two sides are not definitionally equal" },
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
        let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← libLoader }
        let out := String.intercalate "\n" (s.messages.toList.map (·.text))
        check ((out.splitOn "ctor").length == 1 && (out.splitOn "proj").length == 1) s!"a word object in:\n{out}"
        check ((out.splitOn "wiz_word_ashr").length > 1 && (out.splitOn "wiz_word_slt").length > 1) s!"no natives in:\n{out}" }
  ]

/-! ## Stage 24: separation logic (lib/Logic.wiz, lib/HProp.wiz, lib/Hoare.wiz) -/

def seplogicGroup : Group where
  name := "seplogic"
  exercise := "Stage 24"
  cases := [
    { name := "the connectives; propext and funext are definitional", run := fun _ => do
        okLibs ("import Logic\n" ++
          "def t1 (P Q : Prop) (h : P ∧ Q) : Q ∧ P := And.symm h\n" ++
          "def t2 (P Q : Prop) (h : P ∨ Q) : Q ∨ P := Or.symm h\n" ++
          "def t3 : Ex (fun (n : Nat) => n = 3) := Ex.intro (fun (n : Nat) => n = 3) 3 rfl\n" ++
          "def t4 (P Q : Prop) (h : P ↔ Q) : P = Q := propext h\n" ++
          "def t5 (f : Nat → Nat) : (fun x => f x) = f := funext (fun x => rfl)\n" ++
          "def t6 (P : Prop) (n : Not P) (h : P ∨ False) : False := n (Or.resolveRight h (fun f => f))\n" ++
          "def t7 : Not (Nat.succ 0 = 0) := fun e => e")
        failsLibs "import Logic\ndef bad (P Q : Prop) (h : P ∨ Q) : P := h P (fun p => p) (fun q => q)" "mismatch" },
    { name := "heap predicates: ⋆ is commutative, associative, with unit emp (equations, no axioms)", run := fun _ =>
        okLibs ("import HProp\n" ++
          "def t1 (H₁ H₂ H₃ : HProp Nat) : (H₁ ⋆ H₂) ⋆ H₃ = H₁ ⋆ (H₂ ⋆ H₃) := star.assoc H₁ H₂ H₃\n" ++
          "def t2 (H₁ H₂ : HProp Nat) : H₁ ⋆ H₂ = H₂ ⋆ H₁ := star.comm H₁ H₂\n" ++
          "def t3 (H : HProp Nat) : emp ⋆ H = H := star.emp_l H\n" ++
          "def t4 (H₁ H₂ H₃ : HProp Nat) : (H₁ ⋆ H₂) ⋆ H₃ ⊢ H₃ ⋆ (H₂ ⋆ H₁) :=\n" ++
          "  Entails.trans (star.comm_entails (H₁ ⋆ H₂) H₃) (star.mono_r H₃ (star.comm_entails H₁ H₂))") },
    { name := "the frame property and the wand adjunction", run := fun _ =>
        okLibs ("import HProp\n" ++
          "def t1 (H₁ H₁' H₂ : HProp Nat) (m : H₁ ⊢ H₁') : H₁ ⋆ H₂ ⊢ H₁' ⋆ H₂ := star.mono_l H₂ m\n" ++
          "def t2 (H₁ H₂ H₃ : HProp Nat) : (H₁ ⋆ H₂ ⊢ H₃) ↔ (H₁ ⊢ H₂ −∗ H₃) := wand.adjoint H₁ H₂ H₃\n" ++
          "def t3 (H₁ H₂ : HProp Nat) : H₁ ⋆ (H₁ −∗ H₂) ⊢ H₂ := wand.cancel H₁ H₂\n" ++
          "def t4 : (1 ↦ 5) ⋆ (1 ↦ 6) ⊢ @hpure Nat False := pts.same_loc 1 5 6") },
    { name := "a law that doesn't hold has no proof", run := fun _ => do
        -- (small ones: a wrong law about `⋆` is rejected too, but only after minutes of
        -- unfolding; wishful slow-failing-unification)
        failsLibs "import HProp\ndef bad : (1 ↦ 5) ⊢ (1 ↦ 6) := Entails.refl (1 ↦ 5)" "mismatch"
        failsLibs "import HProp\ndef bad : @emp Nat ⊢ hpure False := Entails.refl emp" "mismatch" },
    { name := "wp is a monotone, frame-preserving monad morphism; the triple rules", run := fun _ =>
        okLibs ("import Hoare\n" ++
          "def t1 (c : Prog Nat Nat) (f : Nat → Prog Nat Nat) : wp (Prog.bind c f) = W.bind (wp c) (fun a => wp (f a)) := wp.bind c f\n" ++
          "def t2 (c : Prog Nat Nat) : W.Frame (wp c) := wp.frame c\n" ++
          "def t3 (P H : HProp Nat) (c : Prog Nat Nat) (Q : Nat → HProp Nat) (t : Triple P c Q) :\n" ++
          "  Triple (P ⋆ H) c (fun a => Q a ⋆ H) := Triple.frame H t\n" ++
          "def t4 (l : Nat) : Triple (l ↦ 1) (Prog.bind (Prog.read l) (fun v => Prog.write l (Nat.succ v))) (fun _ => l ↦ 2) :=\n" ++
          "  Triple.bind (Triple.read l 1) (fun r => Triple.pure (fun e =>\n" ++
          "    @Eq.substProp Nat (fun (x : Nat) => Triple (l ↦ 1) (Prog.write l (Nat.succ x)) (fun _ => l ↦ 2)) 1 r (Eq.symm e) (Triple.write l 2 1)))") },
    { name := "swap and in-place list reversal are verified", run := fun _ =>
        okLibs ("import Hoare\n#check @Prog.swap_spec\n#check @Prog.reverse_spec")
          ["Prog.swap_spec : (p : Nat) → (q : Nat) → (a : Nat) → (b : Nat) → Triple Nat Unit (star Nat (pts Nat p a) (pts Nat q b)) (Prog.swap p q) (fun _ => star Nat (pts Nat p b) (pts Nat q a))",
           "Prog.reverse_spec : (L : List Nat) → (fuel : Nat) → (p : Nat) → Nat.lt (List.length Nat L) fuel = .true → Triple Nat Nat (MList L p) (Prog.reverse fuel p) (fun r => MList (List.reverse Nat L) r)"] },
    { name := "a faulting program has no triple from a satisfiable precondition", run := fun _ =>
        failsLibs ("import Hoare\ndef bad : Triple (@emp Nat) (@Prog.fail Nat Unit) (fun (_ : Unit) => @emp Nat) :=\n" ++
          "  Triple.ret () (fun (_ : Unit) => @emp Nat)") "mismatch" },
    { name := "the programs run on concrete heaps, as adequacy says", run := fun _ =>
        okLibs ("import Hoare\n" ++
          "#eval Prog.show (Prog.swap 1 2) (Heap.ofList (.cons 10 (.cons 20 .nil)) 1) 3 3\n" ++
          -- the list 1, 2, 3 in cells at 1, 3, 5
          "#eval Prog.show (Prog.reverse 10 1) (Heap.ofList (.cons 1 (.cons 3 (.cons 2 (.cons 5 (.cons 3 (.cons 0 .nil)))))) 1) 7 7\n" ++
          "#eval Prog.show (Prog.reverse 2 1) (Heap.ofList (.cons 1 (.cons 3 (.cons 2 (.cons 5 (.cons 3 (.cons 0 .nil)))))) 1) 7 7\n" ++
          "#eval Prog.show (Prog.bind (Prog.ref 7) (fun l => Prog.read l)) Heap.empty 0 2")
          [".some ((), .cons .none (.cons (.some 20) (.cons (.some 10) .nil)))",
           -- reversed: the cell at 5 (value 3) points to 3 (value 2), which points to 1 (value 1)
           ".some (5, .cons .none (.cons (.some 1) (.cons (.some 0) (.cons (.some 2) (.cons (.some 1) (.cons (.some 3) (.cons (.some 3) .nil)))))))",
           -- not enough fuel: a fault
           ".none", ".some (7, .cons (.some 7) (.cons .none .nil))"] }
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
        let s := runFrontend (R := ZeroOneMany) src { loader := ← preludeLoader, trustedModule := Tests.libModule }
        match s.messages.toList.map (·.text) with
        | [a, b, c, d] =>
          checkEq (b.replace "unbox0" "unbox") a
          checkEq (d.replace "Pos0" "Pos") c
        | ms => throw (IO.userError s!"unexpected messages {ms}") },
    { name := "the surface Desc.arg takes a field only in exactly its universe", run := fun _ =>
        failsLib "import Prelude\ndef D : Desc Unit := Desc.arg 1 True (fun _ => Desc.ret ())" "type mismatch" }
  ]

/-! ## Equality of descriptions (4g) -/

/-- Small data types without the Prelude. -/
def descEqTypes : String :=
  "inductive N where\n  | z\n  | s (n : N)\n" ++
  "inductive B where\n  | f\n  | t\n" ++
  "inductive L (A : Type) where\n  | nil\n  | cons (x : A) (xs : L A)\n" ++
  "def len {A : Type} : L A → N\n  | .nil => .z\n  | .cons _ xs => .s (len xs)\n"

/-- The Abel–Coquand program with the box cast between two *different* descriptions
(`BoxD` and `BoxD'`, whose tags differ in name), along a proof of the computed equation
built by hand from `tautext`. -/
def abelCoquandTwoBoxes : String :=
  ((abelCoquand).replace
    "def omega : Top := fun A a => unbox (cast (apTy Prop Box T2 A (tautext T2 A id2 a)) (mk delta))\n"
    ("def BoxD' (P : Prop) : Desc Unit := Desc.arg 1 ((_ : Enum [v]) × P) (fun _ => Desc.ret ())\n" ++
     "def Box' (P : Prop) : Type := μ (BoxD' P) ()\n" ++
     "def unbox' {P : Prop} (b : Box' P) : P := ind (fun _ _ => P) (fun i xs ih => xs.1.2) b\n" ++
     "def boxEq : Box T2 = Box' T2 := ((), (((), fun _ => (fun _ => id2, fun _ => id2)), fun _ => ()), ())\n" ++
     "def omega : Top := fun A a => unbox' (cast (apTy Prop Box' T2 A (tautext T2 A id2 a)) (cast boxEq (mk delta) : Box' T2))\n"))

def descEqGroup : Group where
  name := "desceq"
  exercise := "Equality of descriptions (4g)"
  cases := [
    { name := "List Nat = List Bool computes through the codes, and gives Nat = Bool", run := fun _ =>
        ok (descEqTypes ++ "#reduce L N = L B\n")
          ["(0 e : True) × (0 e' : (0 e' : True) × ((0 x : Enum [nil, cons]) → cast (transp (fun y _ => (0 e'' : Unit = y) × ((0 x' : Desc Unit) → Unit = y)) (refl (Desc Unit × Unit)) e).1 (ecase x [Desc.ret (), Desc.arg ω N (fun x' => Desc.rec ω () (Desc.ret ()))]) = ecase x [Desc.ret (), Desc.arg ω B (fun x' => Desc.rec ω () (Desc.ret ()))])) × True"] },
    { name := "List Nat = List Bool is refutable (at the tag cons, Nat = Bool; at succ, rec against ret)", run := fun _ =>
        ok (descEqTypes ++ "def refute (e : L N = L B) : Empty := absurd (((e.2.1.2 'cons).1).2.1.2 's)\n") },
    { name := "List A = List C contains A = C (the cons field's equation)", run := fun _ =>
        ok (descEqTypes ++ "def ac (A C : Type) (e : L A = L C) (P : Type → Type) (p : P A) (q : (0 _ : A = C) → P A → P C) : P C :=\n" ++
          "  q (e.2.1.2 'cons).1 p\n") },
    { name := "UIntN 8 = UIntN 16 is refutable (the phantom is in the index type)", run := fun _ =>
        okLib ("import Prelude\ninductive UIntN (w : Nat) where\n  | mk (toNat : Nat)\n" ++
          "def ne (e : UIntN 8 = UIntN 16) : Empty := absurd ((e.1.1.2 16).1 (refl 16))\n") },
    { name := "casts between List A and List C compute, element by element", run := fun _ =>
        ok (descEqTypes ++
          "def lenCast (A C : Type) (h : L A = L C) (x y : A) : len (cast h (L.cons x (L.cons y L.nil)) : L C) = N.s (N.s N.z) := rfl\n" ++
          "def nilCast (A C : Type) (h : L A = L C) : (cast h (L.nil : L A) : L C) = L.nil := rfl\n" ++
          "def numCast (h : L N = L N) : (cast h (L.cons N.z L.nil) : L N) = L.cons N.z L.nil := rfl\n") },
    { name := "a cast at a variable element type stays a cast (no regularity)", run := fun _ =>
        fails (descEqTypes ++
          "def reg (A C : Type) (h : L A = L C) (x : A) (y : C) : (cast h (L.cons x L.nil) : L C) = L.cons y L.nil := rfl\n") "rfl: the two sides are not definitionally equal" },
    { name := "reflexivity: refl T proves T = T for a data type; i = i' alone does not", run := fun _ => do
        ok (descEqTypes ++ "def r (A : Type) : L A = L A := refl (L A)\n")
        fails (descEqTypes ++
          "inductive V (A : Type) : N → Type where\n  | nil : V A .z\n  | cons {0 n : N} (x : A) (xs : V A n) : V A (.s n)\n" ++
          "def bad (A : Type) (n m : N) (h : n = m) : V A n = V A m := h\n") "type mismatch" },
    -- (soundness-audit) `rfl : T = T` at a data type: the equation of the codes has a part
    -- `(t : Enum ls) → …` that is stuck under the binder; `rfl` proves it tag by tag
    { name := "rfl proves T = T for data types: N, an indexed family, a coinductive type", run := fun _ =>
        ok (descEqTypes ++
          "inductive V (A : Type) : N → Type where\n  | nil : V A .z\n  | cons {0 n : N} (x : A) (xs : V A n) : V A (.s n)\n" ++
          "coinductive S (A : Type) where\n  head : A\n  tail : S A\n" ++
          "def r1 : N = N := rfl\n" ++
          "def r2 (A : Type) : L A = L A := rfl\n" ++
          "def r3 (A : Type) (n : N) : V A n = V A n := rfl\n" ++
          "def r4 (A : Type) : S A = S A := rfl\n" ++
          "def c1 (n : N) : (cast (rfl : N = N) n : N) = n := rfl\n" ++
          "def c2 (A : Type) (l : L A) : L A := cast (rfl : L A = L A) l\n") },
    { name := "rfl proves T = T with the Prelude: Bool, Nat, List A, Option A, a structure", run := fun _ =>
        okLib ("import Prelude\nstructure Pt where\n  x : Nat\n  y : Bool\n" ++
          "def r1 : Bool = Bool := rfl\ndef r2 : Nat = Nat := rfl\n" ++
          "def r3 (A : Type) : List A = List A := rfl\ndef r4 (A : Type) : Option A = Option A := rfl\n" ++
          "def r5 : Pt = Pt := rfl\n") },
    { name := "an un-ascribed cast between two data types asks for an ascription (the equation computed)", run := fun _ => do
        fails (descEqTypes ++ "#check fun (A C : Type) (h : L A = L C) (l : L A) => cast h l\n") "has computed"
        ok (descEqTypes ++ "def f (A C : Type) (h : L A = L C) (l : L A) : N := len (cast h l : L C)\n") },
    { name := "rfl still can't prove an equation between different data types", run := fun _ =>
        fails (descEqTypes ++ "def bad : L N = L B := rfl\n") "rfl" },
    { name := "different description constructors are unequal; quantities count", run := fun _ =>
        ok ("#reduce (Desc.ret () : Desc Unit) = Desc.rec 1 () (Desc.ret ())\n" ++
          "#reduce (Desc.rec 1 () (Desc.ret ()) : Desc Unit) = Desc.rec 0 () (Desc.ret ())\n" ++
          "#reduce (Desc.rec 1 () (Desc.ret ()) : Desc Unit) = Desc.rec 1 () (Desc.ret ())\n")
          ["False", "False", "(0 _ : True) × True"] },
    { name := "a quantity variable against a literal at an arg field is stuck too", run := fun _ =>
        ok ("#reduce fun (q : Qty) => (Desc.arg q Unit (fun _ => Desc.ret ()) : Desc Unit) = Desc.arg 1 Unit (fun _ => Desc.ret ())\n")
          ["fun q => Desc.arg q Unit (fun _ => Desc.ret ()) = Desc.arg 1 Unit (fun _ => Desc.ret ())"] },
    { name := "sizes compare as conversion does: μ^{↑∞} ≡ μ^∞ computes like μ^∞ ≡ μ^∞", run := fun _ => do
        let g : Globals ZeroOneMany := {}
        let mu (s : Val ZeroOneMany) : Val ZeroOneMany := .mu 0 (.unit 1) (.dret .tt) .tt s none
        let q (v : Val ZeroOneMany) : Term ZeroOneMany := quote g 0 v
        let inf := q (vEqType g (mu .szInf) (mu .szInf))
        check (match inf with | .eqTy .. => false | _ => true) "μ^∞ ≡ μ^∞ should compute"
        check (inf == q (vEqType g (mu (.szSuc .szInf)) (mu .szInf))) "μ^{↑∞} ≡ μ^∞ should compute like μ^∞ ≡ μ^∞" },
    { name := "a quantity variable against a literal is not unequal (stuck: substituting can make them equal)", run := fun _ =>
        ok ("#reduce fun (q : Qty) => (Desc.rec q () (Desc.ret ()) : Desc Unit) = Desc.rec 1 () (Desc.ret ())\n")
          ["fun q => Desc.rec q () (Desc.ret ()) = Desc.rec 1 () (Desc.ret ())"] },
    -- the Desc analogue of wiz-notes/qty-false-probe.wiz (F6): if the equation computed to
    -- `False`, `bad 1 (refl _)` would be a closed proof of `False`
    { name := "a quantity variable against a literal does not prove False (rec and arg)", run := fun _ => do
        fails "def bad (q : Qty) (e : (Desc.rec q () (Desc.ret ()) : Desc Unit) = Desc.rec 1 () (Desc.ret ())) : False := e\n" "type mismatch"
        fails "def bad (q : Qty) (e : (Desc.arg q Unit (fun _ => Desc.ret ()) : Desc Unit) = Desc.arg 1 Unit (fun _ => Desc.ret ())) : False := e\n" "type mismatch" },
    { name := "lifted proof fields compare by equivalence, not by shape", run := fun _ =>
        okLib ("import Prelude\ninductive PB (P : Prop) where\n  | mk (p : P)\n" ++
          "def pbne (e : PB True = PB False) : Empty := absurd ((e.2.1.2 'mk).1.1 ())\n") },
    -- Hur-style: injectivity of μ in its description must not inject `Type → Prop` into `Type`
    { name := "Hur-style: a description over Type at level 0 is rejected (fields are exactly in Sort (l+1))", run := fun _ =>
        fails ("def HT (F : Type → Prop) : Desc Unit := Desc.arg 1 Type (fun X => Desc.ret ())\n") "universe level mismatch" },
    { name := "Hur-style: over Prop at level 0 it is allowed; injectivity gives the lifted propositions' equation", run := fun _ =>
        okLib ("import Prelude\ninductive H (F : Prop → Prop) where\n  | mk (P : Prop) (p : F P)\n" ++
          "#reduce fun (F G : Prop → Prop) (e : H F = H G) (P : Prop) => ((e.2.1.2 'mk).2 P).1\n")
          ["fun F G e P => ((e.2.1.2 'mk).2 P).1"] },
    { name := "D1 (Abel–Coquand) with two different box descriptions: checks", run := fun _ => do
        unless (abelCoquandTwoBoxes.splitOn "boxEq").length > 2 do throw (IO.userError "variant not built")
        ok abelCoquandTwoBoxes },
    -- with regularity on, the cast between the two descriptions is still structural (they
    -- are not syntactically equal), so it applies `boxEq`'s equivalence: `id2`, no loop
    { name := "D1 (Abel–Coquand) with two different box descriptions: checks with regularity too", run := fun _ =>
        okWith .full abelCoquandTwoBoxes }
  ]

def phantomGroup : Group where
  name := "phantom"
  exercise := "Phantom parameters"
  cases := [
    { name := "UIntN 8 and UIntN 16 are different types", run := fun _ =>
        failsLib "import Prelude\ninductive UIntN (w : Nat) where\n  | mk (toNat : Nat)\ndef f (x : UIntN 8) : UIntN 16 := x" "mismatch" },
    { name := "so rfl can't prove UIntN 8 = UIntN 16", run := fun _ =>
        failsLib "import Prelude\ninductive UIntN (w : Nat) where\n  | mk (toNat : Nat)\ndef e : UIntN 8 = UIntN 16 := rfl" "mismatch" },
    { name := "μ equality: UIntN 8 = UIntN 8 holds, UIntN 8 = UIntN 16 is refutable (4g)", run := fun _ => do
        -- equality of μ types compares the codes (4g): the phantom is in the index type,
        -- whose equation is `e.1`, and at the phantom it is `(x = 16) ↔ (x = 8)`
        let ty := "import Prelude\ninductive UIntN (w : Nat) where\n  | mk (toNat : Nat)\n"
        okLib (ty ++ "def same : UIntN 8 = UIntN 8 := refl (UIntN 8)")
        okLib (ty ++ "def ne (e : UIntN 8 = UIntN 16) : Empty := absurd ((e.1.1.2 16).1 (refl 16))")
        failsLib (ty ++ "def bad : UIntN 8 = UIntN 16 := refl (UIntN 8)") "mismatch" },
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
          let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
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
    { name := "structures: every pair is a pair; with --unbox-structs the last field is unboxed (22i)", run := fun _ => do
        let src := "import Prelude\nstructure W where\n  val : List Nat\nstructure P (w : Nat) where\n  x : Nat\n  y : List Nat\n" ++
          "def w : W := W.mk (List.cons 1 List.nil)\ndef l : List Nat := List.cons 1 List.nil\n" ++
          "def p : P 3 := P.mk 2 (List.cons 1 List.nil)\ndef q : Nat × List Nat × Unit := (2, List.cons 1 List.nil, ())\n" ++
          "def unW (v : W) : List Nat := v.val\ndef swap (v : P 3) : P 3 := (v.x, v.y, ())\n" ++
          "#eval w\n#run w\n#run p\n#eval swap p\n#run swap p\n" ++
          "def wl : List W := List.cons w List.nil\n#run wl\n"
        for unbox in [false, true] do
          let s := runFrontend (R := ZeroOneMany) src
            { trustedModule := Tests.libModule, loader := ← preludeLoader, globals := { unboxStructs := unbox } }
          let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
          unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
          -- the values read back the same in both layouts
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
          let l ← allocs "l"
          -- unboxed: `W` is its list, and `P` is one pair, as a raw `Nat × List Nat × Unit`
          -- is two; else one cell per field
          let k := if unbox then 0 else 1
          checkEq (unbox, l + k, l + 1 + k, l + 2) (unbox, ← allocs "w", ← allocs "p", ← allocs "q") }
  ]

/-! ### Representations are a function of the type up to conversion (R3)

`wiz-notes/repr-shape.md`. A value keeps its bits when it is converted to an equal type,
or passed to generic code, so erasure may choose a representation only by what conversion
(and substitution) can see: never by a binder name, an `Enum` label or the display name
on a `μ`. -/

/-- `#eval main`, `#run main` (the IR interpreter), and `main` compiled by the C and the
LLVM backends all give `expected`. `unbox`: with `--unbox-structs`. -/
def reprAll (src expected : String) (unbox : Bool := false) (libs : Bool := false) : IO Unit := do
  let full := src ++ "\n#eval main\n#run main\n"
  let loader ← if libs then libLoader else preludeLoader
  let s := runFrontend (R := ZeroOneMany) full
    { trustedModule := Tests.libModule, loader, globals := { unboxStructs := unbox } }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render full
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq [expected, expected] (s.messages.toList.map (·.text))
  for llvm in [false, true] do
    let dir ← IO.FS.createTempDir
    match ← Build.runGlobal (← toolchain) s "main" dir llvm with
    | .ok v => checkEq expected v
    | .error e =>
      let missing := ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1
      if missing then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)

/-- The audit's probe: a hand-written Σ of a structure's shape, converted both ways. -/
def r3Marker : String := "import Prelude
structure S where
  val : Nat
def toS (p : (val : Nat) × ((0 f : Enum [x]) → Unit)) : S := p
def ofS (s : S) : (val : Nat) × ((0 f : Enum [x]) → Unit) := s
def main : Nat := (toS (5, fun _ => ())).val + 10 * (ofS (S.mk 7)).1
"

/-- A structure's phantom tail, at a type that calls it a function, applied. -/
def r3PhantomTail : String := "import Prelude
structure P (n : Nat) where
  val : Nat
def tailOf (p : P 3) : (0 d : (0 x : Nat) × (x = 3)) → (0 f : Enum [q]) → Unit := p.2
def useT (t : (0 d : (0 x : Nat) × (x = 3)) → (0 f : Enum [q]) → Unit) : Unit := t (3, rfl) 'q
def keep (u : Unit) : Nat := 9
def main : Nat := keep (useT (tailOf (P.mk 4)))
"

/-- … and applied by generic code, which knows nothing of the tail. -/
def r3PhantomGeneric : String := "import Prelude
structure P (n : Nat) where
  val : Nat
def app0 {D A : Type} (0 d : D) (f : (0 _ : D) → A) : A := f d
def tailU (p : P 3) : (0 f : Enum [q]) → Unit := app0 (D := (0 x : Nat) × (x = 3)) (3, rfl) p.2
def keep (u : Unit) : Nat := 9
def main : Nat := keep (tailU (P.mk 4) 'q)
"

/-- Generic code over pairs, used at a structure: unification puts the structure's tail
in the type variable `B`. -/
def r3Generic : String := "import Prelude
structure S where
  val : Nat
def first {A : Type} {B : Type} (p : A × B) : A := p.1
def mk2 {A : Type} {B : Type} (a : A) (b : B) : A × B := (a, b)
def s2 : S := mk2 7 (S.mk 1).2
def main : Nat := first (S.mk 5) + 10 * s2.val
"

/-- A Σ whose second component is a function into `Unit` only for some first components. -/
def r3Dependent : String := "import Prelude
def T (b : Bool) : Type := match b with
  | .true => (0 f : Enum [x]) → Unit
  | .false => Nat
def p : (b : Bool) × T b := (.true, fun _ => ())
def q : (b : Bool) × T b := (.false, 7)
def isT (q : (b : Bool) × T b) : Nat := match q.1 with
  | .true => 1
  | .false => 0
def main : Nat := isT p + 10 * isT q
"

/-- A copy of `Nat`'s declaration is convertible to `Nat`. -/
def r3NatCopy : String := "import Prelude
inductive MyNat where
  | zero
  | succ (n : MyNat)
def ofNat (n : Nat) : MyNat := n
def toNat (n : MyNat) : Nat := n
def count : MyNat → Nat
  | .zero => 0
  | .succ n => count n + 1
def main : Nat := count (ofNat 3) + 10 * (toNat (.succ (.succ .zero)) + 1)
"

/-- A proof-valued function applied by code that is generic in the sort. -/
def r3SortPoly : String := "import Prelude
def app.{u} {A : Sort u} (f : Nat → A) : A := f 0
def keep.{u} {A : Sort u} (f : Nat → A) : Nat := let x := app f; 4
def main : Nat := keep (A := 0 = 0) (fun _ => rfl)
"

/-- A description built by a function that abstracts its first field's type, used at an
`Enum`: code at the known type takes the tag from the object, the generic eliminator
would follow the description's run-time mark, which says there is none. -/
def r3DescMark : String := "import Prelude
def mkD (S : Type) (F : S → Desc Unit) : Desc Unit := Desc.arg 1 S F
def B2 : Type := μ (mkD (Enum [a, b]) (fun _ => Desc.ret ())) ()
def tb : B2 := con ('b, (), ())
def isB2 (x : B2) : Nat := ind (fun _ _ => Nat) (fun i xs ih => let h := ih; ecase xs.1 [0, 1]) x
def main : Nat := isB2 tb
"

/-- A pair of proofs projected by code that is generic in the sorts of its components. -/
def r3SortPolyPair : String := "import Prelude
def sndP.{u, v} {A : Sort u} {B : Sort v} (p : A × B) : B := p.2
def keep.{u, v} {A : Sort u} {B : Sort v} (p : A × B) : Nat := let x := sndP p; 4
def main : Nat := keep (A := 0 = 0) (B := 1 = 1) (rfl, rfl)
"

/-- Structures of 1 to 3 fields, with and without a phantom parameter, each with the Σ of
its shape written by hand: values converted back and forth, read through the structure's
projections and through the raw ones. Returns the program and the value of `main`. -/
def r3RoundTrips : String × Nat := Id.run do
  let mut src := "import Prelude\ndef lsum : List Nat → Nat\n  | .nil => 0\n  | .cons x xs => x + lsum xs\n"
  let mut total := 0
  let mut terms : List String := []
  let mut k := 0
  for nf in [1, 2, 3] do
    for phantom in [false, true] do
      k := k + 1
      -- field `i` is a `Nat` (even `i`) or a `List Nat` (odd `i`), with the value `v i`
      let v (i : Nat) : Nat := 3 * k + 5 * i + 1
      let isList (i : Nat) : Bool := i % 2 == 1
      let fty (i : Nat) : String := if isList i then "List Nat" else "Nat"
      let lit (i : Nat) : String := if isList i then s!"(List.cons {v i} (List.cons 1 List.nil))" else s!"{v i}"
      let rd (i : Nat) (e : String) : String := if isList i then s!"lsum ({e})" else e
      let (ps, arg) := if phantom then (" (w : Nat)", " 3") else ("", "")
      let tail := if phantom then "((0 d : (0 x : Nat) × (x = 3)) → (0 f : Enum [q]) → Unit)" else "((0 f : Enum [q]) → Unit)"
      let tailV := if phantom then "(fun _ _ => ())" else "(fun _ => ())"
      let fields := List.range nf
      src := src ++ s!"structure S{k}{ps} where\n" ++ String.join (fields.map fun i => s!"  f{i} : {fty i}\n")
      src := src ++ s!"def H{k} : Type := " ++ String.join (fields.map fun i => s!"(f{i} : {fty i}) × ") ++ tail ++ "\n"
      src := src ++ s!"def to{k} (h : H{k}) : S{k}{arg} := h\ndef of{k} (s : S{k}{arg}) : H{k} := s\n"
      -- the weighted sum of the fields, through the structure's projections and the raw ones
      let viaS := " + ".intercalate (fields.map fun i => s!"{i + 1} * {rd i s!"s.f{i}"}")
      let raw (i : Nat) : String := "h" ++ String.join (List.replicate i ".2") ++ ".1"
      let viaH := " + ".intercalate (fields.map fun i => s!"{i + 1} * {rd i (raw i)}")
      src := src ++ s!"def sumS{k} (s : S{k}{arg}) : Nat := {viaS}\ndef sumH{k} (h : H{k}) : Nat := {viaH}\n"
      src := src ++ s!"def s{k} : S{k}{arg} := S{k}.mk {" ".intercalate (fields.map lit)}\n"
      src := src ++ s!"def h{k} : H{k} := ({", ".intercalate (fields.map lit)}, {tailV})\n"
      let w := fields.foldl (fun acc i => acc + (i + 1) * (v i + (if isList i then 1 else 0))) 0
      let checks := [s!"sumS{k} (to{k} h{k})", s!"sumH{k} (of{k} s{k})", s!"sumS{k} (to{k} (of{k} (to{k} (of{k} s{k}))))",
        s!"sumH{k} (of{k} (to{k} h{k}))", s!"sumS{k} s{k}", s!"sumH{k} h{k}"]
      for c in checks, j in [0:checks.length] do
        terms := terms ++ [s!"{j + 1} * {c}"]
        total := total + (j + 1) * w
  src := src ++ "def main : Nat := " ++ " + ".intercalate terms ++ "\n"
  pure (src, total)

def reprGroup : Group where
  name := "repr"
  exercise := "Representations and conversion (R3)"
  cases := [
    { name := "R3: a hand-written Σ of a structure's shape converts to the structure and back", run := fun _ =>
        reprAll r3Marker "75" },
    { name := "… and with --unbox-structs", run := fun _ => reprAll r3Marker "75" (unbox := true) },
    { name := "R3: a phantom tail at a type that calls it a function is applied (compiled too)", run := fun _ =>
        reprAll r3PhantomTail "9" },
    { name := "… and applied by generic code: ◾ applied is ◾", run := fun _ => do
        reprAll r3PhantomGeneric "9"
        reprAll r3PhantomGeneric "9" (unbox := true) },
    { name := "generic code over pairs, used at a structure (substitution)", run := fun _ =>
        reprAll r3Generic "75" },
    { name := "a Σ whose second component depends on the first is always a pair", run := fun _ => do
        reprAll r3Dependent "1"
        reprAll r3Dependent "1" (unbox := true) },
    { name := "a copy of Nat's declaration is convertible to Nat, and is a number too", run := fun _ =>
        reprAll r3NatCopy "33" },
    { name := "a proof-valued function applied by code generic in the sort", run := fun _ =>
        reprAll r3SortPoly "4" },
    { name := "a pair of proofs projected by code generic in the sorts: a projection of ◾ is ◾", run := fun _ =>
        reprAll r3SortPolyPair "4" },
    { name := "a description whose first field has an abstract type is refused, not miscompiled", run := fun _ => do
        failsLib (r3DescMark ++ "#eval main\n") "cannot compile a description"
        let s := runFrontend (R := ZeroOneMany) r3DescMark { trustedModule := Tests.libModule, loader := ← preludeLoader }
        match Build.cProgram s "main" with
        | .ok _ => throw (IO.userError "it compiled")
        | .error e => check ((e.splitOn "cannot compile a description").length > 1) e
        -- a parameterised type's own fields are not first fields: `List A` compiles
        reprAll "import Prelude\ndef len {A : Type} : List A → Nat\n  | .nil => 0\n  | .cons _ xs => len xs + 1\ndef main : Nat := len (List.cons 'a (List.cons 'b List.nil) : List (Enum [a, b]))\n" "2" },
    { name := "two runs in one process with different options don't share a module's state", run := fun _ => do
        let loader ← preludeLoader
        let run (g : Globals ZeroOneMany) : Globals ZeroOneMany :=
          (runFrontend (R := ZeroOneMany) "import Prelude\n" { trustedModule := Tests.libModule, loader, globals := g }).globals
        check (!(run {}).unboxStructs) "the default unboxes"
        check (run { unboxStructs := true }).unboxStructs "unboxStructs was lost"
        check (!(run {}).unboxStructs) "unboxStructs leaked"
        check ((run { inertReg := .syntactic }).inertReg == .syntactic) "inertReg := syntactic was lost"
        check ((run { inertReg := .conv }).inertReg == .conv) "inertReg := conv was lost"
        check ((run {}).inertReg == .ground) "inertReg leaked"
        check ((run { predicativeProp := true }).predicativeProp) "predicativeProp was lost"
        check (!(run {}).predicativeProp) "predicativeProp leaked"
        check (!(run { lazyProofs := false }).lazyProofs) "lazyProofs := false was lost"
        check ((run {}).lazyProofs) "lazyProofs leaked" },
    { name := "structures and the Σ of their shape: values converted back and forth", run := fun _ => do
        let (src, total) := r3RoundTrips
        reprAll src (toString total)
        reprAll src (toString total) (unbox := true) }
  ]

/-- A user-declared `ShareLet` (no HDL library): the hook fires on a `let` in check mode
with no explicit quantity, and only when an instance exists. -/
def shareLetHook : String := "import Prelude
structure W where
  n : Nat
class ShareLet (A B : Type) where
  share : A → (A → B) → B
instance : ShareLet W W where
  share := fun x f => f (W.mk (x.n + 100))
def t1 : W := let y := W.mk 1; y
def t2 : W := let ω y := W.mk 1; y
def t3 : Nat := let y := 1; y
#eval t1.n
#eval t2.n
#eval t3
"

/-- Circuits whose Verilog the `hdl` group looks at: a counter (non-zero initial value), a
64-bit state (an initial value above 2^32) and a circuit with an input and a pair state. -/
def hdlVerilogSrc : String := "import Hdl.Core
def u8 : HwTy := HwTy.bits 8
def c1 : Circuit (HwTy.bits 1) u8 := Circuit.mk u8 (BitVec.ofNat 8 250) (fun s u => Hw.pair (Hw.add s (Hw.lit 8 1)) s)
def v1 : String := Verilog.emit (Circuit.netlist \"counter\" c1)
def u64 : HwTy := HwTy.bits 64
def c2 : Circuit u8 u64 := Circuit.mk u64 (BitVec.ofNat 64 13835062455471964160) (fun s x => Hw.pair (Hw.add s (Hw.lit 64 1)) s)
def v2 : String := Verilog.emit (Circuit.netlist \"wide\" c2)
def c3 : Circuit u8 u8 := Circuit.mk (HwTy.prod u8 u8) (BitVec.ofNat 8 1, BitVec.ofNat 8 2)
  (fun s x => Hw.pair (Hw.pair x (Hw.fst s)) (Hw.mux (Hw.ult x (Hw.snd s)) (Hw.fst s) (Hw.sub x (Hw.snd s))))
def v3 : String := Verilog.emit (Circuit.netlist \"pairs\" c3)
"

def hdlGroup : Group where
  name := "hdl"
  exercise := "HDL stage S0 (hdl-plan H14)"
  cases := [
    { name := "auto-share: a let becomes ShareLet.share when an instance exists", run := fun _ =>
        okLibs shareLetHook ["101", "1", "1"] },
    { name := "L2 examples: hash-consed netlists are no bigger, three simulations agree; the doubling chain is linear", run := fun _ => do
        -- r1–r4: (nodes hash-consed, nodes naive), then the value simulation and the netlist
        -- simulations (hash-consed, naive). q1: the chain at k = 20 (nodes, adders, builder
        -- work). q2: the chain at k = 3 simulated. q3: the chain without sharing (`let ω`) at
        -- k = 10 (nodes, work, naive nodes). Last: (x + y) * (y + x) has one adder.
        okLibs (← IO.FS.readFile "examples/hdl.wiz") ["((4, 4), .cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 .nil))))), .cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 .nil))))), .cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 .nil))))))", "((7, 7), .cons 250 (.cons 251 (.cons 252 (.cons 253 (.cons 254 (.cons 255 .nil))))), .cons 250 (.cons 251 (.cons 252 (.cons 253 (.cons 254 (.cons 255 .nil))))), .cons 250 (.cons 251 (.cons 252 (.cons 253 (.cons 254 (.cons 255 .nil))))))", "((28, 35), .cons 1 (.cons 1 (.cons 2 (.cons 1 (.cons 3 (.cons 3 .nil))))), .cons 1 (.cons 1 (.cons 2 (.cons 1 (.cons 3 (.cons 3 .nil))))), .cons 1 (.cons 1 (.cons 2 (.cons 1 (.cons 3 (.cons 3 .nil))))))", "((8, 9), .cons 1 (.cons 4 (.cons 9 (.cons 15 (.cons 216 (.cons 162 .nil))))), .cons 1 (.cons 4 (.cons 9 (.cons 15 (.cons 216 (.cons 162 .nil))))), .cons 1 (.cons 4 (.cons 9 (.cons 15 (.cons 216 (.cons 162 .nil))))))", "(22, 20, 22)", "(.cons 8 (.cons 16 (.cons 24 (.cons 32 (.cons 64 (.cons 56 .nil))))), .cons 8 (.cons 16 (.cons 24 (.cons 32 (.cons 64 (.cons 56 .nil))))))", "(11, 2047, 2047)", "4"] },
    { name := "auto-share elaborates an object let to ShareLet.share; an erased or meta let stays a let", run := fun _ =>
        okLibs ("import Hdl.Core\ndef f {r : HwTy → Type} [Hw r] (x : r (HwTy.bits 8)) : r (HwTy.bits 8) := let y := Hw.add x x; Hw.add y y\n" ++
          "def g {r : HwTy → Type} [Hw r] (x : r (HwTy.bits 8)) (k : Nat) : r (HwTy.bits 8) := let j := Nat.succ k; Hw.lit 8 j\n#erase f\n#erase g")
          ["f := (λr. (λinst✝. (λx. (((((ShareLet.share ◾) ◾) ((((instShareLetRARB ◾) #1) ⟨0 8⟩) ⟨0 8⟩)) (((((Hw.add ◾) #1) 8) #0) #0)) (λy. (((((Hw.add ◾) #2) 8) #0) #0))))))",
           "g := (λr. (λinst✝. (λx. (λk. (let j := (Nat.succ #0); ((((Hw.lit ◾) #3) 8) #0))))))"] },
    { name := "Verilog: declarations before use (regs, wires, then the updates), sized initial values", run := fun _ =>
        okLibs (hdlVerilogSrc ++ "#eval v1\n")
          ["\"module counter(input clk, input [0:0] x, output [7:0] y);\\n  reg [7:0] r; initial r = 8'd250;\\n  wire [7:0] n3 = r + 8'd1;\\n  always @(posedge clk) r <= n3;\\n  assign y = r;\\nendmodule\\n\""] },
    { name := "S1: bundles, composition, reset and enable at random cycles; netlist simulation = values; names, test bench, PCF, VCD", run := fun _ => do
        -- t1–t6: (agreement of the netlist simulations with `Circuit.run`, the netlist size
        -- and the outputs) for the bundled counter, a delay chain, `par`, a feedback loop,
        -- two instances, and reset and enable driven at random cycles; then the counter's
        -- Verilog (named ports and registers, `if (rst) … else if (en)`), pin constraints,
        -- the problems of a bad pin list, a waveform, and the sizes of a list of designs
        okLibs (← IO.FS.readFile "examples/hdl-compose.wiz")
          ["(.true, .cons 17 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 4 (.cons 6 (.cons 8 (.cons 8 (.cons 10 (.cons 10 (.cons 10 (.cons 12 (.cons 14 (.cons 14 (.cons 14 (.cons 16 (.cons 19 (.cons 16 (.cons 14 (.cons 12 (.cons 12 (.cons 12 (.cons 12 (.cons 10 (.cons 8 (.cons 6 (.cons 6 (.cons 4 (.cons 2 .nil)))))))))))))))))))))))))))))))",
           "(.true, .cons 5 (.cons 9 (.cons 7 (.cons 0 (.cons 0 (.cons 140 (.cons 173 (.cons 172 (.cons 30 (.cons 11 (.cons 226 (.cons 250 (.cons 211 .nil)))))))))))))",
           "(.true, .cons 9 (.cons 2389 (.cons 1798 (.cons 150 (.cons 40 (.cons 17709 (.cons 24795 (.cons 35041 (.cons 43032 .nil)))))))))",
           "(.true, .cons 4 (.cons 1 (.cons 1 (.cons 26 (.cons 128 (.cons 123 (.cons 250 (.cons 41 (.cons 185 .nil)))))))))",
           "(.true, .cons 29 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 .nil)))))))))))))))))))))))))))))))))))))))))",
           "(.true, .cons 19 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 2 (.cons 0 (.cons 0 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))",
           "\"module counter(input clk, input [0:0] rst, input [0:0] en, input [0:0] go, output [3:0] leds, output [0:0] top);\\n  reg [3:0] count; initial count = 4'd0;\\n  reg [0:0] up; initial up = 1'd1;\\n  wire [3:0] n6 = count + 4'd1;\\n  wire [3:0] n7 = count - 4'd1;\\n  wire [3:0] n8 = up ? n6 : n7;\\n  wire [3:0] next = go ? n8 : count;\\n  wire [0:0] n11 = next == 4'd9;\\n  wire [0:0] n13 = next == 4'd0;\\n  wire [0:0] n16 = n13 ? 1'd1 : up;\\n  wire [0:0] n17 = n11 ? 1'd0 : n16;\\n  wire [0:0] n18 = count == 4'd9;\\n  always @(posedge clk) if (rst) count <= 4'd0; else if (en) count <= next;\\n  always @(posedge clk) if (rst) up <= 1'd1; else if (en) up <= n17;\\n  assign leds = count;\\n  assign top = n18;\\nendmodule\\n\"",
           "\"set_io clk 21\\nset_io rst 1\\nset_io en 2\\nset_io go 3\\nset_io leds[0] 99\\nset_io leds[1] 98\\nset_io leds[2] 97\\nset_io leds[3] 96\\nset_io top 95\\n\"",
           ".cons \"no pin for port rst\" (.cons \"no pin for port en\" (.cons \"port leds has 4 bits, one pin given\" (.cons \"no pin for port top\" (.cons \"pin for no port: led\" .nil))))",
           "\"$timescale 1ns $end\\n$scope module counter $end\\n$var wire 1 ! clk $end\\n$var wire 1 \\\" go $end\\n$var wire 4 # leds $end\\n$var wire 1 $ top $end\\n$var wire 4 % count $end\\n$var wire 1 & up $end\\n$upscope $end\\n$enddefinitions $end\\n#0\\n0!\\n0\\\"\\nb0000 #\\n0$\\nb0000 %\\n1&\\n#1\\n1!\\n#2\\n0!\\n#3\\n1!\\n#4\\n0!\\n#5\\n1!\\n#6\\n0!\\n1\\\"\\n#7\\n1!\\n#8\\n\"",
           ".cons 17 (.cons 5 (.cons 4 .nil))"] },
    { name := "Verilog: Icarus Verilog accepts the emitted modules (skipped without iverilog on PATH)", run := fun _ => do
        let found ← (do let o ← IO.Process.output { cmd := "iverilog", args := #["-V"] }; pure (o.exitCode == 0)) <|> pure false
        unless found do IO.println "    (no iverilog: skipped)"; return
        let s := runFrontend (R := ZeroOneMany) (hdlVerilogSrc ++ "#eval v1\n#eval v2\n#eval v3\n")
          { trustedModule := Tests.libModule, loader := ← libLoader }
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render ""
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {errs}")
        IO.FS.withTempDir fun dir => do
          for m in s.messages.toList, i in [0:3] do
            -- the message is the string as `#eval` prints it: quoted, newlines escaped
            let text := ((m.text.drop 1).dropRight 1).replace "\\n" "\n"
            let file := dir / s!"m{i}.v"
            IO.FS.writeFile file text
            let o ← IO.Process.output { cmd := "iverilog", args := #["-g2005", "-o", (dir / "out.vvp").toString, file.toString] }
            unless o.exitCode == 0 do throw (IO.userError s!"iverilog rejects module {i}:\n{o.stderr}\n{text}")
        -- the composed circuits, and the generated test bench replaying the counter with
        -- reset and enable at random cycles against its value simulation
        let src ← IO.FS.readFile "examples/hdl-compose.wiz"
        let s := runFrontend (R := ZeroOneMany) (src ++ "\n#eval vCounter\n#eval vTwo\n#eval vPipe\n#eval tbCounter\n#eval vecCounter\n")
          { trustedModule := Tests.libModule, loader := ← libLoader }
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render ""
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {errs}")
        let texts := (s.messages.toList.map (·.text)).drop 11
        let unq (t : String) : String := ((t.drop 1).dropRight 1).replace "\\n" "\n" |>.replace "\\\"" "\""
        IO.FS.withTempDir fun dir => do
          let names := ["counter.v", "two.v", "pipe.v", "tb.v", "counter.vec"]
          for t in texts, nm in names do IO.FS.writeFile (dir / nm) (unq t)
          for nm in ["two.v", "pipe.v"] do
            let o ← IO.Process.output { cmd := "iverilog", args := #["-g2005", "-o", (dir / "x.vvp").toString, (dir / nm).toString] }
            unless o.exitCode == 0 do throw (IO.userError s!"iverilog rejects {nm}:\n{o.stderr}")
          let o ← IO.Process.output { cmd := "iverilog", args := #["-g2005", "-o", (dir / "tb.vvp").toString, (dir / "tb.v").toString, (dir / "counter.v").toString], cwd := dir }
          unless o.exitCode == 0 do throw (IO.userError s!"iverilog rejects the test bench:\n{o.stderr}")
          let r ← IO.Process.output { cmd := "vvp", args := #["-n", (dir / "tb.vvp").toString], cwd := dir }
          unless (r.stdout.splitOn "PASS counter: 60 cycles").length > 1 do
            throw (IO.userError s!"test bench: {r.stdout}{r.stderr}") }
  ]

/-! ## Regions: borrow checking as typing (lib/Region.wiz, Rust DSL RD12) -/

def regionsPush : String :=
  "def push1 {ρ : Region} (v : Uniq ρ (List Nat)) : Result (Unit × Uniq ρ (List Nat)) :=\n  .ok ((), Uniq.set v (List.cons 1 v.val))\n"
def regionsLongest : String :=
  "def longest {ρa ρb : Region} (0 h : Outlives ρa ρb) (x : Shr ρa Nat) (y : Shr ρb Nat) : Result (Shr ρb Nat) :=\n" ++
  "  match Nat.lt x.val y.val with\n  | .true => .ok y\n  | .false => .ok (Shr.weaken h x)\n"

/-- The front end's state for `src`, with every library importable. -/
def libsState (src : String) (unbox : Bool := false) : IO (CommandState ZeroOneMany) := do
  let s := runFrontend (R := ZeroOneMany) src
    { trustedModule := Tests.libModule, loader := ← libLoader, globals := { unboxStructs := unbox } }
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
          "def forge {ρ : Region} : Shr ρ Nat := MyShr.mk 5") "mismatch"
        -- nor through an equation with a look-alike (the kernel compares by shape; `rfl`
        -- compares in the elaborator's view)
        failsLibs ("import Region\nstructure MyShr (ρ : Region) (A : Type) where\n  val : A\n" ++
          "def forge {ρ : Region} (x : Nat) : Shr ρ Nat := cast rfl (MyShr.mk x : MyShr ρ Nat)") "not definitionally equal" },
    { name := "with --unbox-structs a handle is its value at run time; a scope is its body run in place (22i)", run := fun _ => do
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
          "#run Shr.borrow Region.static 4 (fun ρ h x => .ok (get x))") (unbox := true)
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


/-! ## 25: concurrency (runtime/wiz.c threads, lib/Session.wiz, lib/MVar.wiz) -/

/-- The dependent protocol of docs/stages/25-concurrency.md: send a length `n`, then `n`
numbers, receive their sum; the server and client as pure processes and over channels. -/
def concSum : String := "import IO
import Session
def sendMany (k : Proto) : Nat → Proto
  | .zero => k
  | .succ n => .send Nat (fun _ => sendMany k n)
def ack : Proto := .recv Nat (fun _ => .done)
def sumProto : Proto := .send Nat (fun n => sendMany ack n)
def nums : (n : Nat) → Proc Nat (sendMany ack n)
  | .zero => fun s => s
  | .succ n => (n + 1, nums n)
def client (m : Nat) : Proc Nat sumProto := (m, nums m)
def serverMany : (n : Nat) → (acc : Nat) → Proc Unit (Proto.dual (sendMany ack n))
  | .zero, acc => (acc, ())
  | .succ n, acc => fun x => serverMany n (acc + x)
def server : Proc Unit (Proto.dual sumProto) := fun n => serverMany n 0
def serveMany : (n : Nat) → (acc : Nat) → (1 c : Chan (Proto.dual (sendMany ack n))) → IO Unit
  | .zero, acc => fun c => Chan.send c acc (fun c' => Chan.close c' (IO.pure ()))
  | .succ n, acc => fun c =>
      Chan.recv c (fun x c' => serveMany n (acc + x) c')
def serve (1 c : Chan (Proto.dual sumProto)) : IO Unit :=
  Chan.recv c (fun n c' => serveMany n 0 c')
def sendNums : (n : Nat) → (1 c : Chan (sendMany ack n)) → IO Nat
  | .zero => fun c => Chan.recv c (fun s c' => Chan.close c' (IO.pure s))
  | .succ n => fun c => Chan.send c (n + 1) (fun c' => sendNums n c')
def runClient (m : Nat) (1 c : Chan sumProto) : IO Nat :=
  Chan.send c m (fun c' => sendNums m c')
"

/-- A chain of threads: each adds one to every element of a list and passes it on; the
last sums, and the sum travels back up. -/
def concChain : String := "import IO
import Session
def Q : Proto := .send (List Nat) (fun _ => .recv Nat (fun _ => .done))
def bump : List Nat → List Nat
  | .nil => .nil
  | .cons x xs => .cons (x + 1) (bump xs)
def total : List Nat → Nat
  | .nil => 0
  | .cons x xs => x + total xs
def upto : Nat → List Nat
  | .zero => .nil
  | .succ n => .cons n (upto n)
def stage : Nat → (1 c : Chan (Proto.dual Q)) → IO Unit
  | .zero => fun c => Chan.recv c (fun xs c' =>
      Chan.send c' (total xs) (fun c'' => Chan.close c'' (IO.pure ())))
  | .succ n => fun c => Chan.recv c (fun xs c' =>
      Chan.fork Q (stage n) (fun d => Chan.send d (bump xs) (fun d' =>
        Chan.recv d' (fun s d'' => Chan.close d''
          (Chan.send c' s (fun c'' => Chan.close c'' (IO.pure ())))))))
def shared : List Nat := upto 100
def main : IO Unit := Chan.fork Q (stage 50) (fun d =>
  Chan.send d shared (fun d' => Chan.recv d' (fun s d'' =>
    Chan.close d'' (IO.bind (IO.println (Nat.toString s)) (fun _ => IO.println (Nat.toString (total shared)))))))
"

/-- A cancellable protocol (decision CS13): up to `n` numbers, each one a value or a
cancel. -/
def concCancel : String := "import IO
import Session
def items : Nat → Proto
  | .zero => .done
  | .succ n => Proto.sendC Nat (fun _ => items n)
def onMsg (n acc : Nat) (serve : (acc : Nat) → (1 c : Chan (Proto.dual (items n))) → IO Unit) :
    (m : Msg Nat) → (1 c : Chan (Proto.dual (Msg.next (fun _ => items n) m))) → IO Unit
  | .val x => fun c => serve (acc + x) c
  | .cancel => fun c => Chan.close c (IO.println (String.append \"cancelled after \" (Nat.toString acc)))
def serveItems : (n : Nat) → (acc : Nat) → (1 c : Chan (Proto.dual (items n))) → IO Unit
  | .zero, acc => fun c => Chan.close c (IO.println (String.append \"all: \" (Nat.toString acc)))
  | .succ n, acc => fun c =>
      Chan.recv c (fun m c' => onMsg n acc (serveItems n) m c')
def client (1 c : Chan (items 3)) : IO Unit :=
  Chan.send c (.val 10) (fun c1 =>
    Chan.send c1 (.val 20) (fun c2 =>
      Chan.cancel c2 (IO.pure ())))
def full (1 c : Chan (items 2)) : IO Unit :=
  Chan.send c (.val 1) (fun c1 =>
    Chan.send c1 (.val 2) (fun c2 => Chan.close c2 (IO.pure ())))
def main : IO Unit := Chan.fork (items 3) (serveItems 3 0) (fun c => client c)
"

/-- Eight threads bump one counter a thousand times each (MVar.modify: the linear
borrow/fill discipline), under a lock, and report through an MVar. -/
def concCounter : String := "import IO
import Session
import MVar
def worker (m : MVar Nat) (l : Lock) : Nat → IO Unit
  | .zero => IO.pure ()
  | .succ n => IO.bind (MVar.modify m (fun x => x + 1)) (fun _ =>
      IO.bind (Lock.with l (IO.pure ())) (fun _ => worker m l n))
def spawnN (m : MVar Nat) (l : Lock) (done : MVar Nat) : Nat → IO Unit
  | .zero => IO.pure ()
  | .succ k => Chan.fork Proto.done (fun c => Chan.close c (IO.bind (worker m l 1000) (fun _ => MVar.put done 1)))
      (fun c => Chan.close c (spawnN m l done k))
def waitN (done : MVar Nat) : Nat → IO Unit
  | .zero => IO.pure ()
  | .succ k => IO.bind (MVar.take done) (fun _ => waitN done k)
def main : IO Unit := do1
  m ← MVar.newFull 0;
  l ← Lock.new;
  done ← MVar.new (A := Nat);
  spawnN m l done 8;
  waitN done 8;
  n ← MVar.take m;
  IO.println (Nat.toString n)
"

/-- Two threads observe one lazy stream (shared lazy cells are not overwritten, 25a). -/
def concStream : String := "import IO
import Session
import MVar
coinductive Stream (A : Type) where
  head : A
  tail : Stream A
def natsFrom (n : Nat) : Stream Nat
  | .head => n
  | .tail => natsFrom (n + 1)
def sumN : Nat → Stream Nat → Nat
  | .zero, _ => 0
  | .succ k, s => s.head + sumN k s.tail
def main : IO Unit := IO.bind (MVar.new (A := Nat)) (fun r =>
  let s := natsFrom 0;
  Chan.fork Proto.done (fun c => Chan.close c (MVar.put r (sumN 2000 s)))
    (fun c => Chan.close c (IO.bind (MVar.take r) (fun a =>
      IO.println (Nat.toString (a + sumN 2000 s))))))
"

def concGroup : Group where
  name := "conc"
  exercise := "lib/Session.wiz, lib/MVar.wiz, runtime threads (stage 25)"
  cases := [
    { name := "a dependent protocol: the pure semantics `link` runs it", run := fun _ =>
        okLibs (concSum ++ "#eval (link sumProto (client 100) server).1") ["5050"] },
    { name := "the same protocol over a channel, server in a new thread", run := fun _ =>
        cRunLibs (concSum ++ "def main : IO Unit := Chan.fork sumProto serve (fun c =>\n" ++
          "  IO.bind (runClient 1000 c) (fun s => IO.println (Nat.toString s)))") "500500\n" },
    { name := "Proc.runLinked: the model is `link`, compiled code runs threads (differential)", run := fun _ => do
        okLibs (concSum ++ "#eval (link sumProto (client 300) server).1") ["45150"]
        cRunLibs (concSum ++ "def main : IO Unit := IO.bind (Proc.runLinked sumProto (client 300) server)\n" ++
          "  (fun r => IO.println (Nat.toString r.1))") "45150\n" },
    { name := "a chain of 51 threads; endpoints move into children", run := fun _ =>
        cRunLibs concChain "9950\n4950\n" },
    { name := "cancellation is a branch of the protocol", run := fun _ => do
        cRunLibs concCancel "cancelled after 30\n"
        cRunLibs (concCancel.replace "def main : IO Unit := Chan.fork (items 3) (serveItems 3 0) (fun c => client c)" "" ++
          "def main : IO Unit := Chan.fork (items 2) (serveItems 2 0) (fun c => full c)") "all: 3\n" },
    { name := "MVars and locks: eight threads, one counter", run := fun _ =>
        cRunLibs concCounter "8000\n" },
    { name := "a lazy stream shared between threads", run := fun _ =>
        cRunLibs concStream "3998000\n" },
    { name := "an endpoint can't be used twice, dropped, or closed twice", run := fun _ => do
        failsLibs (concSum ++ "def twice (1 c : Chan sumProto) : IO Nat :=\n" ++
          "  Chan.send c 1 (fun c' => runClient 1 c)") "quantity 1"
        failsLibs "import IO\nimport Session\ndef leak (1 c : Chan Proto.done) : IO Unit := IO.pure ()" "quantity 1"
        failsLibs "import IO\nimport Session\ndef dupe (1 c : Chan Proto.done) : IO Unit := Chan.close c (Chan.close c (IO.pure ()))" "quantity 1" },
    { name := "a closure that captured an endpoint is linear itself", run := fun _ =>
        failsLibs ("import IO\nimport Session\n" ++
          "def capture (1 c : Chan Proto.done) : Unit → IO Unit := fun _ => Chan.close c (IO.pure ())\n" ++
          "def dupf (1 c : Chan Proto.done) : IO Unit := let f := capture c; IO.bind (f ()) (fun _ => f ())") "quantity" },
    { name := "the protocol is checked: wrong message type, wrong step", run := fun _ => do
        failsLibs (concSum ++ "def bad (1 c : Chan sumProto) : IO Unit :=\n" ++
          "  Chan.send c Bool.true (fun c' => Chan.close c' (IO.pure ()))") "mismatch"
        failsLibs (concSum ++ "def bad (1 c : Chan sumProto) : IO Unit := Chan.close c (IO.pure ())") "mismatch" },
    { name := "endpoints can't be forged, retyped, sent, or stored", run := fun _ => do
        failsLibs "import IO\nimport Session\ndef bad (1 c : Chan Proto.done) : Chan (.send Nat (fun _ => .done)) := c" "mismatch"
        failsLibs ("import IO\nimport Session\ndef bad (1 c : Chan (.send Nat (fun _ => .done))) : IO (Chan (.recv Nat (fun _ => .done))) :=\n" ++
          "  Chan.sendRaw c 1") "private"
        -- an endpoint is not a message (no delegation: the channel graph stays a forest)
        failsLibs ("import IO\nimport Session\ndef bad (1 c : Chan (.send (Chan Proto.done) (fun _ => .done))) (1 d : Chan Proto.done) : IO Unit :=\n" ++
          "  Chan.send c d (fun c' => Chan.close c' (IO.pure ()))") "quantity 1"
        failsLibs ("import IO\nimport Session\nimport MVar\ndef bad (m : MVar (Chan Proto.done)) (1 d : Chan Proto.done) : IO Unit :=\n" ++
          "  MVar.put m d") "quantity 1" },
    { name := "a lock guard and an MVar hole must be given back exactly once", run := fun _ => do
        failsLibs "import IO\nimport MVar\ndef bad (l : Lock) : IO Unit := Lock.acquire l (fun g => IO.pure ())" "quantity 1"
        failsLibs ("import IO\nimport MVar\ndef bad {B : Type} (l : Lock) (b : B) : IO B :=\n" ++
          "  Lock.acquire l (fun g => Lock.release l g (Lock.release l g (IO.pure b)))") "quantity 1"
        failsLibs "import IO\nimport MVar\ndef bad (m : MVar Nat) : IO Nat := MVar.borrow m (fun a h => IO.pure a)" "quantity 1"
        failsLibs "import IO\nimport MVar\ndef forge (l : Lock) : IO (Lock.Guard l) := Lock.acquireRaw l" "private" }
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
  let s := runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule }
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
    { name := "the messages of the tactic at the cursor (trace, trace_state), under the goals", run := fun _ =>
        okInfoview (goalPrelude ++ "#eval Infoview.plainLines (View.lines (View.ofTacState 30 (.some (.mk (.cons g .nil) (.cons \"hello\" (.cons \"n : Nat\\n⊢ Nat\" .nil)))) .none))\n" ++
          "#eval Infoview.htmlTacState 0 (.some (.mk .nil (.cons \"a<b\" .nil))) .none\n" ++
          "def msgsOf : TacView → List String\n  | .mk _ ms => ms\n" ++
          "#eval match Json.parse \"{\\\"goals\\\": [], \\\"messages\\\": [\\\"one\\\", \\\"two\\\"]}\" with\n  | .ok j => msgsOf (TacView.ofJson j)\n  | .error e => List.cons e List.nil")
          [r#".cons "Tactic state" (.cons "A : Type" (.cons "f : Nat → Nat → Nat → Nat" (.cons "⊢ Nat → A" (.cons "" (.cons "Messages" (.cons "hello" (.cons "" (.cons "n : Nat" (.cons "⊢ Nat" .nil)))))))))"#,
           r#""<h3>Tactic state</h3><div class=\"no-goals\">No goals</div><h3>Messages</h3><pre class=\"message\">a&lt;b</pre>""#,
           r#".cons "one" (.cons "two" .nil)"#] },
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

/-- This module's test groups, which `Tests/Main.lean` runs: one per line, in sorted
order, so that branches adding groups rarely touch the same lines. A new group also
needs a shard in `.github/test-shards.json` (CI checks). -/
def groups : List Group :=
  backendGroup ::
  borrowGroup ::
  builtinGroup ::
  cGroup ::
  callbacksGroup ::
  classGroup ::
  coinductiveGroup ::
  concGroup ::
  dataGroup ::
  descEqGroup ::
  derivingGroup ::
  effectsGroup ::
  ffiGroup ::
  ffiStructGroup ::
  group ::
  hdlGroup ::
  inductiveGroup ::
  infoviewGroup ::
  languageGroup ::
  levelGroup ::
  liftGroup ::
  llvmGroup ::
  macroGroup ::
  matchGroup ::
  opticGroup ::
  ottGroup ::
  phantomGroup ::
  qtyGroup ::
  regionsGroup ::
  reprGroup ::
  reuseGroup ::
  runGroup ::
  selfHostGroup ::
  seplogicGroup ::
  sizedGroup ::
  stdGroup ::
  structGroup ::
  sysGroup ::
  tacticGroup ::
  toolingGroup ::
  trustGroup ::
  vecGroup ::
  wordGroup ::
  []

end Tests.Elab
