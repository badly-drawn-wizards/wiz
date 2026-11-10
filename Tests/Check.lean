import Wiz
import Tests.Harness

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

open Wiz Raw ZeroOneMany

namespace Tests.Check

/-- Expect a list of declarations to check. -/
def accepts {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R] (ds : List (Decl R)) : IO Unit :=
  match addDecls {} ds with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"rejected: {e}")

/-- Expect the *last* declaration to be rejected, with an error satisfying `p`.
All earlier declarations must check. -/
def rejects {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]
    (ds : List (Decl R)) (p : TypeError → Bool) (what : String) : IO Unit := do
  let g ← match addDecls {} ds.dropLast with
    | .ok g => pure g
    | .error e => throw (IO.userError s!"setup declaration rejected: {e}")
  match addDecl g ds.getLast! with
  | .ok _ => throw (IO.userError s!"accepted, but expected {what}")
  | .error e => unless p e do throw (IO.userError s!"expected {what}, got: {e}")

def isMismatch : TypeError → Bool | .typeMismatch .. => true | _ => false
def isQty : TypeError → Bool | .quantityMismatch .. => true | _ => false

/-! ## Plain dependent types (`Unit` rig) -/

/-- `Nat = (A : Type) → (A → A) → A → A`. Lives in `Type 1`. -/
def natTy : Raw Unit := pi' "A" () ty (arr () (arr () "A" "A") (arr () "A" "A"))
def church (n : Nat) : Raw Unit :=
  lams ["A", "s", "z"] ((List.range n).foldl (fun acc _ => .app "s" acc) "z")

def churchDecls : List (Decl Unit) := [
  Raw.defn "Nat" (.sort 1) natTy,
  Raw.defn "zero" "Nat" (church 0),
  Raw.defn "succ" (arr () "Nat" "Nat")
    (lams ["n", "A", "s", "z"] (.app "s" (apps "n" ["A", "s", "z"]))),
  Raw.defn "add" (arr () "Nat" (arr () "Nat" "Nat"))
    (lams ["m", "n", "A", "s", "z"] (apps "m" ["A", "s", apps "n" ["A", "s", "z"]])),
  Raw.defn "two" "Nat" (apps "succ" [apps "succ" ["zero"]]),
  Raw.defn "four" "Nat" (church 4)
]

/-- `Eq` à la Leibniz, so we can state `2 + 2 = 4` and prove it by `refl`:
type checking it requires `add two two` and `four` to be convertible. -/
def leibnizDecls : List (Decl Unit) := [
  Raw.defn "Eq" (arr () "Nat" (arr () "Nat" (.sort 2)))
    (lams ["x", "y"] (pi' "P" () (arr () "Nat" (.sort 1)) (arr () (.app "P" "x") (.app "P" "y")))),
  Raw.defn "refl" (pi' "x" () "Nat" (apps "Eq" ["x", "x"])) (lams ["x", "P", "px"] "px")
]

def mlttGroup : Group where
  name := "check: dependent types"
  exercise := "Exercises 1.5–1.7"
  cases := [
    { name := "id : (A : Type) → A → A",
      run := fun _ => accepts [Raw.defn "id" (pi' "A" () ty (arr () "A" "A")) (lams ["A", "x"] "x")] },
    { name := "compose",
      run := fun _ => accepts [Raw.defn "comp"
        (pi' "A" () ty (pi' "B" () ty (pi' "C" () ty
          (arr () (arr () "B" "C") (arr () (arr () "A" "B") (arr () "A" "C"))))))
        (lams ["A", "B", "C", "g", "f", "x"] (.app "g" (.app "f" "x")))] },
    { name := "Church numerals", run := fun _ => accepts churchDecls },
    -- (audit 2) an index beyond the context used to panic and go on with `Sort 0`, as the
    -- variable's type and as its value: a term `Prop : Prop`
    { name := "a variable out of scope is rejected",
      run := fun _ => do
        let outOfScope : TypeError → Bool
          | .other m => (m.splitOn "out of scope").length > 1
          | _ => false
        let d (ty : Term Unit) (v : Option (Term Unit)) : Decl Unit := { name := "d", type := ty, value := v }
        let fnTy : Term Unit := Term.pi "x" .default (.qlit ()) (.sort 1) (.sort 0) none
        rejects [d (.sort 0) (some (.var 0))] outOfScope "an out-of-scope variable"
        rejects [d fnTy (some (.lam "x" (.var 3)))] outOfScope "an out-of-scope variable"
        rejects [d (.var 2) none] outOfScope "an out-of-scope variable" },
    { name := "refl : 2 + 2 = 4 (needs conversion)",
      run := fun _ => accepts (churchDecls ++ leibnizDecls ++
        [Raw.defn "twoPlusTwo" (apps "Eq" [apps "add" ["two", "two"], "four"]) (.app "refl" "four")]) },
    { name := "refl : 2 + 2 = 2 is rejected",
      run := fun _ => rejects (churchDecls ++ leibnizDecls ++
        [Raw.defn "bad" (apps "Eq" [apps "add" ["two", "two"], "two"]) (.app "refl" "two")])
        isMismatch "a type mismatch" },
    { name := "let in check mode",
      run := fun _ => accepts [Raw.defn "k" (pi' "A" () ty (arr () "A" "A"))
        (lams ["A", "x"] (.letE "y" () "A" "x" "y"))] },
    { name := "annotation lets a lambda be applied",
      run := fun _ => accepts [Raw.defn "t" (arr () ty ty)
        (lams ["A"] (.app (.ann (lams ["B"] "B") (arr () ty ty)) "A"))] },
    { name := "Type : Type is rejected",
      run := fun _ => rejects (R := Unit) [Raw.defn "girard" ty ty] isMismatch "a type mismatch" },
    { name := "wrong body type is rejected",
      run := fun _ => rejects [Raw.defn "bad" (pi' "A" () ty (arr () "A" "A")) (lams ["A", "x"] "A")]
        isMismatch "a type mismatch" },
    { name := "unbound global is reported",
      run := fun _ => rejects (R := Unit) [Raw.defn "bad" ty "Nope"]
        (· == .unboundGlobal "Nope") "unboundGlobal" },
    { name := "applying a non-function is rejected",
      run := fun _ => rejects [Raw.defn "bad" (pi' "A" () ty (arr () "A" "A"))
        (lams ["A", "x"] (.app "x" "x"))] (fun | .notAFunction .. => true | _ => false)
        "notAFunction" },
    { name := "bare lambda cannot be inferred",
      run := fun _ => rejects (R := Unit) [Raw.defn "bad" ty (.app (lams ["x"] "x") ty)]
        (fun | .cannotInfer .. => true | _ => false) "cannotInfer" }
  ]

/-! ## Methods in a rig without ω (Q2) -/

/-- In the `Nat` rig (exact counting) there is no unrestricted quantity, so a method of
an eliminator, which runs once per node, may not use a runtime variable. Here `coit`'s
step uses `y`: `bad` declares `y` linear (rejected: each `out` reruns the step), `good`
declares it erased and the step only passes it to an erased argument. -/
def natRigCoit (q : Nat) (name : Name) : List (Decl Nat) :=
  let pi (x : Name) (q : Nat) (a b : Term Nat) : Term Nat := .pi x .default (.qlit q) a b none
  let U : Term Nat := .unit 1
  let D : Term Nat := .dret .tt
  -- a global state family: `fun _ => Unit` would drop its linear argument
  let S : Term Nat := .const s!"{name}S" []
  -- ⟦ret tt⟧ S i = (0 _ : tt = i) × Unit
  let stepTy := pi "i" 1 U (pi "s" 1 (.app S (.var 0)) (pi "y" q U (.sigma "_" (.qlit 0) (.eq U .tt (.var 2)) (.unit 1) none)))
  [{ name := s!"{name}S", type := pi "i" 1 U (.sort 1), value := none },
   { name := s!"{name}S0", type := .app S .tt, value := none },
   { name := s!"{name}Step", type := stepTy, value := none },
   { name, type := pi "y" q U (.nu 0 U D .tt .szInf none),
     value := some (.lam "y" (.coit 0 U D S
       (.lam "i" (.lam "s" (.app (.app (.app (.const s!"{name}Step" []) (.var 1)) (.var 0)) (.var 2)))) .tt (.const s!"{name}S0" []))) }]

/-! ## Quantities (`ZeroOneMany` rig) -/

abbrev Q := ZeroOneMany

/-- `(A :0 Type) → body` -/
def forallA (body : Raw Q) : Raw Q := pi' "A" zero ty body

def qttGroup : Group where
  name := "check: quantities"
  exercise := "Exercises 0.1, 1.5–1.7"
  cases := [
    { name := "linear identity: (A :0 Type) → (x :1 A) → A",
      run := fun _ => accepts [Raw.defn "id" (forallA (arr one "A" "A")) (lams ["A", "x"] "x")] },
    { name := "erased variable used in a type only",
      run := fun _ => accepts [Raw.defn "id" (forallA (pi' "x" one "A" "A")) (lams ["A", "x"] "x")] },
    { name := "erased variable used at runtime is rejected",
      run := fun _ => rejects [Raw.defn "bad" (forallA (arr zero "A" "A")) (lams ["A", "x"] "x")]
        isQty "a quantity error" },
    { name := "linear variable used twice is rejected",
      run := fun _ => rejects [Raw.defn "dup"
        (forallA (arr many (arr many "A" (arr many "A" "A")) (arr one "A" "A")))
        (lams ["A", "f", "x"] (apps "f" ["x", "x"]))] isQty "a quantity error" },
    { name := "linear variable dropped is rejected",
      run := fun _ => rejects [Raw.defn "drop" (forallA (arr one "A" (arr one "A" "A")))
        (lams ["A", "x", "y"] "x")] isQty "a quantity error" },
    { name := "ω variable used once is fine",
      run := fun _ => accepts [Raw.defn "app1" (forallA (arr one (arr one "A" "A") (arr many "A" "A")))
        (lams ["A", "f", "x"] (.app "f" "x"))] },
    { name := "ω variable used twice is fine",
      run := fun _ => accepts [Raw.defn "twice" (forallA (arr one (arr many "A" (arr many "A" "A")) (arr many "A" "A")))
        (lams ["A", "f", "x"] (apps "f" ["x", "x"]))] },
    { name := "passing a linear var to an ω argument is rejected (scaling)",
      run := fun _ => rejects [Raw.defn "bad" (forallA (arr one (arr many "A" "A") (arr one "A" "A")))
        (lams ["A", "f", "x"] (.app "f" "x"))] isQty "a quantity error" },
    { name := "passing a linear var to an erased argument drops it",
      run := fun _ => rejects [Raw.defn "bad" (forallA (arr many (arr zero "A" "A") (arr one "A" "A")))
        (lams ["A", "f", "x"] (.app "f" "x"))] isQty "a quantity error" },
    { name := "erased var can be passed to an erased argument",
      run := fun _ => accepts [Raw.defn "ok" (forallA (arr one (arr zero "A" "A") (arr zero "A" "A")))
        (lams ["A", "f", "x"] (.app "f" "x"))] },
    { name := "linear let",
      run := fun _ => accepts [Raw.defn "l" (forallA (arr one "A" "A"))
        (lams ["A", "x"] (.letE "y" one "A" "x" "y"))] },
    { name := "unused linear let is rejected",
      run := fun _ => rejects [Raw.defn "l" (forallA (arr one "A" (arr one "A" "A")))
        (lams ["A", "x", "z"] (.letE "y" one "A" "x" "z"))] isQty "a quantity error" },
    { name := "erased let feeding a type",
      run := fun _ => accepts [Raw.defn "l" (forallA (arr one "A" "A"))
        (lams ["A", "x"] (.letE "B" zero ty "A" (.ann "x" "B")))] },
    { name := "Nat rig: a method may use an erased variable", run := fun _ => accepts (natRigCoit 0 "good") },
    { name := "Nat rig: a method may not use a linear variable, it runs any number of times (Q2)", run := fun _ =>
        rejects (natRigCoit 1 "bad") (fun | .other .. => true | _ => false) "a method usage error" }
  ]

/-! ## Structural types -/

def structGroup : Group where
  name := "check: structural types"
  exercise := "Exercise 4.7"
  cases := [
    { name := "swap with projections", run := fun _ =>
        accepts [Raw.defn "swap" (pi' "A" () ty (pi' "B" () ty (arr () (.sigma "_" () "A" "B") (.sigma "_" () "B" "A"))))
          (lams ["A", "B", "p"] (.pair (.snd "p") (.fst "p")))] },
    { name := "Σ lives in the larger universe", run := fun _ =>
        accepts [Raw.defn "S" (.sort 1) (.sigma "A" () ty "A")] },
    { name := "linear swap with let (x, y) := p", run := fun _ =>
        accepts [Raw.defn "swap" (forallA (pi' "B" zero ty (arr one (.sigma "x" one "A" "B") (.sigma "y" one "B" "A"))))
          (lams ["A", "B", "p"] (.split one "p" "z" (.sigma "y" one "B" "A") "x" "y" (.pair "y" "x")))] },
    { name := "linear pair projected twice is rejected", run := fun _ =>
        rejects [Raw.defn "swap" (forallA (pi' "B" zero ty (arr one (.sigma "x" one "A" "B") (.sigma "y" one "B" "A"))))
          (lams ["A", "B", "p"] (.pair (.snd "p") (.fst "p")))]
          (fun e => isQty e || match e with | .other .. => true | _ => false) "a quantity or projection error" },
    { name := "erased field cannot be projected", run := fun _ =>
        rejects [Raw.defn "bad" (forallA (pi' "B" zero ty (arr many (.sigma "x" zero "A" "B") "A")))
          (lams ["A", "B", "p"] (.fst "p"))] (fun | .other .. => true | _ => false) "a projection error" },
    { name := "the second projection can't drop a linear first field (Q1)", run := fun _ =>
        rejects [Raw.defn "drop" (forallA (pi' "B" zero ty (arr one (.sigma "x" one "A" "B") "B")))
          (lams ["A", "B", "p"] (.snd "p"))] isQty "a quantity error" },
    { name := "an unrestricted pair may drop its linear first field (Q1)", run := fun _ =>
        accepts [Raw.defn "dropMany" (forallA (pi' "B" zero ty (arr many (.sigma "x" one "A" "B") "B")))
          (lams ["A", "B", "p"] (.snd "p"))] },
    { name := "the first projection can't drop a linear field in the second part (Q1)", run := fun _ =>
        rejects [Raw.defn "dropFst" (forallA (pi' "B" zero ty (arr one (.sigma "x" many "A" (.sigma "y" one "B" "B")) "A")))
          (lams ["A", "B", "p"] (.fst "p"))] isQty "a quantity error" },
    { name := "an unrestricted pair may drop a linear field in its second part (Q1)", run := fun _ =>
        accepts [Raw.defn "dropFstMany" (forallA (pi' "B" zero ty (arr many (.sigma "x" many "A" (.sigma "y" one "B" "B")) "A")))
          (lams ["A", "B", "p"] (.fst "p"))] },
    { name := "the first projection may drop a second part without linear fields", run := fun _ =>
        accepts [Raw.defn "fstω" (forallA (pi' "B" zero ty (arr one (.sigma "x" one "A" (.sigma "y" many "B" "B")) "A")))
            (lams ["A", "B", "p"] (.fst "p")),
          Raw.defn "fst0" (forallA (pi' "B" zero ty (arr one (.sigma "x" one "A" (.sigma "y" zero "B" "B")) "A")))
            (lams ["A", "B", "p"] (.fst "p"))] },
    { name := "projecting a linear field out of the middle of a linear tuple is rejected (Q1)", run := fun _ =>
        rejects [Raw.defn "mid" (forallA (pi' "B" zero ty (arr one (.sigma "x" many "A" (.sigma "y" one "B" (.sigma "z" one "B" "B"))) "B")))
          (lams ["A", "B", "p"] (.fst (.snd "p")))] isQty "a quantity error" },
    { name := "the second projection may drop an ω or erased first field", run := fun _ =>
        accepts [Raw.defn "dropω" (forallA (pi' "B" zero ty (arr one (.sigma "x" many "A" "B") "B")))
            (lams ["A", "B", "p"] (.snd "p")),
          Raw.defn "drop0" (forallA (pi' "B" zero ty (arr one (.sigma "x" zero "A" "B") "B")))
            (lams ["A", "B", "p"] (.snd "p"))] },
    { name := "erased field can be bound by split and ignored", run := fun _ =>
        accepts [Raw.defn "ok" (forallA (pi' "B" zero ty (arr one (.sigma "x" zero "A" "B") "B")))
          (lams ["A", "B", "p"] (.split one "p" "z" "B" "x" "y" "y"))] },
    { name := "unit η: P () → P u", run := fun _ =>
        accepts (R := Unit) [Raw.defn "eta"
          (pi' "u" () (.unit 1) (pi' "P" () (arr () (.unit 1) ty) (arr () (.app "P" .tt) (.app "P" "u"))))
          (lams ["u", "P", "x"] "x")] },
    { name := "ex falso", run := fun _ =>
        accepts (R := Unit) [Raw.defn "efq" (pi' "A" () ty (arr () (.empty 1) "A"))
          (lams ["A", "e"] (.absurd "A" "e"))] },
    { name := "() only checks against Unit", run := fun _ =>
        rejects (R := Unit) [Raw.defn "bad" (.empty 1) .tt] (fun _ => true) "an error" }
  ]

end Tests.Check
