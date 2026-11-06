import Wiz
import Tests.Harness

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

open Wiz Raw

namespace Tests.Eval

abbrev T := Term Unit

def nf' (t : Raw Unit) (g : Globals Unit := {}) : String := (nf g t.toTerm).pretty

/-- A few untyped-but-terminating terms; `eval`/`quote` don't need types. -/
def idR : Raw Unit := lams ["x"] "x"
def constR : Raw Unit := lams ["x", "y"] "x"
def church (n : Nat) : Raw Unit :=
  lams ["s", "z"] ((List.range n).foldl (fun acc _ => .app "s" acc) "z")
def addR : Raw Unit := lams ["m", "n", "s", "z"] (apps "m" ["s", apps "n" ["s", "z"]])

def axiomsG : Globals Unit :=
  ({} : Globals Unit) |>.insert (Raw.axiom "f" ty) |>.insert (Raw.axiom "a" ty)

def evalGroup : Group where
  name := "eval/quote"
  exercise := "Exercises 1.1–1.3"
  cases := [
    { name := "Type normalises to itself", run := fun _ => checkEq "Type" (nf' (.sort 0)) },
    { name := "λx. x is already normal", run := fun _ => checkEq "λ x. x" (nf' idR) },
    { name := "β: (λx. x) (λy. y) ⇝ λy. y",
      run := fun _ => checkEq "λ y. y" (nf' (.app idR (lams ["y"] "y"))) },
    { name := "closures capture: (λx y. x) (λz. z) ⇝ λy z. z",
      run := fun _ => checkEq "λ y. λ z. z" (nf' (.app constR (lams ["z"] "z"))) },
    { name := "de Bruijn levels → indices: λx y. x y",
      run := fun _ => checkEq (Term.lam (R := Unit) "x" (.lam "y" (.app (.var 1) (.var 0))))
        (nf {} (lams ["x", "y"] (.app "x" "y") : Raw Unit).toTerm) },
    { name := "normalise under binders: λx. (λy. y) x ⇝ λx. x",
      run := fun _ => checkEq "λ x. x" (nf' (lams ["x"] (.app idR "x"))) },
    { name := "church 2 + 2 = 4",
      run := fun _ => checkEq (nf' (church 4)) (nf' (apps addR [church 2, church 2])) },
    { name := "let: let y := (λx. x); y ⇝ λx. x",
      run := fun _ => checkEq "λ x. x" (nf' (.letE "y" () ty idR "y")) },
    { name := "axioms stay stuck: f ((λx. x) a) ⇝ f a",
      run := fun _ => checkEq "f a" (nf' (.app "f" (.app idR "a")) axiomsG) },
    { name := "definitions unfold",
      run := fun _ => checkEq "λ x. x"
        (nf' "myid" (({} : Globals Unit).insert (Raw.defn "myid" ty idR))) },
    { name := "Π types: codomain normalised under binder",
      run := fun _ => checkEq "(A :() Type) → A"
        (nf' (pi' "A" () ty (.app idR "A"))) }
  ]

def isConv (a b : Raw Unit) (g : Globals Unit := axiomsG) : Bool :=
  conv g 0 (eval g [] a.toTerm) (eval g [] b.toTerm)

def convGroup : Group where
  name := "conv"
  exercise := "Exercise 1.4"
  cases := [
    { name := "Type ≡ Type", run := fun _ => check (isConv ty ty) "" },
    { name := "Type ≢ Type 1", run := fun _ => check (!isConv ty (.sort 1)) "" },
    { name := "α-equivalence: λx. x ≡ λy. y", run := fun _ => check (isConv idR (lams ["y"] "y")) "" },
    { name := "β: (λx. x) a ≡ a", run := fun _ => check (isConv (.app idR "a") "a") "" },
    { name := "η: λx. f x ≡ f", run := fun _ => check (isConv (lams ["x"] (.app "f" "x")) "f") "" },
    { name := "η (other side): f ≡ λx. f x", run := fun _ => check (isConv "f" (lams ["x"] (.app "f" "x"))) "" },
    { name := "different axioms: f ≢ a", run := fun _ => check (!isConv "f" "a") "" },
    { name := "λx y. x ≢ λx y. y", run := fun _ => check (!isConv constR (lams ["x", "y"] "y")) "" },
    { name := "church 2 + 2 ≡ 4", run := fun _ => check (isConv (apps addR [church 2, church 2]) (church 4)) "" },
    { name := "Π: (A : Type) → A ≢ (A : Type) → Type",
      run := fun _ => check (!isConv (pi' "A" () ty "A") (pi' "A" () ty ty)) "" }
  ]

end Tests.Eval
