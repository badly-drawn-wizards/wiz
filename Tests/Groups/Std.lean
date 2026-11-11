import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def stdGroup : Group where
  name := "std"
  exercise := "Stage 12a"
  cases := [
    -- (7e) integers
    { name := "integers: arithmetic, literals, printing", run := fun _ =>
        okLibs ("import Int\n#eval (-3 : Int) * 4 + 2\n#eval (5 : Int) - 8\n#eval (-7 : Int) / 2\n#eval (-7 : Int) % 2\n" ++
          "def t : (-3 : Int) * 4 + 2 = -10 := rfl\ndef u (a : Int) : 0 + a = a := Int.zero_add a\n#run (2 : Int) - 3 * 4\n#eval Int.natAbs (-5)\n" ++
          "#eval Int.lt (-2) 1\n#eval Int.toNat (-4)")
          ["-10", "-3", "-3", "-1", "-10", "5", ".true", "0"] },
    { name := "integers: lemmas, and printing needs no axiom", run := fun _ =>
        okLibs ("import Int\n#check Int.neg_neg\n#check Int.add_zero\n#print axioms Int.add_zero")
          ["Int.neg_neg : (a : Int) → Neg.neg Int instNegInt (Neg.neg Int instNegInt a) = a",
           "Int.add_zero : (a : Int) → Add.add Int instAddInt a (OfNat.ofNat Int 0 (instOfNatIntN 0)) = a",
           "'Int.add_zero' does not depend on any axioms"] },
    { name := "integers: compiled (C)", run := fun _ =>
        cRunLibs "import Int\ndef main : Int := (-3 : Int) * 4 + 2" "-10" },
    { name := "machine types: operators at UInt64 and Float64", run := fun _ =>
        okLibs "import IO\ndef f (a b : UInt64) : UInt64 := a * b + 1\ndef g (x : Float64) : Float64 := x * x - 2 / 3" },
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

initialize registerGroup stdGroup

end Tests.Elab
