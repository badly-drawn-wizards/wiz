import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

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
  exercise := "lib/Optic.wiz (Feral, RD11)"
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

initialize registerGroup opticGroup

end Tests.Elab
