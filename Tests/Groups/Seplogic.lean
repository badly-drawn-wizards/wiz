import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

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
        failsLibs "import HProp\ndef bad : (1 ↦ 5) ⊢ (1 ↦ 6) := Entails.refl (1 ↦ 5)" "mismatch"
        failsLibs "import HProp\ndef bad : @emp Nat ⊢ hpure False := Entails.refl emp" "mismatch"
        -- a wrong rearrangement of a `⋆` chain, the mismatch at the far end (each `⋆` is
        -- four definitions deep: this used to unfold for minutes before failing)
        failsLibsWithin 60 ("import Hoare\n" ++
          "def bad (p a b : Nat) (H K J : HProp Nat) : H ⋆ (K ⋆ (J ⋆ (p ↦ a))) ⊢ K ⋆ (H ⋆ (J ⋆ (p ↦ b))) :=\n" ++
          "  star.swap H K (J ⋆ (p ↦ a))") "mismatch" },
    { name := "a wrong specification is rejected, quickly", run := fun _ => do
        -- swap's specification with the postcondition of the identity
        failsLibsWithin 60 ("import HoareExamples\n" ++
          "def bad (p q a b : Nat) : Triple ((p ↦ a) ⋆ (q ↦ b)) (Prog.swap p q) (fun _ => (p ↦ a) ⋆ (q ↦ b)) :=\n" ++
          "  Prog.swap_spec p q a b") "mismatch"
        -- a wrong value read back
        failsLibsWithin 60 ("import Hoare\n" ++
          "def bad (l : Nat) : Triple (l ↦ 1) (Prog.read l) (fun r => hpure (r = 2) ⋆ (l ↦ 1)) :=\n" ++
          "  Triple.read l 1") "mismatch" },
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
        okLibs ("import HoareExamples\n#check @Prog.swap_spec\n#check @Prog.reverse_spec")
          ["Prog.swap_spec : (p : Nat) → (q : Nat) → (a : Nat) → (b : Nat) → Triple Nat Unit (star Nat (pts Nat p a) (pts Nat q b)) (Prog.swap p q) (fun _ => star Nat (pts Nat p b) (pts Nat q a))",
           "Prog.reverse_spec : (L : List Nat) → (fuel : Nat) → (p : Nat) → Nat.lt (List.length Nat L) fuel = .true → Triple Nat Nat (MList L p) (Prog.reverse fuel p) (fun r => MList (List.reverse Nat L) r)"] },
    { name := "a faulting program has no triple from a satisfiable precondition", run := fun _ =>
        failsLibs ("import Hoare\ndef bad : Triple (@emp Nat) (@Prog.fail Nat Unit) (fun (_ : Unit) => @emp Nat) :=\n" ++
          "  Triple.ret () (fun (_ : Unit) => @emp Nat)") "mismatch" },
    { name := "the programs run on concrete heaps, as adequacy says", run := fun _ =>
        okLibs ("import HoareExamples\n" ++
          "#eval Prog.show (Prog.swap 1 2) (Heap.ofList (.cons 10 (.cons 20 .nil)) 1) 3 3\n" ++
          -- the list 1, 2, 3 in cells at 1, 3, 5
          "#eval Prog.show (Prog.reverse 10 1) (Heap.ofList (.cons 1 (.cons 3 (.cons 2 (.cons 5 (.cons 3 (.cons 0 .nil)))))) 1) 7 7\n" ++
          "#eval Prog.show (Prog.reverse 2 1) (Heap.ofList (.cons 1 (.cons 3 (.cons 2 (.cons 5 (.cons 3 (.cons 0 .nil)))))) 1) 7 7\n" ++
          "#eval Prog.show (Prog.bind (Prog.ref 7) (fun l => Prog.read l)) Heap.empty 0 2")
          [".some ((), .cons .none (.cons (.some 20) (.cons (.some 10) .nil)))",
           -- reversed: the cell at 5 (value 3) points to 3 (value 2), which points to 1 (value 1)
           ".some (5, .cons .none (.cons (.some 1) (.cons (.some 0) (.cons (.some 2) (.cons (.some 1) (.cons (.some 3) (.cons (.some 3) .nil)))))))",
           -- not enough fuel: a fault
           ".none", ".some (7, .cons (.some 7) (.cons .none .nil))"] },
    { name := "xsimpl: cancellation up to AC, ∃ on both sides, pure facts, emp, htop and wands", run := fun _ =>
        okLibs ("import HoareTactics\n" ++
          "def e1 (a b c : HProp Nat) : (a ⋆ b) ⋆ c ⊢ c ⋆ (b ⋆ a) := by xsimpl\n" ++
          "def e2 (p q : Nat) : (p ↦ 1) ⋆ (q ↦ 2) ⊢ hexists (fun (n : Nat) => (q ↦ n) ⋆ (p ↦ 1)) := by xsimpl\n" ++
          "def e3 (p : Nat) : hexists (fun (n : Nat) => hpure (n = 3) ⋆ (p ↦ n)) ⊢ hexists (fun (m : Nat) => p ↦ m) := by xsimpl\n" ++
          "def e4 (a b : HProp Nat) : emp ⋆ (a ⋆ emp) ⋆ b ⊢ b ⋆ a ⋆ htop ⋆ emp := by xsimpl\n" ++
          "def e5 (a b c : HProp Nat) : c ⋆ (a ⋆ (a −∗ b)) ⊢ b ⋆ c := by xsimpl\n" ++
          "def e6 (a b : HProp Nat) : a ⊢ b −∗ (a ⋆ b) := by xsimpl\n" ++
          "def e7 (P : Prop) (hP : P) (a : HProp Nat) : a ⊢ hpure P ⋆ a := by xsimpl\n" ++
          "def e8 (p : Nat) (a : HProp Nat) : hexists (fun (n : Nat) => hpure (n = p) ⋆ a) ⊢ a := by\n  xpull as n, h\n  xsimpl") },
    { name := "xsimpl leaves what it cannot prove", run := fun _ => do
        failsLibs "import HoareTactics\ndef bad (a b c : HProp Nat) : a ⋆ b ⊢ c ⋆ a := by xsimpl" "⊢ Entails Nat b c"
        failsLibs "import HoareTactics\ndef bad (p : Nat) : (p ↦ 1) ⊢ (p ↦ 2) := by xsimpl" "unsolved goals"
        -- a tactic that fails says why, with the goal
        failsLibs "import HoareExamples\ndef bad (p q n : Nat) : Triple (p ↦ n) (Prog.incr q) (fun _ => p ↦ n) := by xstep" "xstep: the precondition has no cell at q"
        failsLibs "import HoareExamples\ndef bad (p q n : Nat) : Triple (p ↦ n) (Prog.incr3 p q) (fun _ => p ↦ n) := by xapp (Prog.incr_spec q n)" "xapp: the specification is about Prog.incr q, but the program is" },
    { name := "the x-tactics verify a counter, list length, map and free on mutable lists", run := fun _ =>
        okLibs ("import HoareExamples\n#check @Prog.incr3_spec\n#check @Prog.counter_spec\n#check @Prog.length_spec\n" ++
          "#check @Prog.incrAll.spec\n#check @Prog.freeAll.spec\n" ++
          "#eval Prog.show (Prog.counter) Heap.empty 0 1\n" ++
          "#eval Prog.show (Prog.length 10 1) (Heap.ofList (.cons 1 (.cons 3 (.cons 2 (.cons 5 (.cons 3 (.cons 0 .nil)))))) 1) 7 0")
          ["Prog.incr3_spec : (p : Nat) → (q : Nat) → (m : Nat) → (n : Nat) → Triple Nat Unit (star Nat (pts Nat p m) (pts Nat q n)) (Prog.incr3 p q) (fun _ => star Nat (pts Nat q (.succ n)) (pts Nat p (.succ (.succ m))))",
           "Prog.counter_spec : Triple Nat Nat (emp Nat) Prog.counter (fun r => hexists Nat Nat (fun c => star Nat (hpure Nat (r = 1)) (pts Nat c 1)))",
           "Prog.length_spec : (L : List Nat) → (fuel : Nat) → (p : Nat) → Nat.lt (List.length Nat L) fuel = .true → Triple Nat Nat (MList L p) (Prog.length fuel p) (fun r => star Nat (hpure Nat (r = List.length Nat L)) (MList L p))",
           "Prog.incrAll.spec : (L : List Nat) → (f : Nat) → Nat.lt (List.length Nat L) f = .true → (p : Nat) → Triple Nat Unit (MList L p) (Prog.incrAll f p) (fun _ => MList (List.incr L) p)",
           "Prog.freeAll.spec : (L : List Nat) → (f : Nat) → Nat.lt (List.length Nat L) f = .true → (p : Nat) → Triple Nat Unit (MList L p) (Prog.freeAll f p) (fun _ => emp Nat)",
           ".some (1, .cons (.some 1) .nil)", ".some (3, .nil)"] },
    { name := "a wrong specification is not proved by the x-tactics", run := fun _ =>
        failsLibs "import HoareExamples\ndef bad (p n : Nat) : Triple (p ↦ n) (Prog.incr p) (fun _ => p ↦ n) := by xgo" "unsolved goals" }
  ]

initialize registerGroup seplogicGroup

end Tests.Elab
