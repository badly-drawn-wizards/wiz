import Wiz.Rig

/-!
# Rig instances

* `Unit`         -- the trivial rig. Every quantity is the same, so QTT collapses to
                    ordinary dependent type theory. Fully implemented as a worked example.
* `Nat`          -- exact counting: a variable declared at `n` is used exactly `n` times.
                    Fully implemented as a second worked example.
* `ZeroOneMany`  -- Idris 2's `{0, 1, ω}`. **Exercises 0.1 and 0.2.**
-/

namespace Wiz

/-! ## `Unit`: plain Martin-Löf type theory -/

instance : QRig Unit where
  zero := ()
  one := ()
  add _ _ := ()
  mul _ _ := ()
  add_assoc _ _ _ := rfl
  add_comm _ _ := rfl
  zero_add _ := rfl
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  zero_mul _ := rfl
  mul_zero _ := rfl
  left_distrib _ _ _ := rfl
  right_distrib _ _ _ := rfl
  le _ _ := true
  le_refl _ := rfl
  le_trans _ _ _ _ _ := rfl
  add_le_add _ _ _ _ _ _ := rfl
  mul_le_mul _ _ _ _ _ _ := rfl

instance : QuantitySyntax Unit where
  ofLiteral _ := some ()
  explicitDefault := ()
  implicitDefault := ()
  display _ := ""

/-! ## `Nat`: exact usage counting -/

instance : QRig Nat where
  add_assoc := Nat.add_assoc
  add_comm := Nat.add_comm
  zero_add := Nat.zero_add
  mul_assoc := Nat.mul_assoc
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  left_distrib := Nat.left_distrib
  right_distrib := Nat.right_distrib
  le a b := a == b
  le_refl _ := by simp
  le_trans _ _ _ h₁ h₂ := by simp_all
  add_le_add _ _ _ _ h₁ h₂ := by simp_all
  mul_le_mul _ _ _ _ h₁ h₂ := by simp_all

/-- There is no ω in `Nat`, so explicit binders default to exactly once. -/
instance : QuantitySyntax Nat where
  ofLiteral := String.toNat?
  explicitDefault := 1
  implicitDefault := 0
  display := toString

/-! ## `ZeroOneMany`: Idris 2's quantities -/

/-- `zero` = erased, `one` = linear (exactly once), `many` = unrestricted (ω). -/
inductive ZeroOneMany where
  | zero
  | one
  | many
  deriving DecidableEq, Repr, Inhabited

namespace ZeroOneMany

instance : ToString ZeroOneMany where
  toString
    | zero => "0"
    | one => "1"
    | many => "ω"

/-- **Exercise 0.1a.** Addition: "used in one place, then also used in another".
Think about what `1 + 1` must be when there is no `2` available. -/
def add (a b : ZeroOneMany) : ZeroOneMany :=
  sorry

/-- **Exercise 0.1b.** Multiplication: "passed `b`-many times to a binder of quantity `a`". -/
def mul (a b : ZeroOneMany) : ZeroOneMany :=
  sorry

/-- **Exercise 0.1c.** Compatibility: may a variable declared `declared` be used `used` times?
Hint: an ω variable tolerates any usage; a linear one tolerates exactly one use. -/
def le (used declared : ZeroOneMany) : Bool :=
  sorry

/-- **Exercise 0.2.** Prove the laws. Once 0.1 is done, almost all of these fall to
`intro a b c; cases a <;> cases b <;> cases c <;> rfl` (or `decide` on the
case-split goals). -/
instance : QRig ZeroOneMany where
  zero := zero
  one := one
  add := add
  mul := mul
  le := le
  add_assoc := sorry
  add_comm := sorry
  zero_add := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  zero_mul := sorry
  mul_zero := sorry
  left_distrib := sorry
  right_distrib := sorry
  le_refl := sorry
  le_trans := sorry
  add_le_add := sorry
  mul_le_mul := sorry

instance : QuantitySyntax ZeroOneMany where
  ofLiteral
    | "0" => some zero
    | "1" => some one
    | "ω" => some many
    | _ => none
  explicitDefault := many
  implicitDefault := zero
  display := toString

end ZeroOneMany

end Wiz
