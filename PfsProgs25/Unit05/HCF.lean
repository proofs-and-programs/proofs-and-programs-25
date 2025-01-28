import Mathlib
/-!
# GCD: Termination example

As an example of proving termination, we define the function `hcf` that computes the greatest common divisor of two natural numbers. We prove that `hcf` terminates by showing that the argument decreases in each recursive call.
-/

/--
Simple version of the GCD function
-/
def hcfSimple (a b : ℕ) : ℕ :=
  if b = 0 then a else
  if a < b then hcfSimple b a
  else hcfSimple (a - b) b

#eval hcfSimple 12 40 -- 4

/--
The function `hcf` computes the greatest common divisor of two natural numbers. We have to prove that it terminates.
-/
def hcf (a b : ℕ) : ℕ :=
  if h:b = 0 then a else
  if h':a < b then hcf b a
  else
    have h₁ : a % b < b := by
      apply Nat.mod_lt
      simp [Nat.pos_iff_ne_zero]
      assumption
    have : a % b < a := by
      -- apply Nat.lt_of_lt_of_le h₁
      apply Nat.lt_of_lt_of_le _ (Nat.le_of_not_gt h')
      assumption
    have : a % b < a := by
      apply Nat.lt_of_lt_of_le h₁
      apply Nat.le_of_not_gt
      assumption
    hcf (a % b) b
termination_by (b, a)

/-
Nat.pos_iff_ne_zero {n : ℕ} : 0 < n ↔ n ≠ 0
-/
#check Nat.pos_iff_ne_zero
/-
lt_of_lt_of_le.{u_1} {α : Type u_1} [Preorder α] {a b c : α} (hab : a < b) (hbc : b ≤ c) : a < c
-/
#check lt_of_lt_of_le

#eval hcf 12 40 -- 4

/-!
We cannot always make partial definitions.
-/

/--
error: failed to compile 'partial' definition 'wrong', could not prove that the type
  {α : Type} → ℕ → α
is nonempty.

This process uses multiple strategies:
- It looks for a parameter that matches the return type.
- It tries synthesizing 'Inhabited' and 'Nonempty' instances for the return type, while making every parameter into a local 'Inhabited' instance.
- It tries unfolding the return type.

If the return type is defined using the 'structure' or 'inductive' command, you can try adding a 'deriving Nonempty' clause to it.
-/
#guard_msgs in
partial def wrong {α : Type} (x : Nat ) : α := wrong x

/--
A recursively defined function that loops forever but is a legal definition as its codomain is empty.
-/
partial def not_wrong {α : Type} [Nonempty α] (x : Nat ) : α := not_wrong x

#check not_wrong (α := ℝ) 0 -- ℝ
