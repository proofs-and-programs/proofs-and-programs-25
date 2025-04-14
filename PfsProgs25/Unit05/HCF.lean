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

/--
The result that the GCD of two numbers divides both numbers.
-/
theorem hcf_dvd (a b : ℕ) : hcf a b ∣ a ∧ hcf a b ∣ b := by
  if h:b=0 then
    simp [h, hcf]
  else
    if h':a < b then
      rw [hcf]
      simp [h, h']
      let h'' := hcf_dvd b a
      apply And.intro
      · apply h''.right
      · apply h''.left
    else
      rw [hcf]
      simp [h, h']
      have h₁ : a % b < b := by
        apply Nat.mod_lt
        simp [Nat.pos_iff_ne_zero]
        assumption
      have h :=  hcf_dvd (a % b) b
      have ⟨h₁, h₂⟩ := h
      apply And.intro
      · have h₃ :=  Nat.div_add_mod a b
        nth_rewrite 2 [← h₃]
        apply Nat.dvd_add
        · simp [Nat.dvd_trans h₂]
        · assumption
      · apply h₂
termination_by (b, a)

-- #leansearch "A number is the sum of the remainder and the product of the quotient and the divisor."

/--
A structure that represents a Bezout pair of integers `x` and `y` such that `x * a + y * b = hcf a b`.
-/
structure BezoutPair (a b : ℕ) where
  x  : ℤ
  y  : ℤ
  eqn : x * a + y * b = hcf a b

/--
The function `bezoutPair` computes a pair of integers such that `x * a + y * b = hcf a b`.
-/
def bezoutPair (a b : ℕ ) : BezoutPair a b :=
  if h:b = 0 then
    ⟨1, 0, by simp [h, hcf]⟩
  else
    if h':a < b then
      let ⟨x, y, h₁⟩ := bezoutPair b a
      ⟨y, x, by
        rw [hcf]
        simp [h, h']
        rw [← h₁]
        simp [add_comm]
      ⟩
    else
      have h₁ : a % b < b := by
        apply Nat.mod_lt
        simp [Nat.pos_iff_ne_zero]
        assumption
      let ⟨x, y, h₁⟩ := bezoutPair (a % b) b
      ⟨x, y - x * (a / b), by
        rw [hcf]
        simp [h, h']
        rw [← h₁]
        let r := Nat.div_add_mod a b
        nth_rewrite 1 [← r]
        simp
        rw [sub_eq_add_neg, add_comm y, ← neg_mul, add_mul, mul_assoc (-x), neg_mul, ← add_assoc, ← sub_eq_add_neg, ← Int.mul_sub]
        simp only [add_left_inj, mul_eq_mul_left_iff]
        left
        ring
      ⟩
termination_by (b, a)

-- #leansearch "Multiplication distributes over subtraction."

/-
Int.gcd_eq_gcd_ab (x y : ℤ) : ↑(x.gcd y) = x * x.gcdA y + y * x.gcdB y
-/
#check Int.gcd_eq_gcd_ab
/-
Int.gcd_dvd_left {a b : ℤ} : ↑(a.gcd b) ∣ a
-/
#check Int.gcd_dvd_left
/-
Int.gcd_dvd_iff {a b : ℤ} {n : ℕ} : a.gcd b ∣ n ↔ ∃ x y, ↑n = a * x + b * y
-/
#check Int.gcd_dvd_iff
