import Mathlib
/-!
# GCD: Termination example

As an example of proving termination, we define the function `hcf` that computes the greatest common divisor of two natural numbers. We prove that `hcf` terminates by showing that the argument decreases in each recursive call.
-/
def hcf (a b: Nat) : Nat :=
  if p:b = 0 then a
  else
   if c:a < b then
      hcf b a
    else
      have : a % b < a := by
        apply lt_of_lt_of_le (b := b)
        · apply Nat.mod_lt
          simp [Nat.pos_iff_ne_zero]
          assumption
        · apply le_of_not_gt
          assumption
      hcf (a % b) b
termination_by (b, a)

theorem hcf_zero (a: Nat) : hcf a 0 = a := by
  simp [hcf]

theorem hcf_bezout (a b: Nat) :
    ∃ k l: ℤ, hcf a b = k * a + l * b := by
  unfold hcf
  split
  · rename_i h
    simp [h]
    use 1
    simp
  · by_cases c:a < b
    · simp [c]
      let ⟨k, l, p⟩  := hcf_bezout b a
      use l, k
      rw [add_comm]
      exact p
    · simp [c]
      have : a % b < a := by
        apply lt_of_lt_of_le (b := b)
        · apply Nat.mod_lt
          simp [Nat.pos_iff_ne_zero]
          assumption
        · apply le_of_not_gt
          assumption
      let ⟨k', l', p⟩  := hcf_bezout (a % b) b
      rw [← Nat.mod_add_div a b]
      simp
      use k', l' - k' * (a / b)
      rw [p]
      simp
      ring
termination_by (b, a)

#check Nat.mod_add_div

theorem hcf_div (a b: Nat) :
    hcf a b ∣ a ∧ hcf a b ∣ b := by
  unfold hcf
  split
  · rename_i h
    simp [h]
  · by_cases c:a < b
    · simp [c]
      have ⟨p₁, p₂⟩  := hcf_div b a
      simp [p₁, p₂]
    · simp [c]
      rename_i h
      have : a % b < a := by
        apply lt_of_lt_of_le (b := b)
        · apply Nat.mod_lt
          simp [Nat.pos_iff_ne_zero]
          assumption
        · apply le_of_not_gt
          assumption
      have ⟨p₁, p₂⟩  := hcf_div (a % b) b
      simp [p₂]
      rw [← Nat.mod_add_div a b]
      simp
      apply Nat.dvd_add
      · assumption
      · apply Nat.dvd_trans p₂
        apply Nat.dvd_mul_right
termination_by (b, a)

#check Nat.dvd_add
#leansearch "divisibility is transitive."
