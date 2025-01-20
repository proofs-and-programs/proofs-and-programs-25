import Mathlib
/-!
# A Noncomputable function

An interesting example of a non-constructive proof is the following:

**Theorem:** There exist irrational numbers $a$ and $b$ such that $a^b$ is rational.
**Proof:** Let `b = √2`. If `b^b` is rational, then we can take `a = b`. Otherwise, we can take `a = √2^{√2}`, so `a^b=2`.

We can prove this in Lean. But a function that returns such a pair of numbers has to be defined as `noncomputable` in Lean.
-/
noncomputable abbrev sqrt_two := Real.sqrt 2

theorem sq2_pow_twice : ((sqrt_two) ^ sqrt_two) ^ sqrt_two = 2 := by
  rw [← Real.rpow_mul, Real.mul_self_sqrt]
  · simp
  · simp
  · apply Real.sqrt_nonneg

theorem exists_irrationals_pow_rational :
  ∃ a b : ℝ, (Irrational a) ∧ (Irrational b) ∧ ¬ (Irrational (a ^ b)) := by
    by_cases c:Irrational (sqrt_two ^ sqrt_two)
    · use sqrt_two ^ sqrt_two, sqrt_two
      simp [c]
      apply And.intro
      · apply irrational_sqrt_two
      · simp [irrational_iff_ne_rational, sq2_pow_twice]
    · use sqrt_two, sqrt_two
      simp [irrational_sqrt_two, c]
