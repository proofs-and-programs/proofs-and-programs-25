import Mathlib
/-!
# A Noncomputable function

An interesting example of a non-constructive proof is the following:

**Theorem:** There exist irrational numbers $a$ and $b$ such that $a^b$ is rational.
**Proof:** Let `b = √2`. If `b^b` is rational, then we can take `a = b`. Otherwise, we can take `a = √2^{√2}`, so `a^b=2`.

We can prove this in Lean. But a function that returns such a pair of numbers has to be defined as `noncomputable` in Lean.
-/

/--
The square root of `2` (an abbreviation).
-/
noncomputable abbrev sqrt2 : ℝ := Real.sqrt 2

/--
The equation `(sqrt2^sqrt2)^sqrt2 = 2`.
-/
theorem sq_sq_sq_sqrt2_rational :
  (sqrt2^sqrt2)^sqrt2 = 2 := by
  rw [← Real.rpow_mul, Real.mul_self_sqrt]
  · simp
  · simp
  · simp

example :
  (sqrt2^sqrt2)^sqrt2 = 2 := by
  rw [← Real.rpow_mul, Real.mul_self_sqrt] <;> simp

/--
There exists an irrational numbers `a` and `b` such that `a^b` is rational.
-/
theorem irrational_power_irrational_rational :
  ∃ (a b : ℝ), Irrational (a) ∧ Irrational b ∧
    ¬ Irrational (a^b)  := by
  by_cases h : Irrational (sqrt2^sqrt2)
  case pos =>
    use sqrt2 ^ sqrt2, sqrt2
    simp [h, sq_sq_sq_sqrt2_rational, irrational_sqrt_two]
  case neg =>
    use sqrt2, sqrt2
    simp [irrational_sqrt_two]
    assumption

/-
irrational_power_irrational_rational : ∃ a b, Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b)
-/
#check irrational_power_irrational_rational

/--
A structure that contains irrational numbers `a` and `b` such that `a^b` is rational along with proofs.
-/
structure IrrationalPair where
  (a b : ℝ)
  (irrational_a : Irrational a)
  (irrational_b : Irrational b)
  (rational_ab : ¬ Irrational (a^b))

/--
Noncomputable function that returns an `IrrationalPair`, i.e., irrational numbers `a` and `b` such that `a^b` is rational.
-/
noncomputable def irrationalPair : IrrationalPair := by
  apply Classical.choice
  let ⟨a, b, h₁, h₂, h₃⟩ := irrational_power_irrational_rational
  exact ⟨a, b, h₁, h₂, h₃⟩

#check Nonempty

/--
A noncomputable function that returns an `IrrationalPair`, i.e., irrational numbers `a` and `b` such that `a^b` is rational, represented as a subtype.
-/
noncomputable def irrationalPair' :
  {ab: ℝ × ℝ // Irrational ab.1 ∧ Irrational ab.2 ∧ ¬ Irrational (ab.1 ^ ab.2)} := by
  apply Classical.choice
  let ⟨a, b, h₁, h₂, h₃⟩ := irrational_power_irrational_rational
  use (a, b)

/-
Subtype.{u} {α : Sort u} (p : α → Prop) : Sort (max 1 u)
-/
#check Subtype
