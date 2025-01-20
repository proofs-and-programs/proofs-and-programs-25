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

#check lt_of_le_of_lt
