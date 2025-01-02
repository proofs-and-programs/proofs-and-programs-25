import Mathlib
/-!
# Examples of programs and in Lean

We see our first examples of programs and proofs in Lean. A major goal is to illustrate *functional programming*, where we use recursions for loops and avoid mutable variables.
-/

def sumToN (n: Nat) : Nat :=
  match n with
  | 0 => 0
  | m + 1 =>
    let sumToM := sumToN m
    sumToM + (m + 1)

#eval sumToN 10

/-!
We prove a property of `sumToN` by induction. This is a good illustration of how to prove properties of programs in Lean, but not of what a proof means (since we use some automation).
-/
theorem sumToNFormula (n: Nat) : 2 * sumToN n = n * (n + 1) := by
  induction n
  case zero => rfl
  case succ m ih =>
    rw [sumToN, left_distrib, ih]
    ring

/-!
We generally use the functional style as above, with no mutable variables. But Lean is pragmatic and allows mutable variables "using Monads" when needed. Here is an example.

It is harder to prove properties with such definitions. But in meta-programming, where we are typically not able to prove properties, we often use mutable variables.
-/
def sumToN' (n: Nat) : Nat := Id.run do
  let mut sum := 0
  for i in [1:n+1] do
    sum := sum + i
  return sum

#eval sumToN' 10
