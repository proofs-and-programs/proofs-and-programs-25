import Mathlib

/-!
# Recursion

You have to make some recursive definitions and prove that they terminate.
-/

/-!
## Fibonacci numbers

These are defined by the identities:

* `fib 0 = 1`
* `fib 1 = 1`
* `fib (n + 2) = fib (n + 1) + fib n`

Complete the following definition:
-/
def fib (n : ℕ): ℕ :=
  match n with
  -- Change the code below (3 marks)
  | _ => sorry

/-! Test your definition with the following (uncomment the line below).-/
-- example : fib 7 = 21 := by rfl

/-!
## Proving termination

In the following, replace `partial def` by `def` and prove termination by choosing an appropriate function that decreases (2 marks).
-/
partial def f (a b : Nat) : Nat :=
  match a, b with
  | k + 2, l => f k (l + 1) + 1
  | k, l + 2 => f (k + 1) l + 2
  | _, _ => 1

/-!
## Proving termination

In the following, replace `partial def` by `def` and prove termination by choosing an appropriate function that decreases and proving the appropriate lemma (4 marks).
-/
partial def numSteps (step: Nat → Nat)(h : ∀n: Nat, step (n + 1) ≤ n)
    (n: Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 =>
    numSteps step h (step (n + 1)) + 1
