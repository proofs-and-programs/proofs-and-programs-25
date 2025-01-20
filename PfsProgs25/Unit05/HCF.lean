import Mathlib
/-!
# GCD: Termination example

As an example of proving termination, we define the function `hcf` that computes the greatest common divisor of two natural numbers. We prove that `hcf` terminates by showing that the argument decreases in each recursive call.
-/
