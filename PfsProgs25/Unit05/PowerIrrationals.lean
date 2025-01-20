import Mathlib
/-!
# A Noncomputable function

An interesting example of a non-constructive proof is the following:

**Theorem:** There exist irrational numbers $a$ and $b$ such that $a^b$ is rational.
**Proof:** Let `b = √2`. If `b^b` is rational, then we can take `a = b`. Otherwise, we can take `a = √2^{√2}`, so `a^b=2`.

We can prove this in Lean. But a function that returns such a pair of numbers has to be defined as `noncomputable` in Lean.
-/
