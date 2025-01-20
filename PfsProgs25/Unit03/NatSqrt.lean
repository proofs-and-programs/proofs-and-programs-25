/-!
# Structures: Square root of a natural number

We have seen the following types:

* Universes
* Function types
* Dependent function types

There is only one other basic type construction in Lean: **Inductive Types** and their generalization, **Indexed Inductive Types**.

We start with a special class of inductive types: **Structures**. We will also see how to combine data and proofs and to prove with tactics.

## Square root of a natural number
-/
structure NatSqrt (n : Nat) where
  val : Nat
  isSqrt : val * val = n

#check NatSqrt
#check NatSqrt.mk
#check NatSqrt.val
#check NatSqrt.isSqrt

def sqrt4 : NatSqrt 4 := ⟨2, rfl⟩ -- angle brackets can be used to input the structure

def sqrt3 : NatSqrt 9 := NatSqrt.mk 3 rfl -- mk is a constructor

#check sqrt4 -- NatSqrt 4

#eval sqrt4.val -- 2

#eval sqrt3.val -- 3

def sqrt9 : NatSqrt 9 := { val := 3, isSqrt := rfl } -- curly braces can also be used
/-!
## A lemma

We will define a function that gives the square root of a product of two natural numbers. We will first prove a lemma that will be useful in the definition. This will be proved using tactics.

Note that all the `rw` tactics can be written as a single tactic with a list of rewrites.
-/

/-
Nat.mul_assoc (n m k : Nat) : n * m * k = n * (m * k)
-/
#check Nat.mul_assoc

theorem sqrt_mul (a b : Nat) : (a * a) * (b * b) = (a * b) * (a * b) := by
  /-
  a b : Nat
  ⊢ a * a * (b * b) = a * b * (a * b)
  -/
  rw [Nat.mul_assoc]
  /-
  a b : Nat
  ⊢ a * (a * (b * b)) = a * b * (a * b)
  -/
  rw [Nat.mul_comm]
  /-
  a b : Nat
  ⊢ a * (b * b) * a = a * b * (a * b)
  -/
  rw [← Nat.mul_assoc]
  /-
  a b : Nat
  ⊢ a * b * b * a = a * b * (a * b)
  -/
  rw [Nat.mul_assoc (a * b), Nat.mul_comm b a]

def sqrt_prod {m n : Nat}
    (sqm : NatSqrt m) (sqn : NatSqrt n) : NatSqrt (m * n) :=
  let val : Nat := sqm.val * sqn.val
  have h : val * val = m * n := by
    unfold val
    simp [← sqm.isSqrt, ← sqn.isSqrt]
    symm
    /-
    m n : Nat
    sqm : NatSqrt m
    sqn : NatSqrt n
    val : Nat := sqm.val * sqn.val
    ⊢ sqm.val * sqm.val * (sqn.val * sqn.val) = sqm.val * sqn.val * (sqm.val * sqn.val)
    -/
    apply sqrt_mul
    /- The `apply` tactic tries to give the goal as the result of applying the given theorem (or term) with the correct arguments.

    If some arguments are not known, it will make them into new goals.
    -/
  { val := val, isSqrt := h }
