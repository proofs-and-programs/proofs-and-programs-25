/-!
# Simple Terms and Types

We consider a few terms and types in Lean. These are definitions that do not involve recursion/induction or propositions.
-/

#eval 1 + 2

def three := 3

#eval three -- 3

#check three -- three : Nat

#check Nat

#check Type

/-!
## Function types
-/

#check Nat → Nat

def cube (n: Nat) : Nat := n * n * n

#check cube

def cube' : Nat → Nat := fun n ↦ n * n * n

def cube'' := fun n: Nat => n * n * n

#eval cube 3 -- 27 (Note that we do not need brackets)

/-!
## Curried functions

Suppose we want to define the function `f` of two variables `a` and `b` taking value `a + b + 1`. We can define it as a function of one variable `a` returning a function of one variable `b`.
-/
def sum_plus_one : Nat → Nat → Nat :=
  fun a ↦ fun b ↦ a + b + 1

#check sum_plus_one

#check sum_plus_one 3

#check sum_plus_one 3 4

#eval sum_plus_one 3 4

def sum_of_squares (m n: Nat) :=
  m * m + n * n

#eval sum_of_squares 4 5
