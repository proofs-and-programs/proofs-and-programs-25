import Mathlib
/-!
# Match Examples

To see how match works, we consider an example with `Nat`, which is a non-trivial inductive type. We will see how to define functions by recursion on `Nat`.
-/
def Nat.double (n: Nat) : Nat :=
  match n with
  | 0 => 0
  | Nat.succ m => Nat.succ (Nat.succ (Nat.double m))

#eval Nat.double 5 -- 10

/-!
Double of a natural number defined in a more complicated way.
-/
def Nat.double' (n: Nat) : Nat :=
  match p:n with
  | 0 => 0
  | 1 => 2
  | 7 => 14
  | m + 3 => by
    exact double' m + 6
  | m + 1 => double' m + 2

#eval Nat.double' 5 -- 10

/-!
A non-terminating function defined using `match`.
-/
partial def Nat.notDouble (n: Nat) : Nat :=
  match n with
  | m => notDouble m + 2

-- #eval Nat.double'' 5 -- Don't do this!
