/-!
# Tactic Examples

We show many examples of using tactics. The results are of the form `m ≤ n` where `m` and `n` are natural numbers.
-/

/-!
## The `apply` tactic and `repeat` tactic combinator
-/
example : 4 ≤ 8 := by
  /-
  ⊢ 4 ≤ 8
  -/
  apply Nat.succ_le_succ
  /-
  case a
  ⊢ 3 ≤ 7
  -/
  apply Nat.succ_le_succ (n := 2)
  /-
  case a
  ⊢ 2 ≤ 6
  -/
  repeat apply Nat.succ_le_succ -- repeat as long as valid
  apply Nat.zero_le

example : 4 ≤ 8 := by
  /-
  ⊢ 4 ≤ 8
  -/
  repeat apply Nat.succ_le_succ
  apply Nat.zero_le -- `apply` could figure out that `n := 4` works

example : 4 ≤ 8 := by
  /-
  ⊢ 4 ≤ 8
  -/
  have h₁ : 0 ≤ 4 := by apply Nat.zero_le
  have h₂ := Nat.succ_le_succ h₁
  have h₃ : 2 ≤ 6 := Nat.succ_le_succ h₂
  apply Nat.succ_le_succ
  apply Nat.succ_le_succ
  apply h₃

example : 4 ≤ 8 := by
  /-
  ⊢ 4 ≤ 8
  -/
  have h₁ : 0 ≤ 4 := by apply Nat.zero_le
  have h₂ := Nat.succ_le_succ h₁
  have h₃ := Nat.succ_le_succ h₂
  apply Nat.succ_le_succ
  apply Nat.succ_le_succ
  exact h₃ -- `exact` is a tactic that closes the goal if the goal is equal to the term

example : 4 ≤ 8 := by
  /-
  ⊢ 4 ≤ 8
  -/
  have h₁ : 0 ≤ 4 := by apply Nat.zero_le
  have h₂ := Nat.succ_le_succ h₁
  have h₃ := Nat.succ_le_succ h₂
  apply Nat.succ_le_succ
  apply Nat.succ_le_succ
  assumption -- `assumption` closes the goal if the goal is equal to a hypothesis

example : 4 ≤ 8 := by
  /-
  ⊢ 4 ≤ 8
  -/
  apply Nat.le_of_succ_le_succ
  -- repeat apply Nat.le_of_succ_le_succ
  /-
  case a
  ⊢ Nat.succ 4 ≤ Nat.succ 8
  -/
  repeat apply Nat.succ_le_succ
  apply Nat.zero_le -- `apply` could figure out that `n := 4` works

def someNat : Nat := by
  apply Nat.succ
  apply Nat.succ
  exact 4

#eval someNat -- 6

def anotherNat : Nat := by
  apply Nat.succ
  apply Nat.add
  /-
  case a
  ⊢ Nat

  case a
  ⊢ Nat
  -/
  · exact 2
  · apply Nat.succ
    apply Nat.zero

/-
⊢ ∀ {n m : Nat}, n ≤ m → n ≤ m.succ
-/
#check Nat.le_step

/-
⊢ ∀ (n : Nat), n ≤ n
-/
#check Nat.le_refl

example : 3 ≤ 5 := by
  apply Nat.le_step
  apply Nat.le_step
  apply Nat.le_refl

example : 3 ≤ 5 := by
  repeat apply Nat.le_step
  /-
  case h.h.h.h.h
  ⊢ 3 ≤ 0
  -/
  sorry -- We have reached an unprovable state

-- The `first` tactic combinator tries each tactic in order until one works
example : 3 ≤ 5 := by
  /-
  ⊢ 3 ≤ 5
  -/
  first | apply Nat.le_refl | apply Nat.le_step
  /-
  case h
  ⊢ 3 ≤ 4
  -/
  first | apply Nat.le_refl | apply Nat.le_step
  /-
  case h.h
  ⊢ 3 ≤ 3
  -/
  first | apply Nat.le_refl | apply Nat.le_step

example : 30 ≤ 50 := by
  repeat (first | apply Nat.le_refl | apply Nat.le_step)

example : 30 ≤ 50 := by decide

macro "nat_le" : tactic =>
  `(tactic|repeat (first | apply Nat.le_refl | apply Nat.le_step))

example : 30 ≤ 50 := by nat_le

macro "repeating" r:term "finish_with" f:term : tactic =>
  `(tactic| repeat (first | apply $f | apply $r))

example : 30 ≤ 50 := by
  repeating Nat.le_step finish_with Nat.le_refl

example : 30 ≤ 50 := by
  repeating Nat.succ_le_succ finish_with Nat.zero_le
