/-!
# Propositions and Proofs

As we have mentioned, proofs and propositions are terms, with propositions as types. The universe `Prop` is the type of propositions. To start with, it is best to ignore the difference between `Prop` and `Type` and treat them as the same.
-/

/-!
A logical statement like `1 ≤ 2` is a proposition and has type `Prop`.
-/
#check 1 ≤ 2 -- Prop
#check Prop -- Type
#check Type -- Type 1

#check Nat.zero_le -- Nat → 0 ≤ n

#check Nat.le_refl -- ∀ (n : Nat), n

/-!
The proposition `0 ≤ 2` is true and has proof `Nat.zero_le 2`.
-/
#check Nat.zero_le 2 -- 0 ≤ 2

#check Nat.le -- Nat → Nat → Prop

/-!
A proposition may be neither proved nor disproved. So we cannot evaluate it. We can evaluate it if it is decidable.
-/

/--
error: failed to synthesize
  Decidable (Nat.le 1 2)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#eval Nat.le 1 2

#check False -- Prop
#check True -- Prop

/-!
We can combine propositions to make propositions:

* If `P` and `Q` are propositions, then `P ∧ Q` is the proposition "P and Q".
* If `P` and `Q` are propositions, then `P ∨ Q` is the proposition "P or Q".
* If `P` and `Q` are propositions, then `P → Q` is the proposition "if P then Q".
* If `P` is a proposition, then `¬ P` is the proposition "not P", which is `P → False`.

The key idea is that function application is exactly analogous to the logical rule of inference called modus ponens.
-/
def modus_ponens {P Q: Prop} (h₁ : P) (h₂ : P → Q) : Q :=
  h₂ h₁

def application {α β : Type} (a: α) (f: α → β) : β :=
  f a

#check Nat.succ -- Nat → Nat
#eval application 1 Nat.succ -- 2

#check Nat.succ_le_succ -- ∀ {n m : Nat}, n ≤ m → n.succ ≤ m.succ

/-!
We apply modus-ponens with `P` being `0 ≤ 2` and `P → Q` being `Nat.succ_le_succ` applied to `0` and `2`.
-/
#check @Nat.succ_le_succ 0 2 -- 0 ≤ 2 → 1 ≤ 3

#check modus_ponens (Nat.zero_le 2)
  (@Nat.succ_le_succ 0 2) -- 1 ≤ 3

/-!
Some proofs at *term level*
-/
def one_le_three : 1 ≤ 3 :=
  Nat.succ_le_succ (Nat.zero_le 2) -- the `_` is filled in by Lean with `2` as the only way to make the type correct

def two_le_five : 2 ≤ 5 :=
  @Nat.succ_le_succ 1 _ (Nat.succ_le_succ (Nat.zero_le _))

#check @Nat.succ_le_succ 0 2 (Nat.zero_le 2) -- 1 ≤ 3

def wrong_three_le_one (h : 2 ≤ 0) : 3 ≤ 1 :=
  Nat.succ_le_succ h

/-!
## Proof Irrelevance

In Lean, any two proof terms of the same proposition are equal by definition. This is called *proof irrelevance*.
-/
theorem proof_irrelevance {P: Prop} (h₁ h₂: P) :
  h₁ = h₂ := rfl

/-!
## Universes

* Universes in Lean are called `Sort`s, they are `Sort 0`, `Sort 1`, etc.
* `Prop` is `Sort 0`.
* `Type` is `Sort 1`.
* `Type n` is `Sort n.succ`.
* Strictly speaking, the `n` here is a universe level, not a natural number.
-/

/-!
## Dependent Function Types

The type of `Nat.zero_le` is `∀ (n : Nat), 0 ≤ n`. We will write it more like a function type
-/
#check Nat.zero_le -- ∀ (n : Nat), 0 ≤ n

def my_zero_le : (n: Nat) → Nat.le 0 n :=
  fun n ↦ Nat.zero_le n

#check Nat.le 0 -- Nat → Prop
/-!
We saw that if `α` and `β` are types (or props), then `α → β` is the type of functions from `α` to `β`.

If instead we have `β : α → Type`or `β : α → Prop`, then `(a : α) → β a` (more formally `Π (a : α), β a`) is the type of dependent functions from `a : α` to `β a`.
-/
