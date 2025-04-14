import Mathlib
import PfsProgs25.Unit04.ShortAnswer

/-!
# Listable typeclass

This is a crude version of finite types. It is a typeclass that provides a list of all the elements of a type.
-/
class Listable (α : Type u) where
  elems : List α
  elemsComplete : ∀ (a : α), a ∈ elems

instance : Listable Bool where
  elems := [false, true]
  elemsComplete := by
    intro a
    cases a <;> simp

/-!
After defining a typeclass, we generally define functions that allow access to the fields of the typeclass.
-/

def elemsList (α : Type u) [Listable α] : List α :=
  Listable.elems

theorem memElemList
    {α : Type u} [Listable α] (a : α) : a ∈ elemsList α :=
  Listable.elemsComplete a

/-
[1, 3, 3, 9, 5, 15]
-/
#eval List.flatMap  (fun x => [x, x * 3]) [1, 3, 5]

/--
The product of `Listable` types is `Listable`.
-/
instance prodListable {α β : Type u}
    [Listable α] [Listable β] : Listable (α × β) where
  elems :=
      let as := elemsList α
      let bs := elemsList β
      -- as.flatMap fun a => bs.map fun b => (a, b)
      do
        let a ← as
        let b ← bs
        pure (a, b)
  elemsComplete := by
    intro (a, b)
    simp [List.mem_flatMap, memElemList]


/-
List.mem_flatMap.{u_1, u_2} {α : Type u_1} {β : Type u_2} {f : α → List β} {b : β} {l : List α} :
  b ∈ l.flatMap f ↔ ∃ a ∈ l, b ∈ f a
-/
#check List.mem_flatMap
/-!
## Application of listable

Suppose `α` is Listable and `f, g: α → ℕ` are functions. Then we can decide (algorithmically) if `f  = g `. This is impossible for `α = ℕ` and `f, g` arbitrary.

Having decision procedures is captured by the `Decidable` typeclass. This gives a Boolean-valued function `decide`.
-/
/-
false
-/
#eval decide (1 = 3)

/-
instDecidableEqNat 1 3
-/
#synth Decidable (1 = 3)

namespace NatFns

def f (n : ℕ) : ℕ := n + 1

def g (n : ℕ) : ℕ := n + 2

/--
error: failed to synthesize
  Decidable (f = g)

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#eval decide (f = g)

end NatFns


namespace FinFns

def f (n : Fin 5) : ℕ := n.val + 1

def g (n : Fin 5) : ℕ := n.val + 2

/-
false
-/
#eval decide (f = g)

end FinFns

/-!
We will use Listable to make a similar decision procedure.
-/

/-
inductive Decidable : Prop → Type
number of parameters: 1
constructors:
Decidable.isFalse : {p : Prop} → ¬p → Decidable p
Decidable.isTrue : {p : Prop} → p → Decidable p
-/
#print Decidable

/-
@[reducible] def DecidableEq.{u} : Sort u → Sort (max 1 u) :=
fun α ↦ (a b : α) → Decidable (a = b)
-/
#print DecidableEq

/--
`decidableFunctionEqual` is a function that takes two functions `f` and `g` of type `α → β`, and a list `l` of type `List α`, and returns a decidable proposition stating whether the two functions are equal on all elements of the list.
-/
def List.decidableFunctionEqual {α β : Type}[DecidableEq β]
    (f g : α → β) (l: List α) : Decidable (∀ x ∈ l,  f x = g x) :=
  by
    induction l with
    | nil =>
      apply Decidable.isTrue
      simp
    | cons h tail ih =>
      if p: f h = g h then
        simp [p]
        exact ih
      else
        apply Decidable.isFalse
        intro h'
        simp [p] at h'

/--
Given two functions with domains the same `Listable` type and codomains equal with decidable equality, we can decide if they are equal.
-/
instance decidableEqFns_of_Listable {α β : Type}
    [Listable α] [DecidableEq β]
    (f g : α → β) : Decidable (f = g) := by
  if p: ∀x ∈ (elemsList α), f x = g x then
    apply Decidable.isTrue
    funext x
    apply p x
    apply memElemList
  else
    apply Decidable.isFalse
    intro h
    apply p
    simp [h]

instance : Listable (ShortAnswer) where
  elems := [ShortAnswer.yes, ShortAnswer.no, ShortAnswer.maybe]
  elemsComplete := by
    intro a
    cases a <;> simp

#check ShortAnswer.not


/-
false
-/
#eval decide (ShortAnswer.not = id)

#eval decide (ShortAnswer.or = fun _ _ => ShortAnswer.yes) -- false

namespace ShortAnswerEg

def f : ShortAnswer × ShortAnswer → ShortAnswer
  | (ShortAnswer.yes, ShortAnswer.yes) => ShortAnswer.yes
  | (ShortAnswer.yes, ShortAnswer.no) => ShortAnswer.yes
  | (ShortAnswer.yes, ShortAnswer.maybe) => ShortAnswer.yes
  | (ShortAnswer.no, ShortAnswer.yes) => ShortAnswer.yes
  | (ShortAnswer.no, ShortAnswer.no) => ShortAnswer.no
  | (ShortAnswer.no, ShortAnswer.maybe) => ShortAnswer.maybe
  | (ShortAnswer.maybe, ShortAnswer.yes) => ShortAnswer.yes
  | (ShortAnswer.maybe, ShortAnswer.no) => ShortAnswer.maybe
  | (ShortAnswer.maybe, ShortAnswer.maybe) => ShortAnswer.maybe

def g : ShortAnswer × ShortAnswer → ShortAnswer
  | (ShortAnswer.yes, ShortAnswer.yes) => ShortAnswer.yes
  | (ShortAnswer.yes, ShortAnswer.no) => ShortAnswer.yes
  | (ShortAnswer.yes, ShortAnswer.maybe) => ShortAnswer.yes
  | (ShortAnswer.no, ShortAnswer.yes) => ShortAnswer.yes
  | (ShortAnswer.no, ShortAnswer.no) => ShortAnswer.no
  | (ShortAnswer.no, ShortAnswer.maybe) => ShortAnswer.maybe
  | (ShortAnswer.maybe, ShortAnswer.yes) => ShortAnswer.yes
  | (ShortAnswer.maybe, ShortAnswer.no) => ShortAnswer.maybe
  | (ShortAnswer.maybe, ShortAnswer.maybe) => ShortAnswer.maybe

#eval decide (f = g) -- true

end ShortAnswerEg
