/-!
# Inductive types for numbers, data, propositions.

What makes the foundations we use work are that the mathematical objects we need as well as their properties can be constructed in terms of inductive types and dependent function types. Similarly, proofs and terms need only a few rules to be constructed.

We will see how to define inductive types for many basic constructions: natural numbers, products, sums (disjoint unions) etc. We will also see the logical connectives `∧` and `or` as well as quantifiers constructed as inductive types. Further, we see how specific relations like `≤` can be defined as (indexed) inductive types.
-/

/--
The natural numbers are defined inductively.
-/
inductive MyNat where
| zero : MyNat
| succ (n : MyNat) : MyNat
deriving Repr

/-
MyNat.succ (MyNat.succ (MyNat.zero))
-/
#eval MyNat.succ (MyNat.succ MyNat.zero)

-- The namespace command means `MyNat` is added as a prefix to all the names defined in the `MyNat` namespace.
namespace MyNat

/--
The addition function on natural numbers.
-/
def add : MyNat → MyNat → MyNat
| zero, m => m
| succ n, m => succ (add n m)

/-
MyNat.succ (MyNat.succ (MyNat.succ (MyNat.zero)))
-/
#eval succ zero |>.add <| succ  <| succ zero


/--
The addition operation `+` on natural numbers.
-/
instance : Add MyNat where
  add := add
    -- fun a b => add a b
    -- fun a b ↦ a.add b

#eval (succ zero) + (succ (succ zero))

/--
Addition on the left by zero. This is by definition.
-/
theorem zero_add (n : MyNat) : zero + n = n := by
  rfl

/--
Addition on the right by zero. This is by induction on `n`.
-/
theorem add_zero (n : MyNat) : n + zero = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show add (succ n) zero = succ n
    unfold add
    simp
    exact ih

infix:65 " #+# " => add -- a new notation for addition

/-
MyNat.succ (MyNat.succ (MyNat.succ (MyNat.zero)))
-/
#eval (succ zero) #+# (succ (succ zero))

end MyNat

universe u v

/--
The product type is defined as an inductive type.
-/
inductive MyProd (α : Type u) (β : Type v) where
| pair (fst : α) (snd : β) : MyProd α β

/--
The product type is defined as a structure.
-/
structure MyProd' (α : Type u) (β : Type v) where
  fst : α
  snd : β

example : MyProd Nat Nat := MyProd.pair 1 2

example : MyProd' Nat Nat := ⟨1, 2⟩

example : MyProd' Nat Nat := {fst := 1, snd := 2}

example : MyProd Nat String := MyProd.pair 1 "hello"

/--
The first projection of a product.
-/
def MyProd.fst {α : Type u} {β : Type v} : MyProd α β → α
| MyProd.pair a _ => a

/--
The second projection of a product.
-/
def MyProd.snd {α : Type u} {β : Type v} : MyProd α β → β
| MyProd.pair _ b => b

#eval MyProd.fst (MyProd.pair 1 2) -- 1

/-
MyProd.fst.{u, v} {α : Type u} {β : Type v} : MyProd α β → α
-/
#check MyProd.fst

/-
MyProd'.fst.{u, v} {α : Type u} {β : Type v} (self : MyProd' α β) : α
-/
#check MyProd'.fst

/--
The sum type, i.e., *disjoint union* is defined as an inductive type.
-/
inductive MySum (α : Type u) (β : Type v) where
| inl (a : α) : MySum α β
| inr (b : β) : MySum α β

/--
An example of a term in a sum type.
-/
def MySum.eg₁ : MySum Nat String := MySum.inl 1

/--
An example of a term in a sum type.
-/
def MySum.eg₂ : MySum Nat String := MySum.inr "hello"

#check MySum.eg₁ -- MySum Nat String

#check MySum.eg₂ -- MySum Nat String

/--
The Unit type, with a unique element, is defined inductively.
-/
inductive MyUnit where
| star : MyUnit

def MyUnit.eg : MyUnit := MyUnit.star

#check MyUnit.eg -- MyUnit

/--
The empty type is defined inductively.
-/
inductive MyEmpty where

/--
The false proposition is defined as an inductive type.
-/
inductive MyFalse where

/--
The conjunction of two propositions is defined as an inductive type.
-/
inductive MyAnd (a b : Prop) where
| mk (left : a) (right : b) : MyAnd a b

/--
The disjunction of two propositions is defined as an inductive type.
-/
inductive MyOr (a b : Prop) where
| inl (left : a) : MyOr a b
| inr (right : b) : MyOr a b

/--
The true proposition is defined as an inductive type.
-/
inductive MyTrue where
| trivial : MyTrue

/--
The existential quantifier is defined as an inductive type.
-/
inductive MyExists {α : Type u} (p : α → Prop) where
| mk (w : α) (h : p w) : MyExists p
