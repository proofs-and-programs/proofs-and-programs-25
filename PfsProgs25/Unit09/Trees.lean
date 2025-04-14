import Mathlib

/-!
## Inductive types and trees

As we have seen, inductive types are given by constructors. To fully understand these, we must understand:

* What are the allowed types of the constructors?
* What are the corresponding types of the `rec` functions?
* What identities are satisfied by these?

Since the constructs give elements of `T`, they must be (dependent) functions with codomain `T`, or (dependent) functions with codomain (dependent) functions with codomain `T`, etc. Thus, possible types of constructors are:

* `T`.
* If `X` (`= ... → T`) is a possible type and `A` is defined in the context, then `A → X`.
* If `X` (`= ... → T`) is a possible type, then `T → X`.
* If `X` (`= ... → T`) is a possible type and `A` is defined in the context, then `(A → T) → X` is a possible type (we can generalize to `A → B → T` etc. and families).

## Parameterized inductive types

We also have *parametrized* inductive types like lists, where we are defining a family of types `List α` for each `α`. In this case, the constructors can depend on the parameter `α`.

To be precise, a *family of types* is one of:

* A type `T : Type u`.
* Given a type `A` and a family of types `X`, the type `A → X`.
* Given a type `A`, and, for each `a : A`, a family of types `X a`, the type `Π (a : A), X a = (a: A) → X a`.
* Given a type `A` and a family of types `X`, the type `List A → X` (this is in Lean, but not, for example in *Homotopy Type Theory*).

## Indexed inductive types

This is a more subtle notion. We will return to this later. We have already seen an example of this: `MyNat.le` is an indexed inductive type.

## Trees

We see various kinds of trees, giving various inductive types.
-/

/--
A simple binary tree.
-/
inductive BinTree (α : Type) where
  | leaf (label: α) : BinTree α
  | node : BinTree α → BinTree α → BinTree α
deriving Inhabited, Repr

namespace BinTree

def eg₁ : BinTree ℕ  := leaf 3

def eg₂ : BinTree ℕ := node (leaf 3) (leaf 4)

def eg₃ : BinTree ℕ := node (node (leaf 3) (leaf 4)) (leaf 5)

def toList {α : Type} : BinTree α → List α
  | leaf a => [a]
  | node t₁ t₂ => toList t₁ ++ toList t₂

/-
BinTree.node (BinTree.node (BinTree.leaf 3) (BinTree.leaf 4)) (BinTree.leaf 5)
-/
#eval eg₃

/-
[3, 4, 5]
-/
#eval eg₃.toList

/-
⊢ (ℕ → ℤ) → (BinTree ℕ → BinTree ℕ → ℤ → ℤ → ℤ) → BinTree ℕ → ℤ
-/
#check BinTree.rec (α := ℕ)  (motive := fun _ => ℤ)

/-
⊢ {α : Type} →
  {motive : BinTree α → Sort u} →
    ((label : α) → motive (leaf label)) →
      ((a a_1 : BinTree α) → motive a → motive a_1 → motive (a.node a_1)) → (t : BinTree α) → motive t
-/
#check BinTree.rec

/--
Sum of the labels of a tree.
-/
def sum : BinTree ℕ → ℕ
  | leaf a => a
  | node t₁ t₂ => sum t₁ + sum t₂

noncomputable def sum' : BinTree ℕ → ℕ :=
  BinTree.rec (α := ℕ) (motive := fun _ => ℕ)
    (fun a ↦ a) (fun _t₁ _t₂ sum₁ sum₂ ↦ sum₁ + sum₂)

theorem sum'_leaf (a : ℕ) : sum' (leaf a) = a := rfl

theorem sum'_node (t₁ t₂ : BinTree ℕ) :
  sum' (node t₁ t₂) = sum' t₁ + sum' t₂ := rfl

end BinTree

inductive BinTree' (α : Type) where
  | node : BinTree' α → BinTree' α → BinTree' α
  | leaf (label: α) : BinTree' α
deriving Inhabited, Repr

/-
BinTree'.rec : (BinTree' ℕ → BinTree' ℕ → ℤ → ℤ → ℤ) → (ℕ → ℤ) → BinTree' ℕ → ℤ
-/
#check BinTree'.rec (α := ℕ)  (motive := fun _ => ℤ)

def natListSum : List ℕ → ℕ
  | [] => 0
  | head::tail => head + natListSum tail

/--
A different construction of a binary tree.
-/
inductive BoolTree (α : Type) where
  | leaf (a: α ) : BoolTree α
  | node : (Bool → BoolTree α) → BoolTree α

namespace BoolTree

def eg₁ : BoolTree ℕ := leaf 3

def eg₂ : BoolTree ℕ := node (fun _ => leaf 3)

def eg₃ : BoolTree ℕ :=
  node (fun b => if b then leaf 3 else leaf 4)

/--
The list of labels of a tree.
-/
def toList {α : Type} : BoolTree α → List α
  | leaf a => [a]
  | node f => toList (f true) ++ toList (f false)

/--
The binary tree corresponding to a `BoolTree`.
-/
def toBinTree {α : Type} : BoolTree α  → BinTree α
  | leaf a => BinTree.leaf a
  | node f => BinTree.node (toBinTree (f true)) (toBinTree (f false))

#eval eg₃.toBinTree.toList

/--
The `BoolTree` corresponding to a binary tree.
-/
def ofBinTree {α : Type} : BinTree α → BoolTree α
  | BinTree.leaf a => leaf a
  | BinTree.node t₁ t₂ => node (fun b => if b then ofBinTree t₁ else ofBinTree t₂)

end BoolTree

/--
A tree with a list of trees as children.
This is a more general form of `BinTree` and `BoolTree`.
-/
inductive ListTree (α : Type) where
  | leaf (a: α) : ListTree α
  | node : List (ListTree α) → ListTree α
deriving Inhabited, Repr

namespace ListTree

def eg₁ : ListTree ℕ := leaf 3

def eg₂ : ListTree ℕ := node [leaf 3, leaf 4]

def eg₃ : ListTree ℕ := node [node [leaf 3, leaf 4], leaf 5]

def eg₄ : ListTree ℕ := node []

#eval eg₃

def toList {α : Type} : ListTree α → List α
  | leaf a => [a]
  | node [] => []
  | node (t::ts) => toList t ++ toList (node ts)

#eval eg₃.toList

end ListTree

/-!
Lean is pragmatic and allows imperative programming. We can define the sum of a list. Technically, this is in a monad.
-/
def listSumNat (l: List ℕ) : ℕ := Id.run do
  let mut sum := 0
  for n in l do
    sum := sum + n
  return sum

#check List.foldl

def listSumNat' (l: List ℕ) : ℤ :=
  l.foldl (init := 0) (fun (sum :ℤ) (n : ℕ) => sum + n)

#check List.foldl_eq_foldr

#check List.map

def evens : List ℕ → List Bool :=
  List.map (fun n => n % 2 == 0)

#eval evens [1, 2, 3, 4, 5]

#check ℕ  = String

/--
error: failed to synthesize
  BEq Type

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#check ℕ  == String


def evensProp : List ℕ → List Prop :=
  List.map (fun n => n % 2 = 0)


def listTill : Nat → List Nat
  | 0 => []
  | n+1 => n :: listTill n

#check List.flatMap

def listTillFlat (n: ℕ) : List ℕ :=
  (listTill n).flatMap listTill

/-
[9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
-/
#eval listTill 10


/-
[8, 7, 6, 5, 4, 3, 2, 1, 0, 7, 6, 5, 4, 3, 2, 1, 0, 6, 5, 4, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 4, 3, 2, 1, 0, 3, 2, 1, 0, 2,
  1, 0, 1, 0, 0]
-/
#eval listTillFlat 10

/-
structure Fin (n : ℕ) : Type
number of parameters: 1
fields:
  Fin.val : ℕ
  Fin.isLt : ↑self < n
constructor:
  Fin.mk {n : ℕ} (val : ℕ) (isLt : val < n) : Fin n
-/
#print Fin

/--
A tree with a finite collection of trees as children, indexed by `Fin n`.
-/
inductive FinTree (α : Type) where
  | leaf (a: α) : FinTree α
  | node : {n : ℕ} →  (Fin n → FinTree α) → FinTree α

namespace FinTree

/--
The `FinTree` associated to a binary tree.
-/
def ofBinTree {α : Type} : BinTree α → FinTree α
  | BinTree.leaf a => leaf a
  | BinTree.node t₁ t₂ =>
    let family : Fin 2 → FinTree α := fun k =>
      match k with
      | ⟨0, _pf⟩  => ofBinTree t₁
      | ⟨1, _pf⟩  => ofBinTree t₂
    node family

def eg : FinTree ℕ :=
  let family : Fin 3 → FinTree ℕ := fun k =>
    match k with
    | ⟨0, _⟩ => leaf 3
    | ⟨1, _⟩ => ofBinTree <| .node (.leaf 7) (.leaf 6)
    | ⟨2, _⟩ => node (n := 1) (fun _ => leaf 5)
  node family

end FinTree

/-
FinTree.rec : (ℕ → ℤ) → ({n : ℕ} → (Fin n → FinTree ℕ) → (Fin n → ℤ) → ℤ) → FinTree ℕ → ℤ
-/
#check FinTree.rec (α := ℕ)  (motive := fun _ => ℤ)

/-!
## Cantor's theorem

We illustrate what is **not** allowed in defining inductive types, and why.
-/
namespace CantorTree

/--
error: (kernel) arg #1 of 'CantorTree.T''.node' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
inductive T'' where
  | node : (T'' → Bool) → T''


opaque T': Type

inductive T : Type where
| node : (T' → Bool) → T

axiom TisT' : T = T'

/-!
The idea of Cantor's theorem is to show that we can define `p: T → Bool` such that `p (node p) ≠ p p`. If not for the positivity condition, we could define `p (node x) = ¬ x (node x)`.
-/
def flip : T → Bool
| T.node p => !p (TisT' ▸ (T.node p))

def flip' : T' → Bool := TisT' ▸ flip

theorem flip_contra :
  flip (T.node flip') = ! flip' (TisT' ▸ (T.node flip')) := by rfl

end CantorTree
