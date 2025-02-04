import PfsProgs25.Unit06.MyInductives
/-!
# Logic: Curry-Howard Correspondence and Natural numbers

The foundations of Lean represent "all" of Mathematics. This means:

* The Curry-Howard correspondence: proofs are programs, propositions are types; allows **logical connectives** to be represented and **rules of deduction** to be implemented.
* The basic objects of Mathematics are constructed in terms of **inductive types**.
* The basic relations of Mathematics are constructed in terms of **inductive types**.

We will illustrate the latter two points in the context of **Natural numbers**.

## Classical logic: example Natural Numbers

* A **language** is a set of **constants**, (n-ary) **functions**, (n-ary) **predicates** (relations).
  * For natural numbers:
    * Constant: `0`
    * Functions: `succ`, `+`, `×`
    * Predicates: `=`, `≤`
* Mathematical objects: **Terms**, are built from
  * Constants
  * Variables: fixed (countably infinite) set of variables `x₀`, `x₁`, ...
  * Functions applied to terms
* Properties, i.e., **Formulas** are built from
  * Predicates applied to terms
  * Logical connectives: `∧`, `∨`, `¬`, `→`, `↔`
  * Quantifiers: `∀`, `∃`
* Theory: **Axioms** are formulas that are assumed to be true.
  * For natural numbers: Peano axioms
  * We also include **logical axioms**, example *excluded middle*.
* Deduction rules: **Proofs** are constructed from
  * Rules of inference: Modus ponens, i.e., `A → B`, `A` implies `B`., Generalization, i.e., `A` implies `∀ x, A`.
-/
/-
⊢ ∀ (p : Prop), p ∨ ¬p
-/
#check Classical.em
/-
⊢ ∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α), f x = g x) → f = g
-/
#check funext

/-!
## Logic in Lean

* **Propositions** are types.
* **Proofs** are terms.
* The logical connectives are inductive types or constructions from inductive types:
  * Implicication is represented by `A → B` is a function from `A` to `B`.
  * `False`, `True`
  * `And`, `Or`
  * `Not` is `A → False`
  * `forall`, `exists`
-/
/-
structure Iff (a b : Prop) : Prop
number of parameters: 2
fields:
  Iff.mp : a → b
  Iff.mpr : b → a
constructor:
  Iff.intro {a b : Prop} (mp : a → b) (mpr : b → a) : a ↔ b
-/
#print Iff
/-
structure And (a b : Prop) : Prop
number of parameters: 2
fields:
  And.left : a
  And.right : b
constructor:
  And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
-/
#print And
/-
inductive Or : Prop → Prop → Prop
number of parameters: 2
constructors:
Or.inl : ∀ {a b : Prop}, a → a ∨ b
Or.inr : ∀ {a b : Prop}, b → a ∨ b
-/
#print Or
/-
def Not : Prop → Prop :=
fun a ↦ a → False
-/
#print Not

/-!
### Quantifiers

* `∀ x : α, P x` is `(x : α) → P x`.
* `∃ x : α, P x` is `∃ x, P x` or `Exists (fun x => P x)`.
  * A proof of existence is a pair consisting of
    * `x : α` for which `P x` holds.
    * A proof (witness) that `P x` holds.
-/

def forall_example := (x : Nat) → x = x

/-
def forall_example : Prop :=
∀ (x : Nat), x = x
-/
#print forall_example

def exists_example := Exists (fun x : Nat => x = x)

/-
inductive Exists.{u} : {α : Sort u} → (α → Prop) → Prop
number of parameters: 2
constructors:
Exists.intro : ∀ {α : Sort u} {p : α → Prop} (w : α), p w → Exists p
-/
#print Exists
/-
def exists_example : Prop :=
∃ x, x = x
-/
#print exists_example

/-!
## Constructing the Language of Natural Numbers

* Our rules should allow us to constuct the "set" of natural numbers.
* We should be able to define the operations on natural numbers.
* We should be able to define the relations on natural numbers.
* We should be able to represent the axioms of Peano arithmetic, including the induction *axiom schema*.
* Our constructions should be such that all the axioms are theorems.
-/
#check MyNat.add

namespace MyNat

def mul (m n : MyNat) : MyNat :=
  match m with
  | zero => zero
  | succ m' => add n (mul m' n)

/-!
The subtle point is to define relations such as `≤` and `=`. These are *indexed* inductive types.
-/
inductive le : MyNat → MyNat → Prop where
| refl (n : MyNat) : le n n
| step (m n : MyNat) : le m n → le m (succ n)

def one := succ zero
def two := succ one

instance : LE MyNat where
  le := le

example : zero ≤ two := by
  apply le.step
  apply le.step
  apply le.refl

theorem zero_le (n : MyNat) : zero ≤ n := by
  induction n with
  | zero => apply le.refl
  | succ n ih =>
    apply le.step
    exact ih

theorem le_refl (n : MyNat) : n ≤ n := by
  apply le.refl

/-!
The induction principle encodes not only that `refl` and `step` are constructors of `le`, but also that they are the only ways to prove `le`.
-/

/-!
Transitivity of `≤` is a theorem.
-/
theorem le_trans {m n k : MyNat} : m ≤ n → n ≤ k → m ≤ k := by
  intro h₁ h₂
  cases h₁
  case refl =>
    assumption
  case step n h₃ =>
    induction h₂ with
    | refl =>
      apply le.step
      assumption
    | step l h₄ ih =>
      apply le.step
      apply ih

/-!
## What is recursion?

When an inductive type like `MyNat` is defined, the following are automatically defined:
* `MyNat`
* Its constructors: `zero`, `succ`
* Recursion principle: `MyNat.rec`

Further, some equality principles are automatically defined:
-/
/-
⊢ {motive : MyNat → Sort u} → motive zero → ((n : MyNat) → motive n → motive n.succ) → (t : MyNat) → motive t
-/
#check MyNat.rec

/-!
For defining functions from `MyNat` to `MyNat`, we have a simple "motive".
-/
#check rec (motive:= fun _ => MyNat)

noncomputable def fctrl : MyNat → MyNat :=
  rec one (fun n p => mul (succ n) p)

example : fctrl zero = one := rfl

example {n : MyNat} : fctrl (succ n) = mul (succ n) (fctrl n) := rfl

/-
rec : Nat → (MyNat → Nat → Nat) → MyNat → Nat
-/
#check rec (motive:= fun _ => Nat)
