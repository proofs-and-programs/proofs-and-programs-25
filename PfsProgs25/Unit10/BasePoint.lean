import Mathlib
import PfsProgs25.Unit04.ShortAnswer

/-!
#Typeclasses

Typeclasses are (parametrized) types that can be used as implicit arguments. Terms of such types are called *instances*.

What is special about these are:
* Instances can be *synthesized* by Lean.
* It is expected that an instance, if it exists, is unique for a given type.

Formally, a class is a type defined with the same syntax as a structure, but with the `class` keyword. The instances are defined with the `instance` keyword.
-/

class Alone where
  (alone : Bool)

/--
error: failed to synthesize
  Alone

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Alone

instance : Alone := ⟨true⟩

/-!
At its simplest, typeclass synthesis is just search.
-/
#synth Alone -- instAlone

instance extra : Alone := ⟨false⟩

#synth Alone -- extra

example : Alone := inferInstance -- infers the instance of the typeclass

/-
Alone.alone [self : Alone] : Bool
-/
#check Alone.alone

def myAlone {alone: Alone} : Bool := alone.alone

set_option pp.mvars.anonymous false in
/--
error: don't know how to synthesize implicit argument 'alone'
  @myAlone ?_
context:
⊢ Alone
-/
#guard_msgs in
#eval myAlone -- true

/-!
Parameters with type typeclasses can be inferred. This is stronger than implicit arguments. Implicit arguments are inferred from the type.
-/
#eval Alone.alone -- false

/-!
The `class` syntax is just a shorthand for defining a structure with one field and **annotating** it. Annotations modify the environment, but do not affect the elaboration process. More precisely, they modify *environmental extensions*.
-/
@[class]
structure Alone' where
  (alone : Bool)

instance : Alone' := ⟨true⟩

#synth Alone' -- instAlone'

#check Alone'.alone -- Alone'.alone : Bool

/-!
We can also have inductive typeclasses.
-/
class inductive Alone'' where
| mk : Bool → Alone''

/-!
## BasePoint class

This associates a basepoint to a type.
-/
class BasePoint (α : Type u) where
  (basePoint : α)

instance : BasePoint String := ⟨"hello"⟩

#synth BasePoint String -- instBasePointString

/--
Gives the basepoint of a type with a `BasePoint` instance.
-/
def basePoint (α : Type u)[BasePoint α] : α := BasePoint.basePoint

#eval basePoint String -- "hello"

instance {α : Type u} : BasePoint (List α) := ⟨[]⟩

#synth BasePoint (List Nat) -- inst

#eval basePoint (List Nat) -- []

instance prodBasePoint {α β : Type u}
    [BasePoint α] [BasePoint β] : BasePoint (α × β) := ⟨(basePoint α, basePoint β)⟩

#eval basePoint (String × String × (List Bool)) -- ("hello", "hello", [])

/-
class Zero.{u} (α : Type u) : Type u
number of parameters: 1
fields:
  Zero.zero : α
constructor:
  Zero.mk.{u} {α : Type u} (zero : α) : Zero α
-/
#print Zero

#synth Zero Nat -- instZeroNat

#eval (Zero.zero : Nat) -- 0

instance basePointZero {α : Type u} [Zero α] :
    BasePoint α := ⟨Zero.zero⟩

#eval basePoint Nat -- 0

#synth BasePoint (Nat × Nat) -- prodBasePoint

instance idBasePoint {α : Type u} :
    BasePoint <| α → α := ⟨(id : α → α)⟩

#eval basePoint (Nat → Nat) 1 -- 1

instance (priority := low) codomainBasePoint {α β : Type u} [BasePoint β] :
    BasePoint <| α → β := ⟨(fun _ => basePoint β)⟩

#eval basePoint (Nat → Nat) 1 -- 1

#eval basePoint (Bool → Bool) true -- true

/-
ShortAnswer.yes
-/
#eval basePoint (ShortAnswer → ShortAnswer) (.or .yes .no)

#eval basePoint
  ((ShortAnswer × String) → ShortAnswer → ((ShortAnswer → ShortAnswer) × String)) (.or .yes .no, "hello") .no
  |>.snd -- "hello"

/-!
## Useful typeclasses
-/
/-
class Add.{u} (α : Type u) : Type u
number of parameters: 1
fields:
  Add.add : α → α → α
constructor:
  Add.mk.{u} {α : Type u} (add : α → α → α) : Add α
-/
#print Add

/-
class HAdd.{u, v, w} (α : Type u) (β : Type v) (γ : outParam (Type w)) : Type (max (max u v) w)
number of parameters: 3
fields:
  HAdd.hAdd : α → β → γ
constructor:
  HAdd.mk.{u, v, w} {α : Type u} {β : Type v} {γ : outParam (Type w)} (hAdd : α → β → γ) : HAdd α β γ
-/
#print HAdd


/--
error: failed to synthesize
  HAdd String Bool ?_

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option pp.mvars.anonymous false in
#eval "Hello, " + true

instance : HAdd String Bool String := ⟨fun s b =>
  if b then s else "Did you really mean: "++ s⟩

/-
"Hello"
-/
#eval "Hello" + true

/-
"Did you really mean: Hello"
-/
#eval "Hello" + false

section silent

-- This is already defined in Lean. Made local to avoid clashes
local instance {α : Type}[Add α] : HAdd α α α := ⟨Add.add⟩

end silent

/-
inductive Decidable : Prop → Type
number of parameters: 1
constructors:
Decidable.isFalse : {p : Prop} → ¬p → Decidable p
Decidable.isTrue : {p : Prop} → p → Decidable p
-/
#print Decidable

/-
def Decidable.decide : (p : Prop) → [h : Decidable p] → Bool :=
fun p [h : Decidable p] ↦ Decidable.casesOn h (fun x ↦ false) fun x ↦ true
-/
#print decide
