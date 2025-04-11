/-!
# Monads

Monads `m: Type u → Type v` are a common structure for sequencing computations that can:

* involve elements in a collection such as a list `List`,
* fail or have no result, such as `Option`,
* depend on and alter state, such as `StateM`,
* take a long time, such as `Task`,
* have side effects, such as `IO`,
...

## Operations

Monads have the following operations:

* `pure : α → m α` lifts a value into the monad; `return` is closely related.
* `bind : m α → (α → m β) → m β` sequences two computations, also called `flatMap` in concrete cases.
* `map : (α → β) → m α → m β` applies a function to the result of a computation.
* `flatten : m (m α) → m α` collapses nested monadic layers.

These are not independent. The definition of monads only requires `pure` and `bind`, but `map` and `flatten` can be defined in terms of them.

## Do notation

The value of monads is that we can use the `do` notation to avoid explicitly writing `bind` and `pure`. Formally, a `do` block is just syntax for a **term** in Lean, with type of the form `m α` for some `α`. The `do` block is translated into a series of `bind` and `pure` calls.
-/
/-!
## Example: `Stack`

This is just like a list but we put elements at the end.
-/
inductive Stack (α : Type) where
  | empty : Stack α
  | push : Stack α → α → Stack α
deriving Inhabited, Repr

def Stack.last? {α: Type} : Stack α → Option α
  | Stack.empty => none
  | Stack.push _ a => some a

namespace Stack

def pop? {α : Type} : Stack α → Option (Stack α × α)
  | Stack.empty => none
  | Stack.push s a => some (s, a)

def eg : Stack Nat := (empty).push 1 |>.push 2 |>.push 3

#eval eg.last?

#eval eg

def pure {α : Type} (a : α) : Stack α := Stack.push Stack.empty a

def map {α β : Type} (f : α → β) (s : Stack α) : Stack β :=
  match s with
  | Stack.empty => Stack.empty
  | Stack.push s a => Stack.push (map f s) (f a)

def eg2 : Stack Nat := eg.map (fun x => x * x + 1)

/-
Stack.push (Stack.push (Stack.push (Stack.empty) 2) 5) 10
-/
#eval eg2

def eg₃ : Stack Bool := eg.map (fun x => x % 2 = 0)

#eval eg₃

/-
protected def Option.map.{u_1, u_2} : {α : Type u_1} → {β : Type u_2} → (α → β) → Option α → Option β :=
fun {α} {β} f x ↦
  match x with
  | some x => some (f x)
  | none => none
-/
#print Option.map

def append {α : Type} (s₁ s₂ : Stack α) : Stack α :=
  match s₂ with
  | Stack.empty => s₁
  | Stack.push s a => s₁.append s |>.push a

def flatten {α : Type} (ss : Stack (Stack α)) : Stack α :=
  match ss with
  | Stack.empty => Stack.empty
  | Stack.push ss s => ss.flatten.append s

def flatMap {α β : Type} (f : α → Stack β)
    (s : Stack α) : Stack β :=
  flatten (map f s)

instance  : Monad Stack where
  pure := pure
  bind := fun s f => flatMap f s

end Stack
/-!
## Why flatten: example
-/

namespace Monads
def half? (n : Nat) : Option Nat :=
  if n % 2 = 0 then some (n / 2) else none

/-!
In the following, `flatMap` is used to apply `half?` to the result of `half?`. However, do notation lets us get it conveniently.

First we see a naive version using `map`.
-/

def quarter?? (n : Nat) : Option <| Option Nat :=
  half? n |>.map half?

#eval quarter?? 8

/-
some none
-/
#eval quarter?? 6

def quarter? (n : Nat) : Option Nat := do
  let n' ← half? n -- extract the value from the `Option` (or Monad)
  let n'' ← half? n'
  return n''

def quarter?' (n : Nat) : Option Nat :=
  half? n |>.bind half?

/-!
A simple monad is `Id`, which is just the identity function. It is useful for writing `do` blocks that do not involve any monadic operations.
-/
end Monads
