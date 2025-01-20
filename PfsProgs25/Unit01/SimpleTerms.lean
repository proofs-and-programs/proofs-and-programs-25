/-!
# The Lean Context

* "Everything" in Lean is a term. Terms have types.
* Terms include:
  * numbers, strings
  * functions
  * lists
  * propositions (logical statements)
  * proofs
  * types
* We can form expressions for terms and types.
* We make two kinds of *judgements*:
  * term `a` has type `α`.
  * terms `a` and `b` are equal by definition.
* The context has terms with names.
-/

/-!
## Simple Terms and Types

We consider a few terms and types in Lean. These are definitions that do not involve recursion/induction or propositions.

The `#check` command displays the type of a term.
-/
#eval 2 + 3 -- 5

#check 2 + 3 -- Nat

#check "Hello, Lean!" -- String

#check (2: Int) + 3 -- Int

#eval (0: Int) - 1 + 1 -- 1

#eval 0 - 1 + (1: Int) -- 0

#check Nat -- Type

#check Int -- Type

#check Type -- Type 1

def two : Nat := 2

def five := two + 3

#check two -- Nat

#check five -- Nat

#eval five -- 5

/-- error: 'two' has already been declared -/
#guard_msgs in
def two : Int := 2

/-!
## Function types

If `α` and `β` are types, then `α → β` is the type of functions from `α` to `β`.
-/
#check Nat → Nat -- Type

/--
The cube of a natural number.
-/
def cube (n: Nat) : Nat := n * n * n

#check cube -- Nat → Nat

#eval cube 3 -- 27

-- We can only evaluate terms of types for which we have a nice string representation.
/--
error: could not synthesize a 'Repr' or 'ToString' instance for type
  Nat → Nat
-/
#guard_msgs in
#eval cube

/-
def cube : Nat → Nat :=
fun n ↦ n * n * n
-/
#print cube

/--
A generic function to compute the cube of a number. This defines the cube for a type `α` with a multiplication operation.
-/
def cubeGeneric {α: Type} [Mul α]
  (n: α) : α := n * n * n

set_option pp.all true in
#print cubeGeneric

#eval cubeGeneric (-2 : Int) -- -8

#synth Mul Int -- Int.instMul


#eval @cubeGeneric Int Int.instMul  (-2 : Int) -- -8

#eval @cubeGeneric _ _  (-2 : Int) -- -8

#eval cubeGeneric (α := Int)  (-2 : Int) -- -8

#check Mul

def myMul : Mul Int :=
  {mul (m n : Int) := m + n}

#eval @cubeGeneric _ myMul  (-2 : Int) -- -6

/--
The cube of a natural number, using a lambda expression.
-/
def cube' : Nat → Nat :=
  fun n ↦ n * n * n -- can use `=>` instead of `↦`

#eval cube' 3 -- 27

/--
The cube of a natural number, using a lambda expression with argument type specified.
-/
def cube'' := fun (n : Nat) ↦ n * n * n
#check cube'' -- Nat → Nat

/--
error: don't know how to synthesize placeholder for argument 'n'
context:
⊢ Nat
-/
#guard_msgs in
#eval cube _

/-!
## Curried functions

Suppose we want to define the function `f` of two variables `a` and `b` taking value `a + b + 1`. We can define it as a function of one variable `a` returning a function of one variable `b`.
-/

/--
The function of two variables `a` and `b` taking value `a * a + b * b`, defined as an iterated lambda.
-/
def sum_of_squares : Nat → Nat → Nat :=
  fun a ↦ fun b ↦ a * a + b * b

#eval sum_of_squares 3 4 -- 25

/--
The function of two variables `a` and `b` taking value `a * a + b * b`, using arguments in a single pair of parentheses.
-/
def sum_of_squares' (a b : Nat) : Nat :=
  a * a + b * b

#eval sum_of_squares' 3 4 -- 25

/--
The function of two variables `a` and `b` taking value `a * a + b * b`, using a lambda expression with two arguments.
-/
def sum_of_squares'' : Nat → Nat → Nat :=
  fun a b ↦ a * a + b * b

/--
The function of two variables `a` and `b` taking value `a * a + b * b`, using a lambda expression with two arguments and type annotations for one. The other type is inferred.
-/
def sum_of_squares'''  :=
  fun (a : Nat) b ↦ a * a + b * b

#check sum_of_squares''' -- Nat → Nat → Nat

example :=
    fun (a : Nat) (b : Int) ↦ a * a + b * b

/-!
We used typeclasses above. We will discuss them later. For now, note that they are simply types or type families. However, there are plenty of type families that are not typeclasses.
-/
#check List -- Type u → Type u
#check List Nat -- Type
#check Mul -- Type u → Type u
#check Inhabited -- Type u → Type u

/-!
## Implicit parameters

A function parameter may be implicit. This means that it is inferred by Lean from *consistency of types*. We can make a parameter implicit by enclosing it in curly braces `{}`.

A typeclass parameter is always implicit.

If we prefix a function application with `@`, then we must provide all implicit parameters explicitly. Conversely, we can use `_` for an explicit parameter to make it implicit.
-/
def doubleList {α: Type} (l: List α) : List α := l ++ l

/-!
When calling the function `doubleList`, we give only one argument, the list `l`. The type `α` is inferred from the type of `l`.
-/
#eval doubleList [1, 2, 3] -- [1, 2, 3, 1, 2, 3]


def doubleList' (α : Type) (l: List α ) : List α :=
  l ++ l

/-!
When calling the function `doubleList'`, we must provide the type `α` explicitly.
-/
#eval doubleList' Nat [1, 2, 3] -- [1, 2, 3, 1, 2, 3]

/-!
When calling, we can make all parameters explicit or leave some explicit parameters to be deduced.
-/
#eval @doubleList Nat [1, 2, 3] -- [1, 2, 3, 1, 2, 3]

#eval doubleList' _ [1, 2, 3] -- [1, 2, 3, 1, 2, 3]

def doubleList''' := fun {α: Type} =>
  fun (l: List α) => l ++ l

-- set_option autoImplicit false in
def doubleList''  (l: List α){α: Type}  := l ++ l
#check doubleList''

#eval doubleList' (l := [1, 2, 3]) (α := Nat) -- [1, 2, 3, 1, 2, 3]
