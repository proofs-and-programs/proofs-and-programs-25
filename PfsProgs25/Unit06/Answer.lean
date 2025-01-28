import PfsProgs25.Unit04.ShortAnswer
/-!
## Inductive Types

The main type construction in Lean is the inductive type. We will see how to define inductive types and how to define functions by recursion on these types.

We have already seen one special case of inductive types: structures. In `ShortAnswer`, we saw another special case, namely *enumerated types*. We will now see a third special case, namely *non-recursive inductive types*. Finally, we will see the general case, namely *recursive inductive types*.
-/

/--
The `Answer` type is a non-recursive inductive type, with constructors a short answer or a short answer with reason.
-/
inductive Answer where
| just (ans: ShortAnswer) : Answer
| because (ans: ShortAnswer) (reason: String) : Answer

example: Answer := Answer.just ShortAnswer.yes

/--
An example of a term in the `Answer` type.
-/
def Answer.eg₁ : Answer := Answer.because ShortAnswer.yes "I said so"

/--
The short answer to an answer.
-/
def Answer.short (a: Answer) : ShortAnswer :=
  match a with
  | Answer.just ans => ans
  | Answer.because ans _ => ans

#eval Answer.short Answer.eg₁ -- ShortAnswer.yes

open Answer in
#eval short eg₁ -- ShortAnswer.yes

/-!
The **dot** notation.
-/
open Answer in
#eval eg₁.short -- ShortAnswer.yes

/--
A `LongAnswer` is either a `ShortAnswer` or a `LongAnswer` with a reason.
-/
inductive LongAnswer where
| just (ans: ShortAnswer) : LongAnswer
| because (ans: LongAnswer) (reason: String) : LongAnswer

/--
An example of a term in the `LongAnswer` type.
-/
def LongAnswer.eg₁ : LongAnswer := LongAnswer.just ShortAnswer.yes

/--
An example of a term in the `LongAnswer` type.
-/
def LongAnswer.eg₂ : LongAnswer :=
  LongAnswer.because
    (LongAnswer.just ShortAnswer.yes)
    "I said so"

/--
An example of a term in the `LongAnswer` type.
-/
def LongAnswer.eg₃ : LongAnswer :=
  LongAnswer.because
    (LongAnswer.because
      (LongAnswer.just ShortAnswer.yes)
      "I said so")
    "Did you not hear me?"

/-- The short answer to a long answer.
 Lean has convenient notation for pattern matching -/
def LongAnswer.short : LongAnswer → ShortAnswer
| LongAnswer.just ans => ans
| LongAnswer.because ans _ => short ans

/-- The short answer to a long answer.
Expanded definition -/
def LongAnswer.short' : LongAnswer → ShortAnswer :=
  fun a =>
  match a with
  | LongAnswer.just ans => ans
  | LongAnswer.because ans _ => short' ans

/--
The long answer from a short answer.
-/
def ShortAnswer.just (ans: ShortAnswer) : LongAnswer :=
  LongAnswer.just ans

/--
Adding a reason to a long answer.
-/
def LongAnswer.justify (ans: LongAnswer)
  (reason: String) : LongAnswer :=
  LongAnswer.because ans reason

/--
An example of a term in the `LongAnswer` type.
-/
def LongAnswer.eg₄ : LongAnswer :=
  ShortAnswer.yes.just.justify "I said so"

/--
An example of a term in the `LongAnswer` type.
-/
def LongAnswer.eg₅ : LongAnswer :=
  (ShortAnswer.yes.just.justify "I said so").justify "Did you not hear me?"

/--
An example of a term in the `LongAnswer` type.
-/
def LongAnswer.eg₆ : LongAnswer :=
  ShortAnswer.yes.just.justify "I said so"
    |>.justify "Did you not hear me?" |>.justify
    "Please listen next time."

/--
There are no terms of this type.
-/
inductive EmptyAnswer where
| justified (and: EmptyAnswer) (reason: String) : EmptyAnswer

namespace EmptyAnswer
/--
A function from `EmptyAnswer` to `α` for any type `α`. Such a function can only exist if `EmptyAnswer` has no terms.
-/
def mapToType (α : Type) : EmptyAnswer → α := by
  intro a
  match a with
  | justified prev _ =>
    exact mapToType α prev

/--
A function from `EmptyAnswer` to `α` for any type `α`. Such a function can only exist if `EmptyAnswer` has no terms.
-/
noncomputable def mapToType' (α : Type) : EmptyAnswer → α := by
  intro a
  induction a with
  | justified prev j ih =>
    exact ih

/--
error: fail to show termination for
  EmptyAnswer.selfReference
with errors
failed to infer structural recursion:
no parameters suitable for structural recursion

well-founded recursion cannot be used, 'EmptyAnswer.selfReference' does not take any (non-fixed) arguments
-/
#guard_msgs in
def selfReference : EmptyAnswer :=
  justified selfReference "I am talking about myself."

end EmptyAnswer
