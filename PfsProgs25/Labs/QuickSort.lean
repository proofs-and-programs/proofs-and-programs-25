import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
## Quicksort Algorithm (Pivot from Head)

In this lab, we will prove additional properties of the quicksort algorithm. To make this self-contained, we are including again some definitions.
-/


variable {α : Type}[LinearOrder α]

def smaller (pivot : α) (l : List α) : List α :=
  l.filter (fun x => x ≤  pivot)

def larger (pivot : α) (l : List α) : List α :=
  l.filter (fun x => x > pivot)


/--
The `quickSort` function that performs the quicksort algorithm. We prove termination for this function.
-/
def quickSort : List α → List α
  | [] => []
  | pivot :: l =>
    have h₁ : (smaller pivot l).length < (pivot :: l).length := by
      simp [List.length_cons]
      apply Nat.succ_le_succ
      apply List.length_filter_le
    have h₂ : (larger pivot l).length < (pivot :: l).length := by
      simp [List.length_cons]
      apply Nat.succ_le_succ
      apply List.length_filter_le
    (quickSort (smaller pivot l)) ++ pivot :: (quickSort (larger pivot l))
termination_by l => l.length

@[simp]
theorem quickSort_nil : quickSort ([] : List α) = [] := by
  simp [quickSort]

@[simp]
theorem quickSort_cons (pivot : α) (l : List α) :
    quickSort (pivot :: l) = (quickSort (smaller pivot l)) ++
    pivot :: (quickSort (larger pivot l)) := by
  simp [quickSort]

/-!
Exercise 1: Prove that the result of `quickSort` has the same elements as the input list including *multiplicity*. You may want to use the `funext` tactic (saying functions are equal iff they are equal at all values).
-/
theorem quickSort_count_eq (l : List α) : (quickSort l).count  = l.count  := by
  sorry

/--
An inductive definition of a sorted list. A list is sorted if it is empty, has one element, or if the first two elements are in order and the tail is sorted.
-/
inductive Sorted : List α → Prop
  | nil : Sorted []
  | singleton (x : α) : Sorted [x]
  | step (x y : α) (l : List α) (hxy: x ≤ y)
      (tail_sorted: Sorted (y :: l)) : Sorted (x :: y :: l)

/-!
Exercise 2: We prove that the head of a sorted list is less than or equal to the elements in the tail of the list.
-/
theorem sorted_head_le {x: α} {ys: List α} (h: Sorted (x::ys)) :
    ∀ y ∈ ys, x ≤ y := by
  sorry

/-!
Exercise 3: The tail of a sorted list is sorted.
-/
theorem sorted_tail {x: α} {ys: List α} (h: Sorted (x::ys)) :
    Sorted ys := by
  sorry

/-!
Exercise 4: If the head of a list is less than or equal to the elements in the tail of the list and the tail is sorted, then the list is sorted.
-/
theorem sorted_of_head_le_tail_sorted {x: α} {ys: List α}
    (h: ∀ y∈ ys, x ≤ y) (h': Sorted ys) :
    Sorted (x::ys) := by
  sorry
