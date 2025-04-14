import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
## Quicksort Algorithm (Pivot from Head)

Quicksort is a divide-and-conquer sorting algorithm known for its efficiency. It works by recursively partitioning the list around a chosen element (pivot) and then sorting the sub-lists.

Our implementation of quicksort for lists follows the following steps:

* If the list is empty, return the empty list.
* Otherwise, let `pivot` be the first element (`head`) of the list.
* Let `smaller` be the list of elements smaller (`≤`) than `pivot` and `larger` be the list of elements larger (`>`) than `pivot`.
* Recursively sort `smaller` and `larger` lists and concatenate them with `pivot` in between.

We begin by defining `smaller` and `larger` lists. We define them as abbreviations so that they are automatically unfolded by Lean.
-/


/-!
We define `smaller` and `larger` using `List.filter`. We need some theorems relating to filtering.
-/
#check List.mem_filter -- ∀ {α : Type u_1} {x : α} {p : α → Bool} {as : List α}, x ∈ List.filter p as ↔ x ∈ as ∧ p x = true
#check List.length_filter_le -- ∀ {α : Type u_1} (p : α → Bool) (l : List α), List.length (List.filter p l) ≤ List.length l

variable {α : Type}[LinearOrder α]

def smaller (pivot : α) (l : List α) : List α :=
  l.filter (fun x => x ≤  pivot)

def larger (pivot : α) (l : List α) : List α :=
  l.filter (fun x => x > pivot)

/--
The `quickSort` function that performs the quicksort algorithm. We do not prove termination for this function.
-/
partial def naiveQuickSort : List α → List α
  | [] => []
  | pivot :: l =>
    (naiveQuickSort (smaller pivot l)) ++ pivot :: (naiveQuickSort (larger pivot l))

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

/--
A term `x ∈ α` is in `l` if and only if it is in the smaller or larger list.
-/
theorem mem_iff_below_or_above_pivot (pivot : α) (l : List α)(x : α) :
    x ∈ l ↔ x ∈ smaller pivot l ∨ x ∈ larger pivot l := by
  apply Iff.intro
  unfold smaller larger
  · intro h
    by_cases h' : x ≤ pivot
    · left
      rw [List.mem_filter]
      simp [h, h']
    · right
      rw [List.mem_filter]
      simp [h, h', lt_of_not_ge h']
  · intro h
    cases h with
    | inl h =>
      unfold smaller at h
      rw [List.mem_filter] at h
      exact h.left
    | inr h =>
      unfold larger at h
      rw[List.mem_filter] at h
      exact h.left

/--
A term `x ∈ α` is in `l` if and only if it is in the sorted list `quickSort l`.
-/
theorem mem_iff_mem_quickSort (l: List α)(x : α) :
    x ∈ l ↔ x ∈ quickSort l := by
  cases l with
  | nil =>
    simp
  | cons pivot l =>
    simp
    rw [mem_iff_below_or_above_pivot pivot]
    have : (smaller pivot l).length < (pivot :: l).length := by
      simp [List.length_cons]
      apply Nat.succ_le_succ
      apply List.length_filter_le
    have : (larger pivot l).length < (pivot :: l).length := by
      simp [List.length_cons]
      apply Nat.succ_le_succ
      apply List.length_filter_le
    have ihb := mem_iff_mem_quickSort (smaller pivot l)
    have iha := mem_iff_mem_quickSort (larger pivot l)
    rw [← ihb, ← iha]
    tauto
termination_by l.length

/--
An inductive definition of a sorted list. A list is sorted if it is empty, has one element, or if the first two elements are in order and the tail is sorted.
-/
inductive Sorted : List α → Prop
  | nil : Sorted []
  | singleton (x : α) : Sorted [x]
  | step (x y : α) (l : List α) (hxy: x ≤ y)
      (tail_sorted: Sorted (y :: l)) : Sorted (x :: y :: l)

/--
If we append two sorted lists, the result is sorted if there is a `bound` such that all elements in the first list are less than or equal to `bound` and all elements in the second list are greater than or equal to `bound`.
This is a helper theorem for the main theorem.
-/
theorem append_sorted (bound: α)(l₁ l₂ : List α) :
  (∀ x ∈ l₁, x ≤ bound) → (∀ x ∈ l₂, bound ≤  x) → Sorted l₁ → Sorted l₂ → Sorted (l₁ ++ l₂) := by
  intro h₁ h₂ s₁
  induction s₁ with
  | nil => simp
  | singleton x =>
    simp at *
    intro s₂
    cases s₂ with
    | nil => apply Sorted.singleton
    | singleton y =>
      apply Sorted.step x y
      · simp at h₂
        trans bound <;> assumption
      · apply Sorted.singleton
    | step y z l hyz s =>
      apply Sorted.step x y
      · trans bound
        · assumption
        · simp [List.mem_cons] at h₂
          exact h₂.left
      · exact Sorted.step y z l hyz s
  | step x y l hxy _ ih =>
    intro s₂
    apply Sorted.step x y (l ++ l₂) hxy
    rw [← List.cons_append]
    apply ih
    · simp [List.mem_cons]
      simp [List.mem_cons] at h₁
      apply And.intro
      · apply h₁.right.left
      · apply h₁.right.right
    · exact s₂

/--
The main theorem that states that the result of `quickSort` is sorted. We prove this by induction on the length of the list.
We use the `append_sorted` theorem to show that the result of `quickSort` is sorted.
-/
theorem quickSort_sorted (l : List α) : Sorted (quickSort l) := by
  cases l with
  | nil =>
    simp [quickSort_nil]
    apply Sorted.nil
  | cons pivot l =>
    rw [quickSort_cons]
    have : (smaller pivot l).length < (pivot :: l).length := by
      simp [List.length_cons]
      apply Nat.succ_le_succ
      apply List.length_filter_le
    have : (larger pivot l).length < (pivot :: l).length := by
      simp [List.length_cons]
      apply Nat.succ_le_succ
      apply List.length_filter_le
    let ihb := quickSort_sorted (smaller pivot l)
    let iha := quickSort_sorted (larger pivot l)
    apply append_sorted pivot
    · intro x
      rw [← mem_iff_mem_quickSort]
      intro h
      unfold smaller at h
      rw[List.mem_filter] at h
      simp at h
      exact h.right
    · simp
      intro x
      rw [← mem_iff_mem_quickSort]
      intro h
      unfold larger at h
      rw [List.mem_filter] at h
      simp at h
      apply le_of_lt
      exact h.right
    · assumption
    · apply append_sorted pivot [pivot] (quickSort (larger pivot l))
      · simp
      · intro x h
        rw [← mem_iff_mem_quickSort] at h
        unfold larger at h
        rw[List.mem_filter] at h
        simp at h
        apply le_of_lt
        exact h.right
      · apply Sorted.singleton
      · assumption
termination_by l.length
