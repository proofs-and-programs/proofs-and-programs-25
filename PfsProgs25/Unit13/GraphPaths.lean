import Mathlib
/-!
A digression to discuss graphs and paths. We will use the `SimpleGraph` library in Lean 4. This was to help with a project.
-/

#check SimpleGraph

#print SimpleGraph

variable {V : Type} [Inhabited V][DecidableEq V]

namespace SimpleGraph

#check Path

def acyclic (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (p : Walk G v v), ¬p.IsCircuit

def connected (G : SimpleGraph V) : Prop :=
  Nonempty <| ∀ (v w : V), Walk G v w

#check SimpleGraph.IsTree.isConnected

end SimpleGraph

def subsetsOfLength {α : Type} : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | _+1, [] => []
  | n+1, x::xs => (subsetsOfLength n xs).map (List.cons x) ++ subsetsOfLength (n+1) xs

theorem subsetsOfLengthSubset {α : Type} (n : ℕ) (xs : List α) : ∀ l, l ∈ subsetsOfLength n xs →  l ⊆ xs :=
  by
    intro l h
    match n, xs with
    | 0, _ => simp [subsetsOfLength] at h
              simp [h]
    | n+1, [] =>
      simp [subsetsOfLength] at h
    | n+1, x::xs =>
      simp [subsetsOfLength] at h
      cases h
      case inl h₁ =>
        let ⟨t, p₁, p₂⟩ := h₁
        rw [← p₂]
        let ih := subsetsOfLengthSubset n xs t p₁
        simp [ih]
      case inr h₂ =>
        let ih := subsetsOfLengthSubset (n+1) xs _ h₂
        simp [ih]

/-
Set.Ioo.{u_1} {α : Type u_1} [Preorder α] (a b : α) : Set α
-/
#check Set.Ioo

def graph₁ : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun x y ↦ !(x.val == y.val))

-- def m₁ := graph₁.adjMatrix

#check DecidableRel
