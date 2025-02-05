namespace Cantor

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

theorem unwrapping :
  flip' (TisT' ▸ (T.node flip')) = (flip (T.node flip')) := by
  congr
  simp [flip']
  sorry

end Cantor
