import Mathlib

variable {V : Type u} [LinearOrder V]

def Finset.toOrderedList (s : Finset V) : List V :=
  if p:s.Nonempty then
    let head := s.min' p
    let tail := s.erase head
    have : tail.card < s.card := by
      apply Finset.card_erase_lt_of_mem
      apply Finset.min'_mem
    head :: Finset.toOrderedList tail
  else []
termination_by s.card
