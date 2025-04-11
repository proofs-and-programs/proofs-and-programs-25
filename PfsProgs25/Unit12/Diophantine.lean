import Mathlib

/-!
# Diophantine equations

We consider the simple diophantine equation `a * x + b * y = c` where `a`, `b`, and `c` are integers. Our goal is to either find integer solutions `x` and `y` or prove that there are no integer solutions.
-/

/-
Int.gcd_eq_gcd_ab (x y : ℤ) : ↑(x.gcd y) = x * x.gcdA y + y * x.gcdB y
-/
#check Int.gcd_eq_gcd_ab
/-
Int.gcd_dvd_left {a b : ℤ} : ↑(a.gcd b) ∣ a
-/
#check Int.gcd_dvd_left
/-
Int.gcd_dvd_iff {a b : ℤ} {n : ℕ} : a.gcd b ∣ n ↔ ∃ x y, ↑n = a * x + b * y
-/
#check Int.gcd_dvd_iff

namespace Diophantine

inductive Solution (a b c : ℤ) where
| solution (x y : ℤ) (h : a * x + b * y = c) : Solution a b c
| noSolution (h : ∀ x y : ℤ, a * x + b * y ≠ c) : Solution a b c
deriving Repr

/-!
The terms `gcdA x y` and `gcdB x y` are the coefficients in the Bézout identity `x * x.gcdA y + y * x.gcdB y = x.gcd y`.

If `c = gcd a b`, then the Bézout identity gives us a solution to the diophantine equation `a * x + b * y = c`.
In general, we take the Bézout identity and multiply both sides by `c / gcd a b`. So `x = x.gcd y * c / gcd a b` and `y = y.gcd y * c / gcd a b` are solutions to the diophantine equation `a * x + b * y = c`.
-/

def solve (a b c: ℤ) : Solution a b c := by
  if h:(gcd a b) ∣ c then
    let d := gcd a b
    if hd : d = 0 then
      have h : d ∣  c := h
      rw [hd] at h
      have h' : c = 0 := by
        rw [← zero_dvd_iff]
        assumption
      apply Solution.solution 0 0
      simp [h']
    else
      have c_exp : c = (c / d) * d := by
        exact Eq.symm (Int.ediv_mul_cancel h)
      let x := Int.gcdA a b * (c /d)
      let y := Int.gcdB a b * (c /d)
      apply Solution.solution x y
      unfold x y
      have bezout := Int.gcd_eq_gcd_ab a b
      rw [c_exp]
      rw [← mul_assoc, ← mul_assoc, ← add_mul, ← bezout]
      simp [hd]
      rw [mul_comm]
      rfl
  else
    apply Solution.noSolution
    intro x y
    intro hyp
    have ha : gcd a b ∣ a := Int.gcd_dvd_left
    have hb : gcd a b ∣ b := Int.gcd_dvd_right
    have hax : gcd a b ∣ a * x := by
      apply dvd_mul_of_dvd_left
      assumption
    have hby : gcd a b ∣ b * y := by
      apply dvd_mul_of_dvd_left
      assumption
    apply h
    rw [← hyp]
    apply dvd_add <;> assumption

#check mul_right_cancel

end Diophantine

#check zero_dvd_iff

#check dvd_add

/-
Diophantine.Solution.solution (-3) 1 _
-/
#eval Diophantine.solve 20 70 10

/-
Diophantine.Solution.noSolution _
-/
#eval Diophantine.solve 20 70 11
