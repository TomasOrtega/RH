import Mathlib
import Formalism.PieriBlockIdeals.ParamsWindow

open Finset

namespace Formalism.CohomologicalDescent

/- English proof (translation)
Unfold `Formalism.RankGapBounds.JumpSetsAlt.maxVal`. Apply `le_antisymm _ (Nat.zero_le _)` to reduce the goal to its premises. Apply `Finset.sup_le` to reduce the goal to its premises. Introduce `i hi`. Establish `hi' : i ≤ n` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`.

Distinguish the cases in `hp : l.Prime`. Apply `le_of_eq` to reduce the goal to its premises. Apply `Nat.factorization_eq_zero_of_not_dvd` to reduce the goal to its premises. Introduce `hd`. Establish `hdf : l ∣ n.factorial` using `hd.trans ⟨i.factorial * (n - i).factorial, by`.

Rewrite using `[← Nat.choose_mul_factorial_mul_factorial hi']`. Use the proof step `ring⟩`. Use `(Nat.Prime.dvd_factorial hp).mp hdf` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `(Nat.factorization_eq_zero_of_not_prime _ hp).le`.
-/
theorem max_val_eq_zero_of_lt (l n : ℕ) (h : n < l) : Formalism.RankGapBounds.JumpSetsAlt.maxVal l n = 0 := by
  unfold Formalism.RankGapBounds.JumpSetsAlt.maxVal
  apply le_antisymm _ (Nat.zero_le _)
  apply Finset.sup_le
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hp : l.Prime
  · apply le_of_eq
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    have hdf : l ∣ n.factorial := hd.trans ⟨i.factorial * (n - i).factorial, by
      rw [← Nat.choose_mul_factorial_mul_factorial hi']; ring⟩
    have := (Nat.Prime.dvd_factorial hp).mp hdf
    omega
  · exact (Nat.factorization_eq_zero_of_not_prime _ hp).le

end Formalism.CohomologicalDescent
