import Formalism.PeriodIntegrals.PrimeSums
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MertensLogSum.SLeOfBlock
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MertensLogSum.PrimeLogOverPWork

namespace PI.PrimeLogOverPWork

open Finset in
/- English proof (translation)
Introduce `Y hY Q hQ`. Establish `hN1 : 1 ≤ ⌊Y⌋₊` using `Nat.le_floor (by simpa using hY.le)`. Establish `hNY : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y` using `Nat.floor_le (by linarith)`. Establish `h1 : ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ≤ S ⌊Y⌋₊`. Unfold `S`.

Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `p hp`. Take `⟨hpp, hpY⟩` from `hQ p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_Ioc]`. Conclude with `⟨⟨hpp.pos, Nat.le_floor hpY⟩, hpp⟩`.

Introduce `p _ _`. Conclude with `div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)`. Establish `h2 : S ⌊Y⌋₊ ≤ Real.log ((⌊Y⌋₊ : ℕ) : ℝ)`. Break down `Nat.lt_or_ge 63 ⌊Y⌋₊ with h | h` into its components or cases. Conclude with `S_le_large _ (by omega)`.

Conclude with `S_le_small _ hN1 h`. Establish `h3 : Real.log ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Real.log Y` using `Real.log_le_log (Nat.cast_pos.mpr hN1) hNY`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_log_div_prime_le : PI.PrimeLogOverP := by
  intro Y hY Q hQ
  have hN1 : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by simpa using hY.le)
  have hNY : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have h1 : ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ≤ S ⌊Y⌋₊ := by
    unfold S
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpp, hpY⟩ := hQ p hp
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hpp.pos, Nat.le_floor hpY⟩, hpp⟩
    · intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have h2 : S ⌊Y⌋₊ ≤ Real.log ((⌊Y⌋₊ : ℕ) : ℝ) := by
    rcases Nat.lt_or_ge 63 ⌊Y⌋₊ with h | h
    · exact S_le_large _ (by omega)
    · exact S_le_small _ hN1 h
  have h3 : Real.log ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Real.log Y := Real.log_le_log (Nat.cast_pos.mpr hN1) hNY
  linarith

end PI.PrimeLogOverPWork
