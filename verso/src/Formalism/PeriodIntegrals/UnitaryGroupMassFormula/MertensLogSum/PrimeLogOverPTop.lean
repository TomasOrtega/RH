import Formalism.PeriodIntegrals.PrimeSums
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MertensLogSum.SLeOfBlock
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MertensLogSum.PrimeLogOverPWork

namespace PI.PrimeLogOverPWork

open Finset in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

A detailed English derivation is pending.
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
