import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.YHom
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.ExactSecondDegreeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.DivisionPartitionTotal

noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial Finset

def wy (D : ℕ) : Fin D ⊕ Fin D → ℕ := Sum.elim 0 1

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem KK {D : ℕ} (t u : Fin D → P D) (ω : W D) (J : Finset (Fin D)) :
    K t (K u ω) J = ∑ i ∈ Jᶜ, ∑ l ∈ Jᶜ, (if l = i then 0 else
      (sgn i J : P D) * (sgn l (insert i J) : P D) * (t i * u l) * ω (insert l (insert i J))) := by
  simp only [K]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.compl_insert, ← Finset.filter_ne', Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : l = i
  · simp [h]
  · simp only [h, if_false, ne_eq, not_false_eq_true, if_true]
    ring

end PI.EagonNorthcottZ
