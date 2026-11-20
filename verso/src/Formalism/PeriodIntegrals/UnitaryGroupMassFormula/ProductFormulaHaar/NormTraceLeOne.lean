import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ResCharIff

noncomputable section

namespace PI.ProdFormulaE.TrIntP

/- English proof (translation)
Establish `ht' : IsIntegral ℤ_[ℓ] t` using `ht.tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 ht'`. Rewrite using `[← hy]`. Conclude with `y.norm_le_one`.
-/
theorem norm_le_one_of_isIntegral {ℓ : ℕ} [Fact ℓ.Prime] {t : ℚ_[ℓ]} (ht : IsIntegral ℤ t) :
    ‖t‖ ≤ 1 := by
  have ht' : IsIntegral ℤ_[ℓ] t := ht.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 ht'
  rw [← hy]
  exact y.norm_le_one

/- English proof (translation)
Introduce `ℓ _ K _ _ _ w hw`. Conclude with `norm_le_one_of_isIntegral (Algebra.isIntegral_trace hw)`.
-/
theorem norm_trace_le_one : St.TrInt := by
  intro ℓ _ K _ _ _ w hw
  exact norm_le_one_of_isIntegral (Algebra.isIntegral_trace hw)

end PI.ProdFormulaE.TrIntP
