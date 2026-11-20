import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PiNonunit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PairBaseOfLag
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PlaneIsUnitOfSubOneMem

noncomputable section
open Matrix

namespace PI.SqPair.LCP

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem base_lagrangian : BaseLag := by
  intro R _ _ R₀ _ _ ϖ hI κ _ _ hev A hA
  obtain ⟨θ, hθ⟩ := hI.unr
  exact PI.LocCartanPair.lag_exists hI.fix hθ hev A hA.1 hA.2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem hyperbolic_plane : Plane := by
  intro R _ _ R₀ _ ϖ hI α β hα
  obtain ⟨θ, hθ⟩ := hI.unr
  have hσ : ∀ x : R, (starRingAut : R ≃+* R) ((starRingAut : R ≃+* R) x) = x := fun x => by
    simp [starRingAut_apply]
  have hR₀ : ∀ x, x ∈ R₀ ↔ (starRingAut : R ≃+* R) x = x := fun x => by
    rw [starRingAut_apply]
    exact hI.fix x
  have hθ' : IsUnit (θ - (starRingAut : R ≃+* R) θ) := by
    rw [starRingAut_apply]
    exact hθ
  obtain ⟨τ, hτ⟩ := tau_of_theta (starRingAut : R ≃+* R) hσ θ hθ'
  obtain ⟨w, hw1, hw2, hw3⟩ := plane_w (starRingAut : R ≃+* R) hσ R₀ hR₀ τ hτ α β hα
  refine ⟨w, hw1, ?_, hw3⟩
  have hct : wᴴ = (w.map (starRingAut : R ≃+* R))ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply, starRingAut_apply]
  rw [hct, hw2]
  rfl

end PI.SqPair.LCP
