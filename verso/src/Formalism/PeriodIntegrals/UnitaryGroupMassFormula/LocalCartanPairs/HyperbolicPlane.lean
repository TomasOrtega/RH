import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PiNonunit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PairBaseOfLag
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PlaneIsUnitOfSubOneMem

noncomputable section
open Matrix

namespace PI.SqPair.LCP

/- English proof (translation)
Introduce `R _ _ R₀ _ _ ϖ hI κ _ _ hev A hA`. Take `⟨θ, hθ⟩` from `hI.unr`. Conclude with `PI.LocCartanPair.lag_exists hI.fix hθ hev A hA.1 hA.2`.
-/
theorem base_lagrangian : BaseLag := by
  intro R _ _ R₀ _ _ ϖ hI κ _ _ hev A hA
  obtain ⟨θ, hθ⟩ := hI.unr
  exact PI.LocCartanPair.lag_exists hI.fix hθ hev A hA.1 hA.2

/- English proof (translation)
Introduce `R _ _ R₀ _ ϖ hI α β hα`. Take `⟨θ, hθ⟩` from `hI.unr`. Establish `hσ : ∀ x : R, (starRingAut : R ≃+* R) ((starRingAut : R ≃+* R) x) = x` using `fun x => by`. Simplify using `[starRingAut_apply]`. Establish `hR₀ : ∀ x, x ∈ R₀ ↔ (starRingAut : R ≃+* R) x = x` using `fun x => by`.

Rewrite using `[starRingAut_apply]`. Conclude with `hI.fix x`. Establish `hθ' : IsUnit (θ - (starRingAut : R ≃+* R) θ)`. Rewrite using `[starRingAut_apply]`. Conclude with `hθ`.

Take `⟨τ, hτ⟩` from `tau_of_theta (starRingAut : R ≃+* R) hσ θ hθ'`. Take `⟨w, hw1, hw2, hw3⟩` from `plane_w (starRingAut : R ≃+* R) hσ R₀ hR₀ τ hτ α β hα`. Use `⟨w, hw1, ?_, hw3⟩` and prove the remaining obligations. Establish `hct : wᴴ = (w.map (starRingAut : R ≃+* R))ᵀ`. Use extensionality with `i j`.

Simplify using `[Matrix.conjTranspose_apply, starRingAut_apply]`. Rewrite using `[hct, hw2]`. Both sides reduce to the same expression.
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
