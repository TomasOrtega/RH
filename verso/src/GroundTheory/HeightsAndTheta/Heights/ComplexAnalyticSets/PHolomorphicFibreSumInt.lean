import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicFibreSumInt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StWeightedAreaFormula
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ReciprocityTheory.AnForm.A

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem abs_det_fderiv_real_mul_eq_normSq {d : ℕ} {Ω : Set (Fin d → ℂ)} {τ : (Fin d → ℂ) → Fin d → ℂ}
    (hΩ : IsOpen Ω) (hτ : DifferentiableOn ℂ τ Ω) (H : (Fin d → ℂ) → ℝ) :
    Set.EqOn (fun t => |(fderiv ℝ τ t).det| * H t) (fun t => Complex.normSq (jacC τ t).det * H t) Ω := by
  intro t ht
  simp only
  rw [det_fderiv_real_eq_normSq τ t (hτ.differentiableAt (hΩ.mem_nhds ht)),
    abs_of_nonneg (Complex.normSq_nonneg _)]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem HolomorphicFibreSumInt.proof (h : WeightedAreaFormula.Statement) :
    HolomorphicFibreSumInt.Statement := by
  intro d Ω τ H hΩ hτ hfin hint
  have heq := abs_det_fderiv_real_mul_eq_normSq hΩ hτ H
  have hint' : IntegrableOn (fun t => |(fderiv ℝ τ t).det| * H t) Ω :=
    (integrableOn_congr_fun heq hΩ.measurableSet).2 hint
  obtain ⟨h1, h2⟩ := h (Fin d → ℂ) volume Ω τ H hΩ (hτ.restrictScalars ℝ) hfin hint'
  exact ⟨h1, h2.trans (setIntegral_congr_fun hΩ.measurableSet heq)⟩

end

end GroundTheory.Heights₂.Heights
