import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory.RealWeil

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem continuous_matrixCoeff_rhoFun : ∀ (n : ℕ) (g g' : Sch (Fin n)),
    Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) := by
  intro n g g'
  have hp : Continuous (fun w : Fin n ⊕ Fin n → ℝ => pPart w) := by
    unfold pPart; fun_prop
  have hq : Continuous (fun w : Fin n ⊕ Fin n → ℝ => qPart w) := by
    unfold qPart; fun_prop
  refine continuous_of_dominated (bound := fun x => SchwartzMap.seminorm ℂ 0 0 g * ‖g' x‖) ?_ ?_ ?_ ?_
  · intro w
    exact (((continuous_phase w).mul (g.continuous.comp (continuous_id.add continuous_const))).mul
      (continuous_star.comp g'.continuous)).aestronglyMeasurable
  · intro w
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [rhoFun, norm_mul, norm_phase, one_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℂ g _) (norm_nonneg _)
  · exact (SchwartzMap.integrable g').norm.const_mul _
  · refine Filter.Eventually.of_forall fun x => ?_
    simp only [rhoFun, phase]
    fun_prop

end GlobalTheory.RealWeil
