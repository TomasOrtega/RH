import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialRightPreservesL2Norm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DblEval.L2RightPartial.partR_lintegral_sq_eq_const_mul_of_mem_schA` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPartialRightPreservesL2Norm.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.partial_right_preserves_l2_norm : ∀ {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)),
    (∀ μ : @Measure (κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ φ ∈ schA F κ', ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ Φ ∈ schA F (κ ⊕ κ'), partR T Φ ∈ schA F (κ ⊕ κ')) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partR T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.DblEval.L2RightPartial.partR_lintegral_sq_eq_const_mul_of_mem_schA | exact GlobalTheory.DblEval.L2RightPartial.partR_lintegral_sq_eq_const_mul_of_mem_schA | (intros; apply GlobalTheory.DblEval.L2RightPartial.partR_lintegral_sq_eq_const_mul_of_mem_schA <;> assumption)
