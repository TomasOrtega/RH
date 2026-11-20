import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSqIntegralInnerWeightLe
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.norm_sq_integral_inner_smul_le` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FNormSqIntegralInnerWeightLe.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.norm_sq_integral_inner_weight_le : ∀ (Ω V : Type) [MeasurableSpace Ω] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ν : Measure Ω) (f g : Ω → V) (ph : Ω → ℂ), AEStronglyMeasurable f ν → AEStronglyMeasurable g ν → AEStronglyMeasurable ph ν → ENNReal.ofReal (‖∫ x, ⟪f x, ph x • g x⟫_ℂ ∂ν‖ ^ 2) ≤ (∫⁻ x, ENNReal.ofReal (‖ph x‖ ^ 2 * ‖f x‖ ^ 2) ∂ν) * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂ν := by
  first | exact @GlobalTheory.norm_sq_integral_inner_smul_le | exact GlobalTheory.norm_sq_integral_inner_smul_le | (intros; apply GlobalTheory.norm_sq_integral_inner_smul_le <;> assumption)
