import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralQExpansionEqLSeries
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FUnitStripIntegralQExpansionEqLSeries.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.unitStrip_integral_qExpansion_eq_LSeries : ∀ (h b : ℕ → ℂ) (w : ℝ), 0 < w → PolyB h → PolyB b → h 0 = 0 → LSeriesSummable (fun n => conj (h n) * b n) w → IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ)) strip → ∫ τ in strip, conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ) = ((Real.Gamma w / (4 * π) ^ w : ℝ) : ℂ) * LSeries (fun n => conj (h n) * b n) w := by
  first | exact @GlobalTheory.EisM.strip_eq_LSeries | exact GlobalTheory.EisM.strip_eq_LSeries | (intros; apply GlobalTheory.EisM.strip_eq_LSeries <;> assumption)
