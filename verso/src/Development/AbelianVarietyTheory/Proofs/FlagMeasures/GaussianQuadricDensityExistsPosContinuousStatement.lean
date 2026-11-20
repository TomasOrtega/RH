import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuous
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GaussMean.Density.gaussDens_spec` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FGaussianQuadricDensityExistsPosContinuous.lean&line=207#L207)
-/
theorem _root_.GlobalTheory.T.gaussianQuadricDensity_exists_pos_continuous : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ β : ℝ, β ≠ 0 → HasDerivAt (fun t : ℝ => ∫ y in {y : Fin n → ℂ | qEps ε y ≤ t}, gauss y) (gaussDens ε β) β ∧ 0 ≤ gaussDens ε β) ∧ ContinuousOn (gaussDens ε) {β | β ≠ 0} ∧ ∀ s : Bool, (∃ a, ε a = s) → 0 < gaussDens ε (sgn ℝ s) := by
  first | exact @GlobalTheory.GaussMean.Density.gaussDens_spec | exact GlobalTheory.GaussMean.Density.gaussDens_spec | (intros; apply GlobalTheory.GaussMean.Density.gaussDens_spec <;> assumption)
