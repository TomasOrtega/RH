import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreVolumeNormalFormStabiliser
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Amp.FibreVolume.fibre_volume` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FFibreVolumeNormalFormStabiliser.lean&line=79#L79)
-/
theorem _root_.GlobalTheory.T.fibreVolume_normalFormStabiliser : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (De s : ℝ) (μR : Measure (Mt k r)), 1 ≤ j → j + 2 ≤ k → DeOK k r z z' γ De → 0 < s → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → ∀ g₁ ∈ GG k r, lebN k r {n | Yj k r hj z z' γ (Matrix.of n * g₁) = 0} = 0 ∧ ∀ φ, SubCut (GG k r) μR φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ (rmulM g₁ n) * (Eset0 k r hj z z' γ R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol0 k r j R₀ De y / s) := by
  first | exact @GlobalTheory.Amp.FibreVolume.fibre_volume | exact GlobalTheory.Amp.FibreVolume.fibre_volume | (intros; apply GlobalTheory.Amp.FibreVolume.fibre_volume <;> assumption)
