import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProductChartTangentEquivBallVolume
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlkExt
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsProductChartTangentEquivBallVolume.lean&line=177#L177)
-/
theorem _root_.GlobalTheory.T.exists_productChart_tangentEquiv_ballVolume : ∀ (k : ℕ) (η : ℝ), 1 ≤ k → (η = 1 ∨ η = -1) → ∃ L : Par k ≃L[ℝ] lieE (UH (Hd k η)), (∀ v : Par k, unrealify ((L v : lieE (UH (Hd k η))) : EuclideanSpace ℝ _) = tang η v) ∧ ∀ ρ : ℝ, 0 < ρ → volume (L '' Metric.ball (0 : Par k) ρ) = volume (Metric.ball (0 : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ))) ρ) * ENNReal.ofReal (2 * ρ * (Real.pi ^ k * ρ ^ (2 * k) / (k.factorial : ℝ))) := by
  first | exact @GlobalTheory.TubeLie.exists_tang_equiv | exact GlobalTheory.TubeLie.exists_tang_equiv | (intros; apply GlobalTheory.TubeLie.exists_tang_equiv <;> assumption)
