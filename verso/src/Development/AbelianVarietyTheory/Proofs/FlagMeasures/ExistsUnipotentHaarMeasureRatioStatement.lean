import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentHaarMeasureRatio
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsUnipotentHaarMeasureRatio.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.exists_unipotentHaarMeasure_ratio : ∀ (k r : ℕ), ∃ cN : ℝ, IsRatioN k r cN := by
  first | exact @GlobalTheory.ThA.exists_isRatioN | exact GlobalTheory.ThA.exists_isRatioN | (intros; apply GlobalTheory.ThA.exists_isRatioN <;> assumption)
