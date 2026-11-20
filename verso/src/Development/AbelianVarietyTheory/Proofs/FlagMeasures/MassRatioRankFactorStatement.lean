import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioRankFactor
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMassRatioRankFactor.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.mass_ratio_rank_factor : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ), 1 ≤ M → Formalism.HermitianLatticesTheory.massRatioRightSide E M * volU M ^ Formalism.HermitianLatticesTheory.fDeg E = rankFac E M * volU (M - 1) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  first | exact @GlobalTheory.FlagMeas.mass_ratio_mul_unitary_volume | exact GlobalTheory.FlagMeas.mass_ratio_mul_unitary_volume | (intros; apply GlobalTheory.FlagMeas.mass_ratio_mul_unitary_volume <;> assumption)
