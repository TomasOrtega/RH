import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHyperplaneVolumeRatioSiegelWeil
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FUnitaryHyperplaneVolumeRatioSiegelWeil.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.unitary_hyperplane_volumeRatio_siegelWeil : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.RT.MassRatioUnderVolume D := by
  first | exact @GlobalTheory.VolRatioFromSiegelWeil.volumeRatio | exact GlobalTheory.VolRatioFromSiegelWeil.volumeRatio | (intros; apply GlobalTheory.VolRatioFromSiegelWeil.volumeRatio <;> assumption)
