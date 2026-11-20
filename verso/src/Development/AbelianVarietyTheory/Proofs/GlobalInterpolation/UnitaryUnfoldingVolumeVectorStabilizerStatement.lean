import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryUnfoldingVolumeVectorStabilizer
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FUnitaryUnfoldingVolumeVectorStabilizer.lean&line=269#L269)
-/
theorem _root_.GlobalTheory.T.unitaryUnfolding_volume_vectorStabilizer : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures → GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar → GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive → ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.Unfolding D := by
  first | exact @GlobalTheory.VolumeUnfolding.unfolding | exact GlobalTheory.VolumeUnfolding.unfolding | (intros; apply GlobalTheory.VolumeUnfolding.unfolding <;> assumption)
