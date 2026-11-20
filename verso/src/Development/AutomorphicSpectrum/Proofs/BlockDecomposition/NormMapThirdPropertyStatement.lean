import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapThirdProperty
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNormMapThirdProperty.lean&line=153#L153)
-/
theorem _root_.GlobalTheory.T.norm_map_third_property : PositivityTheory.Rg.Tf.Loc.N1 → PositivityTheory.Rg.Tf.Loc.N2 → PositivityTheory.Rg.Tf.Loc.N3 := by
  first | exact @GlobalTheory.CompanionTheory.UnitNorm.norm_units_surjective | exact GlobalTheory.CompanionTheory.UnitNorm.norm_units_surjective | (intros; apply GlobalTheory.CompanionTheory.UnitNorm.norm_units_surjective <;> assumption)
