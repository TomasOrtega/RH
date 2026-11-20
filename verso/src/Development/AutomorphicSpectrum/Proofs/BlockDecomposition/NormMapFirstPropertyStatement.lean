import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapFirstProperty
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.NormOnto.norm_onto` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNormMapFirstProperty.lean&line=339#L339)
-/
theorem _root_.GlobalTheory.T.norm_map_first_property : PositivityTheory.Rg.Tf.Loc.N1 := by
  first | exact @GlobalTheory.CompanionTheory.NormOnto.norm_onto | exact GlobalTheory.CompanionTheory.NormOnto.norm_onto | (intros; apply GlobalTheory.CompanionTheory.NormOnto.norm_onto <;> assumption)
