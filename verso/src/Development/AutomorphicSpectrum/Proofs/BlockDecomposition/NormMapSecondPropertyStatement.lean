import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapSecondProperty
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNormMapSecondProperty.lean&line=152#L152)
-/
theorem _root_.GlobalTheory.T.norm_map_second_property : PositivityTheory.Rg.Tf.Loc.N2 := by
  first | exact @GlobalTheory.CompanionTheory.NormLoc.fixedRing_traceOne_firstOrder | exact GlobalTheory.CompanionTheory.NormLoc.fixedRing_traceOne_firstOrder | (intros; apply GlobalTheory.CompanionTheory.NormLoc.fixedRing_traceOne_firstOrder <;> assumption)
