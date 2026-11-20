import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeThirdProperty
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TwistedCent.h3` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHeckeThirdProperty.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.hecke_third_property : PositivityTheory.Rg.Tf.Loc.H3 := by
  first | exact @GlobalTheory.CompanionTheory.TwistedCent.h3 | exact GlobalTheory.CompanionTheory.TwistedCent.h3 | (intros; apply GlobalTheory.CompanionTheory.TwistedCent.h3 <;> assumption)
