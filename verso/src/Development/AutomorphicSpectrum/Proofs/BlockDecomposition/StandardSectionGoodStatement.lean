import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionGood
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.StdGoodAd.stdGood` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FStandardSectionGood.lean&line=241#L241)
-/
theorem _root_.GlobalTheory.T.standard_section_good : PositivityTheory.RgEis.StdGood := by
  first | exact @GlobalTheory.CompanionTheory.StdGoodAd.stdGood | exact GlobalTheory.CompanionTheory.StdGoodAd.stdGood | (intros; apply GlobalTheory.CompanionTheory.StdGoodAd.stdGood <;> assumption)
