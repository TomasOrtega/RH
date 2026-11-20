import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitAlmostEverywhereFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnitAlmostEverywhereFacts.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.unit_almost_everywhere_facts : PositivityTheory.Rg.BcB.G8.Fin.UnitAE := by
  first | exact @GlobalTheory.CompanionTheory.UnitAEPair.main | exact GlobalTheory.CompanionTheory.UnitAEPair.main | (intros; apply GlobalTheory.CompanionTheory.UnitAEPair.main <;> assumption)
