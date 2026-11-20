import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHypothesesHold
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LocHypProof.locHyp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalHypothesesHold.lean&line=271#L271)
-/
theorem _root_.GlobalTheory.T.local_hypotheses_hold : PositivityTheory.Rg.BcB.G8.Fin.LocHyp := by
  first | exact @GlobalTheory.CompanionTheory.LocHypProof.locHyp | exact GlobalTheory.CompanionTheory.LocHypProof.locHyp | (intros; apply GlobalTheory.CompanionTheory.LocHypProof.locHyp <;> assumption)
