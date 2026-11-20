import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGoodReduction
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LocGoodProof.locGood` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalGoodReduction.lean&line=175#L175)
-/
theorem _root_.GlobalTheory.T.local_good_reduction : PositivityTheory.Rg.BcB.G8.Fin.LocGood := by
  first | exact @GlobalTheory.CompanionTheory.LocGoodProof.locGood | exact GlobalTheory.CompanionTheory.LocGoodProof.locGood | (intros; apply GlobalTheory.CompanionTheory.LocGoodProof.locGood <;> assumption)
