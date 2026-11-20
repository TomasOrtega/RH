import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonSplit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.LcSplit.locCompareSplit | exact GlobalTheory.CompanionTheory.LcSplit.locCompareSplit | (intros; apply GlobalTheory.CompanionTheory.LcSplit.locCompareSplit <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.local_comparison_split : PositivityTheory.Rg.BcB.G8.Fin.LocCompareSplit := by
  first | exact @GlobalTheory.CompanionTheory.LcSplit.locCompareSplit | exact GlobalTheory.CompanionTheory.LcSplit.locCompareSplit | (intros; apply GlobalTheory.CompanionTheory.LcSplit.locCompareSplit <;> assumption)
