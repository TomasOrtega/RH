import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteConjugacyExists
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteConjugacyExists.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.finite_conjugacy_exists : PositivityTheory.Rg.BcB.G8.Fin.CjEx := by
  first | exact @GlobalTheory.CompanionTheory.CjEx.cjEx | exact GlobalTheory.CompanionTheory.CjEx.cjEx | (intros; apply GlobalTheory.CompanionTheory.CjEx.cjEx <;> assumption)
