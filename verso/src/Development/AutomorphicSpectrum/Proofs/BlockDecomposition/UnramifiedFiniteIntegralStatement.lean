import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFiniteIntegral
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Gunr.finInt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnramifiedFiniteIntegral.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.unramified_finite_integral : PositivityTheory.SiegelWeilFormula.Gunr.FinInt := by
  first | exact @GlobalTheory.CompanionTheory.Gunr.finInt | exact GlobalTheory.CompanionTheory.Gunr.finInt | (intros; apply GlobalTheory.CompanionTheory.Gunr.finInt <;> assumption)
