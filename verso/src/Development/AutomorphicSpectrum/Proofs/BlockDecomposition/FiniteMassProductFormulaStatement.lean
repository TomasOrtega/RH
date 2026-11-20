import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteMassProductFormula
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteMassProductFormula.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.finite_mass_product_formula : PositivityTheory.Rg.BcB.G8.Fin.MassProd := by
  first | exact @GlobalTheory.CompanionTheory.MassProd.massProd | exact GlobalTheory.CompanionTheory.MassProd.massProd | (intros; apply GlobalTheory.CompanionTheory.MassProd.massProd <;> assumption)
