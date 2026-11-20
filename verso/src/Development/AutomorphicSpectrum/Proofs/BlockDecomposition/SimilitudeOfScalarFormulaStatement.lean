import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeOfScalarFormula
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.BaseSimil.simil` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSimilitudeOfScalarFormula.lean&line=104#L104)
-/
theorem _root_.GlobalTheory.T.similitude_of_scalar_formula : Scal → Simil := by
  first | exact @GlobalTheory.CompanionTheory.SW.BaseSimil.simil | exact GlobalTheory.CompanionTheory.SW.BaseSimil.simil | (intros; apply GlobalTheory.CompanionTheory.SW.BaseSimil.simil <;> assumption)
