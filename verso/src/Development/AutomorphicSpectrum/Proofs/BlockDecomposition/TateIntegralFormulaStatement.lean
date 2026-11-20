import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateIntegralFormula
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTateIntegralFormula.lean&line=405#L405)
-/
theorem _root_.GlobalTheory.T.tate_integral_formula : Tate := by
  first | exact @GlobalTheory.CompanionTheory.TateRes.tate | exact GlobalTheory.CompanionTheory.TateRes.tate | (intros; apply GlobalTheory.CompanionTheory.TateRes.tate <;> assumption)
