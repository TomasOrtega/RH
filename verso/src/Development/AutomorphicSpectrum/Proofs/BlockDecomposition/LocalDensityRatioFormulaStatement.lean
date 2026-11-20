import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityRatioFormula
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalDensityRatioFormula.lean&line=707#L707)
-/
theorem _root_.GlobalTheory.T.local_density_ratio_formula : Ratio := by
  first | exact @GlobalTheory.CompanionTheory.RatioBase.ratio | exact GlobalTheory.CompanionTheory.RatioBase.ratio | (intros; apply GlobalTheory.CompanionTheory.RatioBase.ratio <;> assumption)
