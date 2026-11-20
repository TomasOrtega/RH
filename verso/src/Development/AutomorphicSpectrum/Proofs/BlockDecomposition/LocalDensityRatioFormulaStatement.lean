import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityRatioFormula
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RatioBase.ratio | exact GlobalTheory.CompanionTheory.RatioBase.ratio | (intros; apply GlobalTheory.CompanionTheory.RatioBase.ratio <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.local_density_ratio_formula : Ratio := by
  first | exact @GlobalTheory.CompanionTheory.RatioBase.ratio | exact GlobalTheory.CompanionTheory.RatioBase.ratio | (intros; apply GlobalTheory.CompanionTheory.RatioBase.ratio <;> assumption)
