import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateIntegralFormula
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.TateRes.tate | exact GlobalTheory.CompanionTheory.TateRes.tate | (intros; apply GlobalTheory.CompanionTheory.TateRes.tate <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.tate_integral_formula : Tate := by
  first | exact @GlobalTheory.CompanionTheory.TateRes.tate | exact GlobalTheory.CompanionTheory.TateRes.tate | (intros; apply GlobalTheory.CompanionTheory.TateRes.tate <;> assumption)
