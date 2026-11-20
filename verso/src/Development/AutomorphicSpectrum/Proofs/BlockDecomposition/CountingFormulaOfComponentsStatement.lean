import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormulaOfComponents
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RgBaseCnt.cnt_of | exact GlobalTheory.CompanionTheory.RgBaseCnt.cnt_of | (intros; apply GlobalTheory.CompanionTheory.RgBaseCnt.cnt_of <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.counting_formula_of_components : Tate → PsiSide → Ratio → HEx → TestEx → Dens → LSide → ThetaId → Cnt := by
  first | exact @GlobalTheory.CompanionTheory.RgBaseCnt.cnt_of | exact GlobalTheory.CompanionTheory.RgBaseCnt.cnt_of | (intros; apply GlobalTheory.CompanionTheory.RgBaseCnt.cnt_of <;> assumption)
