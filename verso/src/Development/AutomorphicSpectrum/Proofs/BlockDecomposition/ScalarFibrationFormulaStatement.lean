import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarFibrationFormula
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.scalar_fibration_formula : Scal := by
  first | exact @GlobalTheory.CompanionTheory.RgBase.ScalFib.scal | exact GlobalTheory.CompanionTheory.RgBase.ScalFib.scal | (intros; apply GlobalTheory.CompanionTheory.RgBase.ScalFib.scal <;> assumption)
