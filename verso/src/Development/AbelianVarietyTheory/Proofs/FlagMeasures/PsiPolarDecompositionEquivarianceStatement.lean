import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiPolarDecompositionEquivariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.psi_polar_decomposition_equivariance : PsiPolar := by
  first | exact @GlobalTheory.Dec.psiPolar | exact GlobalTheory.Dec.psiPolar | (intros; apply GlobalTheory.Dec.psiPolar <;> assumption)
