import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HerbrandQuotientEigenDet
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.herbrandQuotient_eigen_det : GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.HerbrandDet := by
  first | exact @GlobalTheory.HerbrandAlg.herbrandDet | exact GlobalTheory.HerbrandAlg.herbrandDet | (intros; apply GlobalTheory.HerbrandAlg.herbrandDet <;> assumption)
