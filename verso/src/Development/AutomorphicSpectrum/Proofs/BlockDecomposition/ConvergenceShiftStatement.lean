import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceShift
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.convergence_shift : GlobalTheory.CompanionTheory.EGlue.ConvShift := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.convShift_holds | exact GlobalTheory.CompanionTheory.EGlue.convShift_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.convShift_holds <;> assumption)
