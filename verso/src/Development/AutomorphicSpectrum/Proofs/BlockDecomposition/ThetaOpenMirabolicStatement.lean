import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolic
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.BZFun.thetaOpen | exact GlobalTheory.CompanionTheory.BZFun.thetaOpen | (intros; apply GlobalTheory.CompanionTheory.BZFun.thetaOpen <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.theta_open_mirabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.ThetaOpen k := by
  first | exact @GlobalTheory.CompanionTheory.BZFun.thetaOpen | exact GlobalTheory.CompanionTheory.BZFun.thetaOpen | (intros; apply GlobalTheory.CompanionTheory.BZFun.thetaOpen <;> assumption)
