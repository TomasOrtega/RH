import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviStabilityReal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.levi_stability_real : PositivityTheory.RgBcC.RealD.LevStab := by
  first | exact @GlobalTheory.CompanionTheory.LevBd.levStab | exact GlobalTheory.CompanionTheory.LevBd.levStab | (intros; apply GlobalTheory.CompanionTheory.LevBd.levStab <;> assumption)
