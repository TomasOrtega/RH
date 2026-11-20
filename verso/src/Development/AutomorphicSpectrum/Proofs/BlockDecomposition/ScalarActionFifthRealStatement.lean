import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarActionFifthReal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.CapScal.capScal | exact GlobalTheory.CompanionTheory.CapScal.capScal | (intros; apply GlobalTheory.CompanionTheory.CapScal.capScal <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.scalar_action_fifth_real : PositivityTheory.RgBcC.RealD.CapelliProductsScalar := by
  first | exact @GlobalTheory.CompanionTheory.CapScal.capScal | exact GlobalTheory.CompanionTheory.CapScal.capScal | (intros; apply GlobalTheory.CompanionTheory.CapScal.capScal <;> assumption)
