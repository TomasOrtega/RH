import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.N2TopReal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ExpansionTerms
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T | exact GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T | (intros; apply GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.n2_top_real : PositivityTheory.RgBcC.RealD.SecondTypeWeightsShorter := by
  first | exact @GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T | exact GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T | (intros; apply GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T <;> assumption)
