import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.N2TopReal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ExpansionTerms
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FN2TopReal.lean&line=127#L127)
-/
theorem _root_.GlobalTheory.T.n2_top_real : PositivityTheory.RgBcC.RealD.SecondTypeWeightsShorter := by
  first | exact @GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T | exact GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T | (intros; apply GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T <;> assumption)
