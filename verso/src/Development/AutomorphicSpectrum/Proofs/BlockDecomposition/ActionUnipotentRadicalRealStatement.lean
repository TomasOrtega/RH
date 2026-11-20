import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionUnipotentRadicalReal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PairBridge.actUU` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FActionUnipotentRadicalReal.lean&line=546#L546)
-/
theorem _root_.GlobalTheory.T.action_unipotent_radical_real : PositivityTheory.RgBcC.RealD.ActUU := by
  first | exact @GlobalTheory.CompanionTheory.PairBridge.actUU | exact GlobalTheory.CompanionTheory.PairBridge.actUU | (intros; apply GlobalTheory.CompanionTheory.PairBridge.actUU <;> assumption)
