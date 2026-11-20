import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryInverseReduction
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.InvStep.invStepU` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnitaryInverseReduction.lean&line=238#L238)
-/
theorem _root_.GlobalTheory.T.unitary_inverse_reduction : PositivityTheory.SphericalProduct.InvStepU := by
  first | exact @GlobalTheory.CompanionTheory.InvStep.invStepU | exact GlobalTheory.CompanionTheory.InvStep.invStepU | (intros; apply GlobalTheory.CompanionTheory.InvStep.invStepU <;> assumption)
