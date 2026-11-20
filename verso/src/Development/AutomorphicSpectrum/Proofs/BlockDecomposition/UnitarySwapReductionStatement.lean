import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySwapReduction
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnitarySwapReduction.lean&line=136#L136)
-/
theorem _root_.GlobalTheory.T.unitary_swap_reduction : PositivityTheory.SphericalProduct.SwapStepU := by
  first | exact @GlobalTheory.CompanionTheory.SwapRoot.swapStepU | exact GlobalTheory.CompanionTheory.SwapRoot.swapStepU | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.swapStepU <;> assumption)
