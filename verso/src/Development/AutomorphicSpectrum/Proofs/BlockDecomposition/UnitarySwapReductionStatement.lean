import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySwapReduction
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.SwapRoot.swapStepU | exact GlobalTheory.CompanionTheory.SwapRoot.swapStepU | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.swapStepU <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.unitary_swap_reduction : PositivityTheory.SphericalProduct.SwapStepU := by
  first | exact @GlobalTheory.CompanionTheory.SwapRoot.swapStepU | exact GlobalTheory.CompanionTheory.SwapRoot.swapStepU | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.swapStepU <;> assumption)
