import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteFourierCoefficients
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FuncCalc.absFC` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAbsoluteFourierCoefficients.lean&line=397#L397)
-/
theorem _root_.GlobalTheory.T.absolute_fourier_coefficients : PositivityTheory.RgBcC.Fc.AbsFC := by
  first | exact @GlobalTheory.CompanionTheory.FuncCalc.absFC | exact GlobalTheory.CompanionTheory.FuncCalc.absFC | (intros; apply GlobalTheory.CompanionTheory.FuncCalc.absFC <;> assumption)
