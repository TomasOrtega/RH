import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigenReal
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TensEigSecond.tensEigR` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTensorEigenReal.lean&line=139#L139)
-/
theorem _root_.GlobalTheory.T.tensor_eigen_real : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEigR := by
  first | exact @GlobalTheory.CompanionTheory.TensEigSecond.tensEigR | exact GlobalTheory.CompanionTheory.TensEigSecond.tensEigR | (intros; apply GlobalTheory.CompanionTheory.TensEigSecond.tensEigR <;> assumption)
