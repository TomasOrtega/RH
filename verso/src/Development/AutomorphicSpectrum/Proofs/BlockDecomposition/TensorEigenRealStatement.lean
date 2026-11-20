import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigenReal
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.TensEigSecond.tensEigR | exact GlobalTheory.CompanionTheory.TensEigSecond.tensEigR | (intros; apply GlobalTheory.CompanionTheory.TensEigSecond.tensEigR <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.tensor_eigen_real : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEigR := by
  first | exact @GlobalTheory.CompanionTheory.TensEigSecond.tensEigR | exact GlobalTheory.CompanionTheory.TensEigSecond.tensEigR | (intros; apply GlobalTheory.CompanionTheory.TensEigSecond.tensEigR <;> assumption)
