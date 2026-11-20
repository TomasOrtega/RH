import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigen
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TensContr.tensEig` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTensorEigen.lean&line=195#L195)
-/
theorem _root_.GlobalTheory.T.tensor_eigen : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEig := by
  first | exact @GlobalTheory.CompanionTheory.TensContr.tensEig | exact GlobalTheory.CompanionTheory.TensContr.tensEig | (intros; apply GlobalTheory.CompanionTheory.TensContr.tensEig <;> assumption)
