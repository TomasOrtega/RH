import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentToSaturation
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ExpProd.expToSat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExponentToSaturation.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.exponent_to_saturation : PositivityTheory.Rg.BcB.F.Tail.PExp.ExpToSat := by
  first | exact @GlobalTheory.CompanionTheory.ExpProd.expToSat | exact GlobalTheory.CompanionTheory.ExpProd.expToSat | (intros; apply GlobalTheory.CompanionTheory.ExpProd.expToSat <;> assumption)
