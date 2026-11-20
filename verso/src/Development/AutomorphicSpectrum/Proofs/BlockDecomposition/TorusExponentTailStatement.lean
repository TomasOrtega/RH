import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusExponentTail
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTorusExponentTail.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.torus_exponent_tail : PositivityTheory.Rg.BcB.F.Tail.PExp.TorusExp := by
  first | exact @GlobalTheory.CompanionTheory.TorusExpU.torusExp | exact GlobalTheory.CompanionTheory.TorusExpU.torusExp | (intros; apply GlobalTheory.CompanionTheory.TorusExpU.torusExp <;> assumption)
