import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTwistBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.BlockTypes
open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TotalTrace.twBound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLimitTwistBound.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.limit_twist_bound : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.TwBound := by
  first | exact @GlobalTheory.CompanionTheory.TotalTrace.twBound | exact GlobalTheory.CompanionTheory.TotalTrace.twBound | (intros; apply GlobalTheory.CompanionTheory.TotalTrace.twBound <;> assumption)
