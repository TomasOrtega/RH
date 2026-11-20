import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiscriminantIdentity
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.FinDiscP.main | exact GlobalTheory.CompanionTheory.FinDiscP.main | (intros; apply GlobalTheory.CompanionTheory.FinDiscP.main <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.finite_discriminant_identity : PositivityTheory.Rg.BcB.SpectralAccumulation.FinDisc := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscP.main | exact GlobalTheory.CompanionTheory.FinDiscP.main | (intros; apply GlobalTheory.CompanionTheory.FinDiscP.main <;> assumption)
