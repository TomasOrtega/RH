import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.LatticeIndexOfSmith
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.InertIndex.latIndex` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FLatticeIndexOfSmith.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.lattice_index_of_smith : Smith → LatIndex := by
  first | exact @GlobalTheory.CompanionTheory.InertIndex.latIndex | exact GlobalTheory.CompanionTheory.InertIndex.latIndex | (intros; apply GlobalTheory.CompanionTheory.InertIndex.latIndex <;> assumption)
