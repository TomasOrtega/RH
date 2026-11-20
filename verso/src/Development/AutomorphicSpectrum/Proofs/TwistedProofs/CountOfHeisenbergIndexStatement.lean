import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CountOfHeisenbergIndex
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FCountOfHeisenbergIndex.lean&line=149#L149)
-/
theorem _root_.GlobalTheory.T.count_of_heisenberg_index : Heis → LatIndex → TraceIndex → Count := by
  first | exact @GlobalTheory.CompanionTheory.InertCount.count | exact GlobalTheory.CompanionTheory.InertCount.count | (intros; apply GlobalTheory.CompanionTheory.InertCount.count <;> assumption)
