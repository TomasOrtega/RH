import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CountingBound
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FCountingBound.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.CountingBound : Count := by
  first | exact @GlobalTheory.CompanionTheory.ZuckCount.count | exact GlobalTheory.CompanionTheory.ZuckCount.count | (intros; apply GlobalTheory.CompanionTheory.ZuckCount.count <;> assumption)
