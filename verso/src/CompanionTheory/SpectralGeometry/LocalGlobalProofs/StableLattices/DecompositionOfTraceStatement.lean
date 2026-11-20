import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTrace
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FDecompositionOfTrace.lean&line=181#L181)
-/
theorem _root_.GlobalTheory.T.DecompositionOfTrace : DecOfTrace := by
  first | exact @GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace | exact GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace | (intros; apply GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace <;> assumption)
