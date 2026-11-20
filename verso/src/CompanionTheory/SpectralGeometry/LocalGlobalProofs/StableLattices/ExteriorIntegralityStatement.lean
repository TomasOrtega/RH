import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorIntegrality
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FExteriorIntegrality.lean&line=176#L176)
-/
theorem _root_.GlobalTheory.T.ExteriorIntegrality : WedgeInt := by
  first | exact @GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt | exact GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt | (intros; apply GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt <;> assumption)
