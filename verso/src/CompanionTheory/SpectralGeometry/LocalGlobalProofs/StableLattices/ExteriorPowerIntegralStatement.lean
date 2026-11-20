import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorPowerIntegral
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FExteriorPowerIntegral.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.ExteriorPowerIntegral : OKWedge := by
  first | exact @GlobalTheory.CompanionTheory.ZuckWedge.okWedge | exact GlobalTheory.CompanionTheory.ZuckWedge.okWedge | (intros; apply GlobalTheory.CompanionTheory.ZuckWedge.okWedge <;> assumption)
