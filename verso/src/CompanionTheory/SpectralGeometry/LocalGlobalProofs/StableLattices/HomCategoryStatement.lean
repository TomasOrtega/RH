import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HomCategory
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FHomCategory.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.HomCategory : HomCat := by
  first | exact @GlobalTheory.CompanionTheory.ZuckHomCat.homCat | exact GlobalTheory.CompanionTheory.ZuckHomCat.homCat | (intros; apply GlobalTheory.CompanionTheory.ZuckHomCat.homCat <;> assumption)
