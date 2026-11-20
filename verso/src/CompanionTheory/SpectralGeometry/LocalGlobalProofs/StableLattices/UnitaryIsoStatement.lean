import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitaryIso
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ZuckUIso.uIso` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FUnitaryIso.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.UnitaryIso : UIso := by
  first | exact @GlobalTheory.CompanionTheory.ZuckUIso.uIso | exact GlobalTheory.CompanionTheory.ZuckUIso.uIso | (intros; apply GlobalTheory.CompanionTheory.ZuckUIso.uIso <;> assumption)
