import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviDecomposition
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BesselLevi.leviQ` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FLeviDecomposition.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.LeviDecomposition : LeviQ := by
  first | exact @GlobalTheory.CompanionTheory.BesselLevi.leviQ | exact GlobalTheory.CompanionTheory.BesselLevi.leviQ | (intros; apply GlobalTheory.CompanionTheory.BesselLevi.leviQ <;> assumption)
