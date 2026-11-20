import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecomposition
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FCartanDecomposition.lean&line=340#L340)
-/
theorem _root_.GlobalTheory.T.CartanDecomposition : CartanQ := by
  first | exact @GlobalTheory.CompanionTheory.BesselCartan.cartanQ | exact GlobalTheory.CompanionTheory.BesselCartan.cartanQ | (intros; apply GlobalTheory.CompanionTheory.BesselCartan.cartanQ <;> assumption)
