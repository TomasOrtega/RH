import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorBound
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BmuTorBound.torBound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FTorBound.lean&line=104#L104)
-/
theorem _root_.GlobalTheory.T.torBound' : TorBound := by
  first | exact @GlobalTheory.CompanionTheory.BmuTorBound.torBound | exact GlobalTheory.CompanionTheory.BmuTorBound.torBound | (intros; apply GlobalTheory.CompanionTheory.BmuTorBound.torBound <;> assumption)
