import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivationLimit
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FTruncatedDerivationLimit.lean&line=128#L128)
-/
theorem _root_.GlobalTheory.T.truncated_derivation_limit : Factor → CutDer → CutLim := by
  first | exact @GlobalTheory.CompanionTheory.BesselCutLim.cutLim_of | exact GlobalTheory.CompanionTheory.BesselCutLim.cutLim_of | (intros; apply GlobalTheory.CompanionTheory.BesselCutLim.cutLim_of <;> assumption)
