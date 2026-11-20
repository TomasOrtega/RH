import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfIwasawaLeviCartan
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BmuDecomp.decomp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FDecompositionOfIwasawaLeviCartan.lean&line=227#L227)
-/
theorem _root_.GlobalTheory.T.decomposition_of_iwasawa_levi_cartan : AdaptExists → IwaQ → LeviQ → CartanQ → Decomp := by
  first | exact @GlobalTheory.CompanionTheory.BmuDecomp.decomp | exact GlobalTheory.CompanionTheory.BmuDecomp.decomp | (intros; apply GlobalTheory.CompanionTheory.BmuDecomp.decomp <;> assumption)
