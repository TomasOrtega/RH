import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordLengthBoundOfLinear
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FWordLengthBoundOfLinear.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.word_length_bound_of_linear : DsLin → WordBd := by
  first | exact @GlobalTheory.CompanionTheory.BmuWordBd.wordBd_of_dsLin | exact GlobalTheory.CompanionTheory.BmuWordBd.wordBd_of_dsLin | (intros; apply GlobalTheory.CompanionTheory.BmuWordBd.wordBd_of_dsLin <;> assumption)
