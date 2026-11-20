import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfFrameWittTorus
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FDecompositionOfFrameWittTorus.lean&line=347#L347)
-/
theorem _root_.GlobalTheory.T.decomposition_of_frame_witt_torus : StFrame → StWitt → StTor → StDecomp := by
  first | exact @GlobalTheory.CompanionTheory.FlDecomp.stDecomp_of_frame_witt_tor | exact GlobalTheory.CompanionTheory.FlDecomp.stDecomp_of_frame_witt_tor | (intros; apply GlobalTheory.CompanionTheory.FlDecomp.stDecomp_of_frame_witt_tor <;> assumption)
