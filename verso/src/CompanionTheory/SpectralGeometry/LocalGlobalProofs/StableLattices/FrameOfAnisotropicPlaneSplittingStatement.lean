import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FrameOfAnisotropicPlaneSplitting
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.HermFrame.stFrame_of` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FFrameOfAnisotropicPlaneSplitting.lean&line=207#L207)
-/
theorem _root_.GlobalTheory.T.frame_of_anisotropic_plane_splitting : StAniso → StPlane → StSplit → StFrame := by
  first | exact @GlobalTheory.CompanionTheory.HermFrame.stFrame_of | exact GlobalTheory.CompanionTheory.HermFrame.stFrame_of | (intros; apply GlobalTheory.CompanionTheory.HermFrame.stFrame_of <;> assumption)
