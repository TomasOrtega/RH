import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FrameTorus.stTor` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FTorusStatement.lean&line=158#L158)
-/
theorem _root_.GlobalTheory.T.TorusStatement : StTor := by
  first | exact @GlobalTheory.CompanionTheory.FrameTorus.stTor | exact GlobalTheory.CompanionTheory.FrameTorus.stTor | (intros; apply GlobalTheory.CompanionTheory.FrameTorus.stTor <;> assumption)
