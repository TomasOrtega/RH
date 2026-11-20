import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SeparatedMovingStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgFl.stSepMove` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FSeparatedMovingStatement.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.SeparatedMovingStatement : StSepMove := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stSepMove | exact GlobalTheory.CompanionTheory.RgFl.stSepMove | (intros; apply GlobalTheory.CompanionTheory.RgFl.stSepMove <;> assumption)
