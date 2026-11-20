import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DefinitenessStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FDefinitenessStatement.lean&line=204#L204)
-/
theorem _root_.GlobalTheory.T.DefinitenessStatement : StDefinite := by
  first | exact @GlobalTheory.CompanionTheory.DefiniteForm.stDefinite | exact GlobalTheory.CompanionTheory.DefiniteForm.stDefinite | (intros; apply GlobalTheory.CompanionTheory.DefiniteForm.stDefinite <;> assumption)
