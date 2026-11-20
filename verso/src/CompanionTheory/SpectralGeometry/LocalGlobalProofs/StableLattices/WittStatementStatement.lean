import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WittStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FWittStatement.lean&line=209#L209)
-/
theorem _root_.GlobalTheory.T.WittStatement : StWitt := by
  first | exact @GlobalTheory.CompanionTheory.FlWitt.stWitt | exact GlobalTheory.CompanionTheory.FlWitt.stWitt | (intros; apply GlobalTheory.CompanionTheory.FlWitt.stWitt <;> assumption)
