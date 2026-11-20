import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FIwahoriStatement.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.IwahoriStatement : StIwahori := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.stIwahori | exact GlobalTheory.CompanionTheory.Iwahori.stIwahori | (intros; apply GlobalTheory.CompanionTheory.Iwahori.stIwahori <;> assumption)
