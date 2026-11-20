import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsomorphismStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FIsomorphismStatement.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.IsomorphismStatement : StIso := by
  first | exact @GlobalTheory.CompanionTheory.FactorIso.stIso | exact GlobalTheory.CompanionTheory.FactorIso.stIso | (intros; apply GlobalTheory.CompanionTheory.FactorIso.stIso <;> assumption)
