import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ArchimedeanPrincipalSeries
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FArchimedeanPrincipalSeries.lean&line=302#L302)
-/
theorem _root_.GlobalTheory.T.ArchimedeanPrincipalSeries : StArchPI := by
  first | exact @GlobalTheory.CompanionTheory.ArchPI.archPI | exact GlobalTheory.CompanionTheory.ArchPI.archPI | (intros; apply GlobalTheory.CompanionTheory.ArchPI.archPI <;> assumption)
