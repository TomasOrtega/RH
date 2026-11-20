import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeAlgebraStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.HeckeBern.stHecke` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FHeckeAlgebraStatement.lean&line=198#L198)
-/
theorem _root_.GlobalTheory.T.HeckeAlgebraTheorem : StHecke := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBern.stHecke | exact GlobalTheory.CompanionTheory.HeckeBern.stHecke | (intros; apply GlobalTheory.CompanionTheory.HeckeBern.stHecke <;> assumption)
