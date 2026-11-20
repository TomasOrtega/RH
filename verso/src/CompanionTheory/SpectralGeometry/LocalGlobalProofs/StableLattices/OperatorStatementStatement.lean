import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OperatorStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgFl.stOp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FOperatorStatement.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.OperatorStatement : StOp := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stOp | exact GlobalTheory.CompanionTheory.RgFl.stOp | (intros; apply GlobalTheory.CompanionTheory.RgFl.stOp <;> assumption)
