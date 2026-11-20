import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.InducedCellSemisimplification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FInducedCellSemisimplification.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.induced_cell_semisimplification : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.CellSemisimplification k := by
  first | exact @GlobalTheory.CompanionTheory.Glob.cellSemisimplification | exact GlobalTheory.CompanionTheory.Glob.cellSemisimplification | (intros; apply GlobalTheory.CompanionTheory.Glob.cellSemisimplification <;> assumption)
