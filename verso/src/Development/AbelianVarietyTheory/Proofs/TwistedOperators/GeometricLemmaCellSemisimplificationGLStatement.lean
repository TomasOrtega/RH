import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaCellSemisimplificationGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FGeometricLemmaCellSemisimplificationGL.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.geometricLemma_cell_semisimplification_GL : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.CellSemisimplification k := by
  first | exact @GlobalTheory.SmGL.CellSemis.cellSemisimplification | exact GlobalTheory.SmGL.CellSemis.cellSemisimplification | (intros; apply GlobalTheory.SmGL.CellSemis.cellSemisimplification <;> assumption)
