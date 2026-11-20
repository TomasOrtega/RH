import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaCellSemisimplificationGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFinitenessStatement

/- English proof (translation)
The claim follows from `GlobalTheory.SmGL.CellSemis.cellSemisimplification GlobalTheory.T.bernstein_zelevinsky_finiteness`.
-/
theorem GlobalTheory.CompanionTheory.Glob.cellSemisimplification : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.CellSemisimplification k :=
  GlobalTheory.SmGL.CellSemis.cellSemisimplification GlobalTheory.T.bernstein_zelevinsky_finiteness
