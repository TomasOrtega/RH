import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetOfInducedFiltrationStatement
/- English proof (translation)
The claim follows from `GlobalTheory.T.jacquet_of_induced_filtration`.
-/
theorem _root_.GlobalTheory.T.jacquetOfInducedFiltration' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetOfInducedFiltration k := GlobalTheory.T.jacquet_of_induced_filtration
