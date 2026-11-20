import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.InducedCellSemisimplificationStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetOfInducedFiltration

namespace GlobalTheory.CompanionTheory.GeoLink

/- English proof (translation)
Introduce `k _ _ _ _`. Establish `h` using `GlobalTheory.T.induced_cell_semisimplification k`. Establish `hloc` using `GlobalTheory.T.jacquetOfInducedFiltration' k`. Use `first`. Consider the case `exact h hloc`.

Consider the case `exact h.mpr hloc`. Consider the case `exact ⟨h, hloc⟩`. Consider the case `exact ⟨hloc, h⟩`. Consider the case `exact hloc.mpr h`. Consider the case `exact hloc h`.

Consider the case `exact hloc`.
-/
theorem geometricLemma : GlobalTheory.Published.GeometricLemma := by
  intro k _ _ _ _
  have h := GlobalTheory.T.induced_cell_semisimplification k
  have hloc := GlobalTheory.T.jacquetOfInducedFiltration' k
  first
    | exact h hloc
    | exact h.mpr hloc
    | exact ⟨h, hloc⟩
    | exact ⟨hloc, h⟩
    | exact hloc.mpr h
    | exact hloc h
    | exact hloc

end GlobalTheory.CompanionTheory.GeoLink
