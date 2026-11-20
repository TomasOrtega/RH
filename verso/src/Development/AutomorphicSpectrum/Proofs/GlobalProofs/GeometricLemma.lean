import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.InducedCellSemisimplificationStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetOfInducedFiltration

namespace GlobalTheory.CompanionTheory.GeoLink

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

A detailed English derivation is pending.
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
