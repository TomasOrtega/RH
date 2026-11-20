import Development.EtaleCohomology.DivisorCycles.MatUnitsOf

namespace LateralTheory.Fin.MatrixUnits₂
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_matrix_units_system_of_key : LateralTheory.DivDb.MatrixUnits₂ := by
  apply LateralTheory.DivDb.MatrixUnitConstruction.MatUnits_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.MatrixUnits₂ := etale_matrix_units_system_of_key
end LateralTheory.Fin.MatrixUnits₂
