import Development.EtaleCohomology.DivisorCycles.BigCorner2

namespace LateralTheory.Fin.BigCorner
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_big_corner_statement_holds_assembled : LateralTheory.DivDb.BigCorner := by
  apply LateralTheory.DivDb.BigCorner₂.BigCorner_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.BigCorner := etale_big_corner_statement_holds_assembled
end LateralTheory.Fin.BigCorner
