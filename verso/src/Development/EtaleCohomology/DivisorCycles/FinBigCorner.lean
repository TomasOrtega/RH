import Development.EtaleCohomology.DivisorCycles.BigCorner2

namespace LateralTheory.Fin.BigCorner
/- English proof (translation)
Apply `LateralTheory.DivDb.BigCorner₂.BigCorner_of` to reduce the goal to its premises.
-/
theorem etale_big_corner_statement_holds_assembled : LateralTheory.DivDb.BigCorner := by
  apply LateralTheory.DivDb.BigCorner₂.BigCorner_of
/- English proof (translation)
The claim follows from `etale_big_corner_statement_holds_assembled`.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.BigCorner := etale_big_corner_statement_holds_assembled
end LateralTheory.Fin.BigCorner
