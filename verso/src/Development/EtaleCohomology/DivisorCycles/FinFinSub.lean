import Development.EtaleCohomology.DivisorCycles.FinSubOf

namespace LateralTheory.Fin.FinSub
/- English proof (translation)
Apply `LateralTheory.DivDb.FiniteSubrepresentation.FinSub_of` to reduce the goal to its premises.
-/
theorem finite_subrepresentation_etale_charpoly_instance : LateralTheory.DivDb.FinSub := by
  apply LateralTheory.DivDb.FiniteSubrepresentation.FinSub_of
/- English proof (translation)
The claim follows from `finite_subrepresentation_etale_charpoly_instance`.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinSub := finite_subrepresentation_etale_charpoly_instance
end LateralTheory.Fin.FinSub
