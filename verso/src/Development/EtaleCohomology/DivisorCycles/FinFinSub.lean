import Development.EtaleCohomology.DivisorCycles.FinSubOf

namespace LateralTheory.Fin.FinSub
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem finite_subrepresentation_etale_charpoly_instance : LateralTheory.DivDb.FinSub := by
  apply LateralTheory.DivDb.FiniteSubrepresentation.FinSub_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinSub := finite_subrepresentation_etale_charpoly_instance
end LateralTheory.Fin.FinSub
