import Development.EtaleCohomology.DivisorCycles.FinPolyPf

namespace LateralTheory.Fin.FinPoly
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem charpoly_eq_of_annihilating_poly_etale_instance : LateralTheory.DivDb.FinPoly := by
  apply LateralTheory.DivDb.FinPolyPf.FinPoly_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinPoly := charpoly_eq_of_annihilating_poly_etale_instance
end LateralTheory.Fin.FinPoly
