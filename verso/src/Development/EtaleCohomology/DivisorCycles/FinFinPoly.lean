import Development.EtaleCohomology.DivisorCycles.FinPolyPf

namespace LateralTheory.Fin.FinPoly
/- English proof (translation)
Apply `LateralTheory.DivDb.FinPolyPf.FinPoly_of` to reduce the goal to its premises.
-/
theorem charpoly_eq_of_annihilating_poly_etale_instance : LateralTheory.DivDb.FinPoly := by
  apply LateralTheory.DivDb.FinPolyPf.FinPoly_of
/- English proof (translation)
The claim follows from `charpoly_eq_of_annihilating_poly_etale_instance`.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinPoly := charpoly_eq_of_annihilating_poly_etale_instance
end LateralTheory.Fin.FinPoly
