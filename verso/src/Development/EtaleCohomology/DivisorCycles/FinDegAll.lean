import Development.EtaleCohomology.DivisorCycles.DegPoly2
import Development.EtaleCohomology.DivisorCycles.EntriesCont

namespace LateralTheory.Fin.DegAll
/- English proof (translation)
Apply `LateralTheory.DivDb.DegPoly₂.DegPoly_of` to reduce the goal to its premises.
-/
theorem etale_degree_polynomial_bound : LateralTheory.DivDb.DegPoly := by
  apply LateralTheory.DivDb.DegPoly₂.DegPoly_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.DivDb.DegAll_of <;> first | exact etale_degree_polynomial_bound`.
-/
theorem etale_rep_image_degree_bound_all_holds_assembled : LateralTheory.DivDb.DegAll := by
  apply LateralTheory.DivDb.DegAll_of <;> first | exact etale_degree_polynomial_bound
/- English proof (translation)
The claim follows from `etale_rep_image_degree_bound_all_holds_assembled`.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.DegAll := etale_rep_image_degree_bound_all_holds_assembled
end LateralTheory.Fin.DegAll
