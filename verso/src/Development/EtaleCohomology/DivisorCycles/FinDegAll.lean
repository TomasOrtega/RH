import Development.EtaleCohomology.DivisorCycles.DegPoly2
import Development.EtaleCohomology.DivisorCycles.EntriesCont

namespace LateralTheory.Fin.DegAll
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_degree_polynomial_bound : LateralTheory.DivDb.DegPoly := by
  apply LateralTheory.DivDb.DegPoly₂.DegPoly_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_rep_image_degree_bound_all_holds_assembled : LateralTheory.DivDb.DegAll := by
  apply LateralTheory.DivDb.DegAll_of <;> first | exact etale_degree_polynomial_bound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.DegAll := etale_rep_image_degree_bound_all_holds_assembled
end LateralTheory.Fin.DegAll
