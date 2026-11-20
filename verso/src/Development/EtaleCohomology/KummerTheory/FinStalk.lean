import Development.EtaleCohomology.KummerTheory.FixStalk

namespace LateralTheory.Fin.Stalk
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_cohomology_stalk_compatibility_finite_coefficients_holds : LateralTheory.KummerTheory.Stalk := by
  apply LateralTheory.Fix.Stalk.intersectionNumber_baseChange
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.Stalk := etale_cohomology_stalk_compatibility_finite_coefficients_holds
end LateralTheory.Fin.Stalk
