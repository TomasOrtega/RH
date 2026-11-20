import Development.EtaleCohomology.KummerTheory.FixStalk

namespace LateralTheory.Fin.Stalk
/- English proof (translation)
Apply `LateralTheory.Fix.Stalk.intersectionNumber_baseChange` to reduce the goal to its premises.
-/
theorem etale_cohomology_stalk_compatibility_finite_coefficients_holds : LateralTheory.KummerTheory.Stalk := by
  apply LateralTheory.Fix.Stalk.intersectionNumber_baseChange
/- English proof (translation)
The claim follows from `etale_cohomology_stalk_compatibility_finite_coefficients_holds`.
-/
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.Stalk := etale_cohomology_stalk_compatibility_finite_coefficients_holds
end LateralTheory.Fin.Stalk
