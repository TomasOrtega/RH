import Development.EtaleCohomology.KummerTheory.PlaceResGoodPf
import Development.EtaleCohomology.KummerTheory.PlaceStepPf
import Development.EtaleCohomology.KummerTheory.PlaceExPfZorn
import Development.EtaleCohomology.KummerTheory.PlacePfVal
import Development.EtaleCohomology.KummerTheory.AlgExtPf

namespace LateralTheory.Fin.AlgExt
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_cohomology_place_restriction_good_reduction : LateralTheory.KummerTheory.PlaceResGood := by
  apply LateralTheory.KummerTheory.PlaceResGood_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_cohomology_place_localization_inductive_extension : LateralTheory.KummerTheory.PlaceStep := by
  apply LateralTheory.KummerTheory.PlaceStep_of <;> first | exact etale_cohomology_place_restriction_good_reduction
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_cohomology_place_localization_exists : LateralTheory.KummerTheory.PlaceEx := by
  apply LateralTheory.KummerTheory.PlaceEx_of_step <;> first | exact etale_cohomology_place_localization_inductive_extension
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_cohomology_place_localization_holds : LateralTheory.KummerTheory.Place := by
  apply LateralTheory.KummerTheory.Place_of_ex <;> first | exact etale_cohomology_place_localization_exists
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_cohomology_algebraic_extension_invariance_of_places : LateralTheory.KummerTheory.AlgExt := by
  apply LateralTheory.KummerTheory.AlgExt_of <;> first | exact etale_cohomology_place_localization_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.AlgExt := etale_cohomology_algebraic_extension_invariance_of_places
end LateralTheory.Fin.AlgExt
