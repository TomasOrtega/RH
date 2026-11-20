import Development.EtaleCohomology.KummerTheory.PlaceResGoodPf
import Development.EtaleCohomology.KummerTheory.PlaceStepPf
import Development.EtaleCohomology.KummerTheory.PlaceExPfZorn
import Development.EtaleCohomology.KummerTheory.PlacePfVal
import Development.EtaleCohomology.KummerTheory.AlgExtPf

namespace LateralTheory.Fin.AlgExt
/- English proof (translation)
Apply `LateralTheory.KummerTheory.PlaceResGood_of` to reduce the goal to its premises.
-/
theorem etale_cohomology_place_restriction_good_reduction : LateralTheory.KummerTheory.PlaceResGood := by
  apply LateralTheory.KummerTheory.PlaceResGood_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.KummerTheory.PlaceStep_of <;> first | exact etale_cohomology_place_restriction_good_reduction`.
-/
theorem etale_cohomology_place_localization_inductive_extension : LateralTheory.KummerTheory.PlaceStep := by
  apply LateralTheory.KummerTheory.PlaceStep_of <;> first | exact etale_cohomology_place_restriction_good_reduction
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.KummerTheory.PlaceEx_of_step <;> first | exact etale_cohomology_place_localization_inductive_extension`.
-/
theorem etale_cohomology_place_localization_exists : LateralTheory.KummerTheory.PlaceEx := by
  apply LateralTheory.KummerTheory.PlaceEx_of_step <;> first | exact etale_cohomology_place_localization_inductive_extension
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.KummerTheory.Place_of_ex <;> first | exact etale_cohomology_place_localization_exists`.
-/
theorem etale_cohomology_place_localization_holds : LateralTheory.KummerTheory.Place := by
  apply LateralTheory.KummerTheory.Place_of_ex <;> first | exact etale_cohomology_place_localization_exists
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.KummerTheory.AlgExt_of <;> first | exact etale_cohomology_place_localization_holds`.
-/
theorem etale_cohomology_algebraic_extension_invariance_of_places : LateralTheory.KummerTheory.AlgExt := by
  apply LateralTheory.KummerTheory.AlgExt_of <;> first | exact etale_cohomology_place_localization_holds
/- English proof (translation)
The claim follows from `etale_cohomology_algebraic_extension_invariance_of_places`.
-/
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.AlgExt := etale_cohomology_algebraic_extension_invariance_of_places
end LateralTheory.Fin.AlgExt
