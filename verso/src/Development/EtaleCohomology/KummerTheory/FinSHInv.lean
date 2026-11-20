import Development.EtaleCohomology.KummerTheory.PlaceResGoodPf
import Development.EtaleCohomology.KummerTheory.PlaceStepPf
import Development.EtaleCohomology.KummerTheory.PlaceExPfZorn
import Development.EtaleCohomology.KummerTheory.PlacePfVal
import Development.EtaleCohomology.KummerTheory.AlgExtPf
import Development.EtaleCohomology.KummerTheory.SHInsepLocPf
import Development.EtaleCohomology.KummerTheory.SHInsepHensPf
import Development.EtaleCohomology.KummerTheory.SHInsepResPf
import Development.EtaleCohomology.KummerTheory.SHInsepPf
import Development.EtaleCohomology.KummerTheory.PrimTorsPf
import Development.EtaleCohomology.KummerTheory.ShSectPf
import Development.EtaleCohomology.KummerTheory.SecSHPf
import Development.EtaleCohomology.KummerTheory.TwSecPf
import Development.EtaleCohomology.KummerTheory.InsepPf
import Development.EtaleCohomology.KummerTheory.SHInvPf

namespace LateralTheory.Fin.SHInv
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
Apply `LateralTheory.KummerTheory.SHInsepLoc_of` to reduce the goal to its premises.
-/
theorem etale_strict_henselization_inseparable_localization_in_henselization_i : LateralTheory.KummerTheory.SHInsepLoc := by
  apply LateralTheory.KummerTheory.SHInsepLoc_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.KummerTheory.SHInsepHens_of <;> first | exact etale_strict_henselization_inseparable_localization_in_henselization_i`.
-/
theorem etale_strict_henselization_inseparable_henselian_pair_in_henselization : LateralTheory.KummerTheory.SHInsepHens := by
  apply LateralTheory.KummerTheory.SHInsepHens_of <;> first | exact etale_strict_henselization_inseparable_localization_in_henselization_i
/- English proof (translation)
Apply `LateralTheory.KummerTheory.SHInsepRes_of` to reduce the goal to its premises.
-/
theorem etale_strict_henselization_inseparable_residue_field_in_henselization_ : LateralTheory.KummerTheory.SHInsepRes := by
  apply LateralTheory.KummerTheory.SHInsepRes_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.KummerTheory.SHInsep_of <;> first | exact etale_strict_henselization_inseparable_localization_in_henselization_i | exact etale_strict_henselization_inseparable_henselian_pair_in_henselization | exact etale_strict_henselization_inseparable_residue_field_in_hens …`.
-/
theorem etale_strict_henselization_inseparable_invariance_in_henselization_inv : LateralTheory.KummerTheory.SHInsep := by
  apply LateralTheory.KummerTheory.SHInsep_of <;> first | exact etale_strict_henselization_inseparable_localization_in_henselization_i | exact etale_strict_henselization_inseparable_henselian_pair_in_henselization | exact etale_strict_henselization_inseparable_residue_field_in_henselization_
/- English proof (translation)
Apply `LateralTheory.KummerTheory.PrimTors_of` to reduce the goal to its premises.
-/
theorem etale_prime_to_characteristic_torsion_cohomology_in_henselization_inva : LateralTheory.KummerTheory.PrimTors := by
  apply LateralTheory.KummerTheory.PrimTors_of
/- English proof (translation)
Apply `LateralTheory.KummerTheory.ShSectPf.ShSect_of` to reduce the goal to its premises.
-/
theorem etale_sheaf_sections_over_strict_henselization_in_henselization_invari : LateralTheory.KummerTheory.SecSHPf.ShSect := by
  apply LateralTheory.KummerTheory.ShSectPf.ShSect_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.KummerTheory.SecSH_of <;> first | exact etale_sheaf_sections_over_strict_henselization_in_henselization_invari`.
-/
theorem etale_sections_over_strict_henselization_in_henselization_invariance_a : LateralTheory.KummerTheory.SecSH := by
  apply LateralTheory.KummerTheory.SecSH_of <;> first | exact etale_sheaf_sections_over_strict_henselization_in_henselization_invari
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.KummerTheory.TwSec_of <;> first | exact etale_prime_to_characteristic_torsion_cohomology_in_henselization_inva | exact etale_sections_over_strict_henselization_in_henselization_invariance_a`.
-/
theorem etale_twisted_sections_cohomology_isomorphism_in_henselization_invaria : LateralTheory.KummerTheory.TwSec := by
  apply LateralTheory.KummerTheory.TwSec_of <;> first | exact etale_prime_to_characteristic_torsion_cohomology_in_henselization_inva | exact etale_sections_over_strict_henselization_in_henselization_invariance_a
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.KummerTheory.InsepPf.Insep_of <;> first | exact etale_strict_henselization_inseparable_invariance_in_henselization_inv | exact etale_twisted_sections_cohomology_isomorphism_in_henselization_invaria`.
-/
theorem etale_purely_inseparable_extension_cohomology_invariant_in_henselizati : LateralTheory.KummerTheory.Insep := by
  apply LateralTheory.KummerTheory.InsepPf.Insep_of <;> first | exact etale_strict_henselization_inseparable_invariance_in_henselization_inv | exact etale_twisted_sections_cohomology_isomorphism_in_henselization_invaria
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.KummerTheory.SHInv_of <;> first | exact etale_cohomology_algebraic_extension_invariance_of_places | exact etale_purely_inseparable_extension_cohomology_invariant_in_henselizati`.
-/
theorem etale_strict_henselization_invariance_of_cohomology_in_henselization_i : LateralTheory.KummerTheory.SHInv := by
  apply LateralTheory.KummerTheory.SHInv_of <;> first | exact etale_cohomology_algebraic_extension_invariance_of_places | exact etale_purely_inseparable_extension_cohomology_invariant_in_henselizati
/- English proof (translation)
The claim follows from `etale_strict_henselization_invariance_of_cohomology_in_henselization_i`.
-/
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.SHInv := etale_strict_henselization_invariance_of_cohomology_in_henselization_i
end LateralTheory.Fin.SHInv
