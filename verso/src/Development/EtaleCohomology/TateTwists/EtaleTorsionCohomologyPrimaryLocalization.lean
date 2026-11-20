import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder
import Development.EtaleCohomology.TateTwists.EtaleLocallyKummerRootsOfUnitsOfInvertibleOrder
import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib

namespace LateralTheory.Fin.EtalePrimitiveRootsExistLocally
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_locally_exists_primitive_root_of_unity : LateralTheory.EtaleFoundations.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder := by
  apply LateralTheory.EtaleFoundations.etale_locally_exists_primitive_root_of_unity_of_invertible_order
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_torsion_cohomology_primary_localization_kummer : LateralTheory.EtaleFoundations.EtaleLocallyKummerRootsOfUnits := by
  apply LateralTheory.EtaleFoundations.etale_locally_kummer_roots_of_units_of_invertible_order
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_torsion_cohomology_primary_localization : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally := by
  apply LateralTheory.EtaleFoundations.etale_locally_roots_of_unity_structure_of_exists_and_kummer <;> first | exact etale_locally_exists_primitive_root_of_unity | exact etale_torsion_cohomology_primary_localization_kummer
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally := etale_torsion_cohomology_primary_localization
end LateralTheory.Fin.EtalePrimitiveRootsExistLocally
