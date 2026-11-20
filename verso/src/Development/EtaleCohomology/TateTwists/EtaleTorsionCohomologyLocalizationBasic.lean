import Development.EtaleCohomology.TateTwists.EtaleLocalPropertyBasicClosureProperties

namespace LateralTheory.Fin.EtaleLocalPropertyBasicClosure
/- English proof (translation)
Apply `LateralTheory.EtaleFoundations.etale_local_property_basic_closure_properties` to reduce the goal to its premises.
-/
theorem etale_torsion_cohomology_localization_basic : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure := by
  apply LateralTheory.EtaleFoundations.etale_local_property_basic_closure_properties
/- English proof (translation)
The claim follows from `etale_torsion_cohomology_localization_basic`.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure := etale_torsion_cohomology_localization_basic
end LateralTheory.Fin.EtaleLocalPropertyBasicClosure
