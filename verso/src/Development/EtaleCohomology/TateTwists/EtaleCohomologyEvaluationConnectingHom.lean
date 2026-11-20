import Development.EtaleCohomology.TateTwists.PpEvBasicPf
import Development.EtaleCohomology.TateTwists.PpEvMkPf
import Development.EtaleCohomology.TateTwists.PpEvDeltaPf
import Development.EtaleCohomology.TateTwists.EtaleSemilinearCohomologyOperationExistsOfEvalua

namespace LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses
/- English proof (translation)
Apply `LateralTheory.EtaleFoundations.pp_ev_basic_of` to reduce the goal to its premises.
-/
theorem etale_evaluation_map_basic_of_components : LateralTheory.EtaleFoundations.pp_ev_basic := by
  apply LateralTheory.EtaleFoundations.pp_ev_basic_of
/- English proof (translation)
Apply `LateralTheory.EtaleFoundations.pp_ev_mk_of` to reduce the goal to its premises.
-/
theorem etale_cohomology_evaluation_mk : LateralTheory.EtaleFoundations.pp_ev_mk := by
  apply LateralTheory.EtaleFoundations.pp_ev_mk_of
/- English proof (translation)
Apply `LateralTheory.EtaleFoundations.pp_ev_delta_of` to reduce the goal to its premises.
-/
theorem etale_cohomology_evaluation_connecting_hom : LateralTheory.EtaleFoundations.pp_ev_delta := by
  apply LateralTheory.EtaleFoundations.pp_ev_delta_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_exists_of_evaluation <;> first | exact etale_evaluation_map_basic_of_components | exact etale_cohomology_evaluation_mk | exact etale_cohomology_evaluation_connecting_hom`.
-/
theorem etale_torsion_cohomology_operation_spec : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := by
  apply LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_exists_of_evaluation <;> first | exact etale_evaluation_map_basic_of_components | exact etale_cohomology_evaluation_mk | exact etale_cohomology_evaluation_connecting_hom
/- English proof (translation)
The claim follows from `etale_torsion_cohomology_operation_spec`.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := etale_torsion_cohomology_operation_spec
end LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses
