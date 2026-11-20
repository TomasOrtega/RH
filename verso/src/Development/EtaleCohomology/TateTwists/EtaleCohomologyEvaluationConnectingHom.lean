import Development.EtaleCohomology.TateTwists.PpEvBasicPf
import Development.EtaleCohomology.TateTwists.PpEvMkPf
import Development.EtaleCohomology.TateTwists.PpEvDeltaPf
import Development.EtaleCohomology.TateTwists.EtaleSemilinearCohomologyOperationExistsOfEvalua

namespace LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_evaluation_map_basic_of_components : LateralTheory.EtaleFoundations.pp_ev_basic := by
  apply LateralTheory.EtaleFoundations.pp_ev_basic_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_cohomology_evaluation_mk : LateralTheory.EtaleFoundations.pp_ev_mk := by
  apply LateralTheory.EtaleFoundations.pp_ev_mk_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_cohomology_evaluation_connecting_hom : LateralTheory.EtaleFoundations.pp_ev_delta := by
  apply LateralTheory.EtaleFoundations.pp_ev_delta_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_torsion_cohomology_operation_spec : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := by
  apply LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_exists_of_evaluation <;> first | exact etale_evaluation_map_basic_of_components | exact etale_cohomology_evaluation_mk | exact etale_cohomology_evaluation_connecting_hom
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := etale_torsion_cohomology_operation_spec
end LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses
