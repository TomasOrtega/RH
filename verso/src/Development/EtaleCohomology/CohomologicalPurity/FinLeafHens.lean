import Development.EtaleCohomology.CohomologicalPurity.LeafCompPf
import Development.EtaleCohomology.CohomologicalPurity.LeafInvPf
import Development.EtaleCohomology.CohomologicalPurity.LeafRootStdPf
import Development.EtaleCohomology.CohomologicalPurity.LeafRootHensPf
import Development.EtaleCohomology.CohomologicalPurity.LeafRootPf
import Development.EtaleCohomology.CohomologicalPurity.LeafSupPf
import Development.EtaleCohomology.CohomologicalPurity.LeafCoeqPf
import Development.EtaleCohomology.CohomologicalPurity.LeafDiagPf
import Development.EtaleCohomology.CohomologicalPurity.LeafStagePf
import Development.EtaleCohomology.CohomologicalPurity.LeafColHensPf
import Development.EtaleCohomology.CohomologicalPurity.LeafColUnivPf
import Development.EtaleCohomology.CohomologicalPurity.LeafHensCut

namespace LateralTheory.Fin.LeafHens
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem henselization_compatible_maps_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafComp := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafComp_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem henselization_inverse_limit_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafInv := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafInv_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem standard_etale_simple_root_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafRootStd := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafRootStd_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem henselian_simple_root_lift_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafRootHens := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafRootHens_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem henselization_simple_root_lift_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafRoot := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafRoot_of <;> first | exact standard_etale_simple_root_of_henselization | exact henselian_simple_root_lift_of_henselization
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem henselization_supremum_neighborhood_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafSup := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafSup_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem henselization_coequalizer_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafCoeq := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafCoeq_of <;> first | exact henselization_inverse_limit_of_henselization | exact henselization_compatible_maps_of_henselization
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem henselization_diagonal_section_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafDiag := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafDiag_of <;> first | exact henselization_compatible_maps_of_henselization | exact henselization_supremum_neighborhood_of_henselization | exact henselization_coequalizer_of_henselization
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem henselization_etale_neighborhood_stage_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafStage := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafStage_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem henselization_colimit_henselian_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafColHens := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafColHens_of <;> first | exact henselization_etale_neighborhood_stage_of_henselization | exact henselization_inverse_limit_of_henselization | exact henselization_simple_root_lift_of_henselization
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem henselization_colimit_universal_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafColUniv := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafColUniv_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_purity_henselian_local_of_henselization : LateralTheory.CohomologicalPurity.LeafHens := by
  apply LateralTheory.CohomologicalPurity.Hz.goal_of <;> first | exact henselization_compatible_maps_of_henselization | exact henselization_inverse_limit_of_henselization | exact henselization_simple_root_lift_of_henselization | exact henselization_supremum_neighborhood_of_henselization | exact henselization_coequalizer_of_henselization | exact henselization_diagonal_section_of_henselization | exact henselization_etale_neighborhood_stage_of_henselization | exact henselization_colimit_henselian_of_henselization | exact henselization_colimit_universal_of_henselization
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafHens := etale_purity_henselian_local_of_henselization
end LateralTheory.Fin.LeafHens
