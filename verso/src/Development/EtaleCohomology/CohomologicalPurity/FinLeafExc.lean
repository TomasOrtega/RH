import Development.EtaleCohomology.CohomologicalPurity.LeafExcIdentPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExcDegPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExcFormalPf
import Development.EtaleCohomology.CohomologicalPurity.LeafFreeCokInjPf
import Development.EtaleCohomology.CohomologicalPurity.LeafFreeCokPfSurj
import Development.EtaleCohomology.CohomologicalPurity.LeafSurjGeoPf
import Development.EtaleCohomology.CohomologicalPurity.LeafInjGeoPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExcSheafCut
import Development.EtaleCohomology.CohomologicalPurity.LeafExcPf

namespace LateralTheory.Fin.LeafExc
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.EtaleExcIdent` to reduce the goal to its premises.
-/
theorem etale_excision_identification_of_excision : LateralTheory.CohomologicalPurity.LeafExcIdent := by
  apply LateralTheory.CohomologicalPurity.EtaleExcIdent
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.LeafExcDeg_of` to reduce the goal to its premises.
-/
theorem etale_excision_cohomological_degree_of_excision : LateralTheory.CohomologicalPurity.LeafExcDeg := by
  apply LateralTheory.CohomologicalPurity.LeafExcDeg_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.CohomologicalPurity.LeafExcFormal_of <;> first | exact etale_excision_identification_of_excision | exact etale_excision_cohomological_degree_of_excision`.
-/
theorem etale_excision_formal_reduction_of_excision : LateralTheory.CohomologicalPurity.LeafExcFormal := by
  apply LateralTheory.CohomologicalPurity.LeafExcFormal_of <;> first | exact etale_excision_identification_of_excision | exact etale_excision_cohomological_degree_of_excision
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.LeafFreeCokInj_of` to reduce the goal to its premises.
-/
theorem etale_excision_free_cokernel_injective_of_excision : LateralTheory.CohomologicalPurity.LeafFreeCokInj := by
  apply LateralTheory.CohomologicalPurity.LeafFreeCokInj_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.CohomologicalPurity.LeafFreeCok_of_inj <;> first | exact etale_excision_free_cokernel_injective_of_excision`.
-/
theorem etale_excision_cokernel_free_of_excision : LateralTheory.CohomologicalPurity.LeafFreeCok := by
  apply LateralTheory.CohomologicalPurity.LeafFreeCok_of_inj <;> first | exact etale_excision_free_cokernel_injective_of_excision
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.LeafSurjGeo_of` to reduce the goal to its premises.
-/
theorem etale_excision_surjective_geometric_points_of_excision : LateralTheory.CohomologicalPurity.LeafSurjGeo := by
  apply LateralTheory.CohomologicalPurity.LeafSurjGeo_of
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.LeafInjGeo_of` to reduce the goal to its premises.
-/
theorem etale_excision_injective_geometric_points_of_excision : LateralTheory.CohomologicalPurity.LeafInjGeo := by
  apply LateralTheory.CohomologicalPurity.LeafInjGeo_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.CohomologicalPurity.LeafExcSheaf_of <;> first | exact etale_excision_cokernel_free_of_excision | exact etale_excision_surjective_geometric_points_of_excision | exact etale_excision_injective_geometric_points_of_excision`.
-/
theorem etale_excision_sheaf_level_of_excision : LateralTheory.CohomologicalPurity.LeafExcSheaf := by
  apply LateralTheory.CohomologicalPurity.LeafExcSheaf_of <;> first | exact etale_excision_cokernel_free_of_excision | exact etale_excision_surjective_geometric_points_of_excision | exact etale_excision_injective_geometric_points_of_excision
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.CohomologicalPurity.LeafExc_of <;> first | exact etale_excision_formal_reduction_of_excision | exact etale_excision_sheaf_level_of_excision`.
-/
theorem etale_excision_isomorphism_of_excision : LateralTheory.CohomologicalPurity.LeafExc := by
  apply LateralTheory.CohomologicalPurity.LeafExc_of <;> first | exact etale_excision_formal_reduction_of_excision | exact etale_excision_sheaf_level_of_excision
/- English proof (translation)
The claim follows from `etale_excision_isomorphism_of_excision`.
-/
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafExc := etale_excision_isomorphism_of_excision
end LateralTheory.Fin.LeafExc
