import Development.EtaleCohomology.CohomologicalPurity.LeafMonoPf
import Development.EtaleCohomology.CohomologicalPurity.PresSheafify
import Development.EtaleCohomology.CohomologicalPurity.LeafGoodPf
import Development.EtaleCohomology.CohomologicalPurity.LeafDeltaPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExactPf
import Development.EtaleCohomology.CohomologicalPurity.FreePMapMk
import Development.EtaleCohomology.CohomologicalPurity.LeafImgHomPf
import Development.EtaleCohomology.CohomologicalPurity.LeafImgPf
import Development.EtaleCohomology.CohomologicalPurity.LeafBdCut
import Development.EtaleCohomology.CohomologicalPurity.LeafExcIdentPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExcDegPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExcFormalPf
import Development.EtaleCohomology.CohomologicalPurity.LeafFreeCokInjPf
import Development.EtaleCohomology.CohomologicalPurity.LeafFreeCokPfSurj
import Development.EtaleCohomology.CohomologicalPurity.LeafSurjGeoPf
import Development.EtaleCohomology.CohomologicalPurity.LeafInjGeoPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExcSheafCut
import Development.EtaleCohomology.CohomologicalPurity.LeafExcPf
import Development.EtaleCohomology.CohomologicalPurity.FixLeafIndExc

namespace LateralTheory.Fin.LeafIndExc
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.Bd.LeafMono_of` to reduce the goal to its premises.
-/
theorem etale_boundary_monomorphism_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafMono := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafMono_of
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.Bd.LeafPush_of` to reduce the goal to its premises.
-/
theorem etale_relative_boundary_pushout_property_holds : LateralTheory.CohomologicalPurity.Bd.LeafPush := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafPush_of
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.Bd.LeafGood_of` to reduce the goal to its premises.
-/
theorem etale_boundary_good_pair_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafGood := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafGood_of
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.Bd.LeafDelta_of` to reduce the goal to its premises.
-/
theorem etale_boundary_connecting_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafDelta := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafDelta_of
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.Bd.LeafExact_of` to reduce the goal to its premises.
-/
theorem etale_boundary_exact_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafExact := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafExact_of
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.Bd.LeafGen_of` to reduce the goal to its premises.
-/
theorem etale_boundary_generator_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafGen := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafGen_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.CohomologicalPurity.Bd.LeafImgHom_of <;> first | exact etale_boundary_generator_of_thom_isomorphism`.
-/
theorem etale_boundary_image_hom_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafImgHom := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafImgHom_of <;> first | exact etale_boundary_generator_of_thom_isomorphism
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.CohomologicalPurity.Bd.LeafImg_of <;> first | exact etale_boundary_image_hom_of_thom_isomorphism`.
-/
theorem etale_boundary_image_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafImg := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafImg_of <;> first | exact etale_boundary_image_hom_of_thom_isomorphism
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.CohomologicalPurity.Bd.goal_of <;> first | exact etale_boundary_monomorphism_of_thom_isomorphism | exact etale_relative_boundary_pushout_property_holds | exact etale_boundary_good_pair_of_thom_isomorphism | exact etale_boundary_connecting_of_thom_isomorphism | …`.
-/
theorem etale_boundary_map_of_thom_isomorphism : LateralTheory.CohomologicalPurity.LeafBd := by
  apply LateralTheory.CohomologicalPurity.Bd.goal_of <;> first | exact etale_boundary_monomorphism_of_thom_isomorphism | exact etale_relative_boundary_pushout_property_holds | exact etale_boundary_good_pair_of_thom_isomorphism | exact etale_boundary_connecting_of_thom_isomorphism | exact etale_boundary_exact_of_thom_isomorphism | exact etale_boundary_generator_of_thom_isomorphism | exact etale_boundary_image_hom_of_thom_isomorphism | exact etale_boundary_image_of_thom_isomorphism
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
Apply the tactic sequence `apply LateralTheory.Fix.LeafIndExc.intersectionNumber_baseChange <;> first | exact etale_boundary_map_of_thom_isomorphism | exact etale_excision_isomorphism_of_excision`.
-/
theorem etale_excision_inductive_of_reduction : LateralTheory.CohomologicalPurity.LeafIndExc := by
  apply LateralTheory.Fix.LeafIndExc.intersectionNumber_baseChange <;> first | exact etale_boundary_map_of_thom_isomorphism | exact etale_excision_isomorphism_of_excision
/- English proof (translation)
The claim follows from `etale_excision_inductive_of_reduction`.
-/
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafIndExc := etale_excision_inductive_of_reduction
end LateralTheory.Fin.LeafIndExc
