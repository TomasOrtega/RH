import Development.EtaleCohomology.CohomologicalPurity.LeafMonoPf
import Development.EtaleCohomology.CohomologicalPurity.LeafPushPf
import Development.EtaleCohomology.CohomologicalPurity.LeafGoodPf
import Development.EtaleCohomology.CohomologicalPurity.LeafDeltaPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExactPf
import Development.EtaleCohomology.CohomologicalPurity.LeafGenPf
import Development.EtaleCohomology.CohomologicalPurity.LeafImgHomPf
import Development.EtaleCohomology.CohomologicalPurity.LeafImgPf
import Development.EtaleCohomology.CohomologicalPurity.LeafBdCut
import Development.EtaleCohomology.CohomologicalPurity.PresSheafify
import Development.EtaleCohomology.CohomologicalPurity.FreePMapMk

namespace LateralTheory.Fin.LeafBd
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
The claim follows from `etale_boundary_map_of_thom_isomorphism`.
-/
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafBd := etale_boundary_map_of_thom_isomorphism
end LateralTheory.Fin.LeafBd
