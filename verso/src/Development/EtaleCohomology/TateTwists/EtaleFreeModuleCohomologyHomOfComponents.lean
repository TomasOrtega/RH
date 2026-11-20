import Development.EtaleCohomology.TateTwists.EtaleFreeSheafHomUniversalPropertyHolds

namespace LateralTheory.Fin.EtaleFreeSheafUniversalProperty
/- English proof (translation)
Apply `LateralTheory.EtaleFoundations.etale_free_sheaf_hom_universal_property_holds` to reduce the goal to its premises.
-/
theorem etale_free_module_cohomology_hom_of_components : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := by
  apply LateralTheory.EtaleFoundations.etale_free_sheaf_hom_universal_property_holds
/- English proof (translation)
The claim follows from `etale_free_module_cohomology_hom_of_components`.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := etale_free_module_cohomology_hom_of_components
end LateralTheory.Fin.EtaleFreeSheafUniversalProperty
