import Development.EtaleCohomology.TateTwists.EtaleFreeSheafHomUniversalPropertyHolds

namespace LateralTheory.Fin.EtaleFreeSheafUniversalProperty
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_free_module_cohomology_hom_of_components : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := by
  apply LateralTheory.EtaleFoundations.etale_free_sheaf_hom_universal_property_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := etale_free_module_cohomology_hom_of_components
end LateralTheory.Fin.EtaleFreeSheafUniversalProperty
