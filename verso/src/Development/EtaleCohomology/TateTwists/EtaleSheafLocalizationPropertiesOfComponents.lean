import Development.EtaleCohomology.TateTwists.EtaleSheafSectionsEqOfLocallyEq

namespace LateralTheory.Fin.EtaleSheafificationSectionsLocallyFromPresheaf
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_sheaf_localization_properties_of_components : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := by
  apply LateralTheory.EtaleFoundations.ShfLocPf.etale_sheaf_sections_eq_of_locally_eq
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := etale_sheaf_localization_properties_of_components
end LateralTheory.Fin.EtaleSheafificationSectionsLocallyFromPresheaf
