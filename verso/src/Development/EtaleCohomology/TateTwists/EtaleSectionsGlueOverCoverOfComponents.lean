import Development.EtaleCohomology.TateTwists.EtaleSheafSectionsGlueOfForgetIsSheaf

namespace LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_sections_glue_over_cover_of_components : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue := by
  apply LateralTheory.EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue := etale_sections_glue_over_cover_of_components
end LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue
