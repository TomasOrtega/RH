import Development.EtaleCohomology.TateTwists.EtaleSheafSectionsGlueOfForgetIsSheaf

namespace LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue
/- English proof (translation)
Apply `LateralTheory.EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf` to reduce the goal to its premises.
-/
theorem etale_sections_glue_over_cover_of_components : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue := by
  apply LateralTheory.EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf
/- English proof (translation)
The claim follows from `etale_sections_glue_over_cover_of_components`.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue := etale_sections_glue_over_cover_of_components
end LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue
