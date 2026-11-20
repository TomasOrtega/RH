import Development.EtaleCohomology.TateTwists.EtaleTateTwistSectionsFlatOfQuotientIso

namespace LateralTheory.Fin.EtaleTateTwistSheafFlat
/- English proof (translation)
Apply `LateralTheory.EtaleFoundations.etale_tate_twist_sections_flat_of_quotient_iso` to reduce the goal to its premises.
-/
theorem etale_roots_of_unity_twist_flat_of_local_free : LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat := by
  apply LateralTheory.EtaleFoundations.etale_tate_twist_sections_flat_of_quotient_iso
/- English proof (translation)
The claim follows from `etale_roots_of_unity_twist_flat_of_local_free`.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat := etale_roots_of_unity_twist_flat_of_local_free
end LateralTheory.Fin.EtaleTateTwistSheafFlat
