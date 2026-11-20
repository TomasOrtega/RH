import Development.EtaleCohomology.TateTwists.EtaleTateTwistSectionsFlatOfQuotientIso

namespace LateralTheory.Fin.EtaleTateTwistSheafFlat
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_roots_of_unity_twist_flat_of_local_free : LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat := by
  apply LateralTheory.EtaleFoundations.etale_tate_twist_sections_flat_of_quotient_iso
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat := etale_roots_of_unity_twist_flat_of_local_free
end LateralTheory.Fin.EtaleTateTwistSheafFlat
