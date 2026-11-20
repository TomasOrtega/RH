import Development.EtaleCohomology.TateTwists.EtaleInjectiveSheafSectionsInjectiveHolds
import Development.EtaleCohomology.TateTwists.ZmodInjectiveModuleFlatHolds
import Development.EtaleCohomology.TateTwists.EtaleKInjectiveExtensionAlongQuasiIsoFromSingle

namespace LateralTheory.Fin.EtaleTwistResolutionUniversalExtension
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_twisted_resolution_sections_injective : LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective := by
  apply LateralTheory.EtaleFoundations.etale_injective_sheaf_sections_injective_holds
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_twisted_resolution_quasiIso_flat : LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat := by
  apply LateralTheory.EtaleFoundations.zmod_injective_module_flat_holds
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_twisted_resolution_exists_of_flat_sections : LateralTheory.EtaleFoundations.EtaleTwistResolutionUniversalExtension := by
  apply LateralTheory.EtaleFoundations.etale_tate_twist_resolution_universal_of_injective_sections_and_zmod_f <;> first | exact etale_twisted_resolution_sections_injective | exact etale_twisted_resolution_quasiIso_flat
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTwistResolutionUniversalExtension := etale_twisted_resolution_exists_of_flat_sections
end LateralTheory.Fin.EtaleTwistResolutionUniversalExtension
