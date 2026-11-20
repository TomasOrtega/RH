import Development.EtaleCohomology.TateTwists.EtaleFreePresheafMayerVietorisShortExactHolds
import Development.EtaleCohomology.TateTwists.EtaleChainsMayerVietorisShortExactOfFree

namespace LateralTheory.Fin.EtaleMayerVietorisChainsShortExact
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_mayer_vietoris_short_exact_sequence_free_of_components : LateralTheory.EtaleFoundations.EtaleFreePresheafMayerVietorisShortExact := by
  apply LateralTheory.EtaleFoundations.etale_free_presheaf_mayer_vietoris_short_exact_holds
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_mayer_vietoris_short_exact_sequence_of_components : LateralTheory.EtaleFoundations.EtaleMayerVietorisChainsShortExact := by
  apply LateralTheory.EtaleFoundations.etale_chains_mayer_vietoris_short_exact_of_free <;> first | exact etale_mayer_vietoris_short_exact_sequence_free_of_components
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleMayerVietorisChainsShortExact := etale_mayer_vietoris_short_exact_sequence_of_components
end LateralTheory.Fin.EtaleMayerVietorisChainsShortExact
