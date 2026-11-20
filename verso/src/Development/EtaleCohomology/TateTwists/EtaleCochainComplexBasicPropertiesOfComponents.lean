import Development.EtaleCohomology.TateTwists.EtaleSimplicialChainsBasicPropertiesHold

namespace LateralTheory.Fin.EtaleSimplicialChainsFreeDescription
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_cochain_complex_basic_properties_of_components : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := by
  apply LateralTheory.EtaleFoundations.etale_simplicial_chains_basic_properties_hold
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := etale_cochain_complex_basic_properties_of_components
end LateralTheory.Fin.EtaleSimplicialChainsFreeDescription
