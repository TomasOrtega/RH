import Development.EtaleCohomology.TateTwists.LeafAcycPf
import Development.EtaleCohomology.TateTwists.LeafAwPf
import Development.EtaleCohomology.TateTwists.LeafWaPf
import Development.EtaleCohomology.TateTwists.EtaleSteenrodPrismHomotopyOfAcyclicAlexanderWhit

namespace LateralTheory.Fin.PrismAlexanderWhitneySwapChainHomotopy
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_steenrod_acyclic_models_of_components : LateralTheory.EtaleFoundations.SteenPf.leaf_acyc := by
  apply LateralTheory.EtaleFoundations.SteenPf.leaf_acyc_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_steenrod_alexander_whitney_compatibility_of_components : LateralTheory.EtaleFoundations.SteenPf.leaf_aw := by
  apply LateralTheory.EtaleFoundations.AwPf.leaf_aw_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_steenrod_whitney_alexander_compatibility_of_components : LateralTheory.EtaleFoundations.SteenPf.leaf_wa := by
  apply LateralTheory.EtaleFoundations.SteenPf.leaf_wa_of <;> first | exact etale_steenrod_alexander_whitney_compatibility_of_components
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_steenrod_power_operation_properties_of_components : LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy := by
  apply LateralTheory.EtaleFoundations.etale_steenrod_prism_homotopy_of_acyclic_alexander_whitney <;> first | exact etale_steenrod_acyclic_models_of_components | exact etale_steenrod_alexander_whitney_compatibility_of_components | exact etale_steenrod_whitney_alexander_compatibility_of_components
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy := etale_steenrod_power_operation_properties_of_components
end LateralTheory.Fin.PrismAlexanderWhitneySwapChainHomotopy
