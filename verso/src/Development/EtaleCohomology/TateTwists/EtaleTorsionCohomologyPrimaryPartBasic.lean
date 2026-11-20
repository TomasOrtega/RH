import Development.EtaleCohomology.TateTwists.CyclotomicPrimitiveRootProductIdentitiesOfAdjoin

namespace LateralTheory.Fin.PrimitiveRootsOfUnityBasicIdentities
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_torsion_cohomology_primary_part_basic : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities := by
  apply LateralTheory.EtaleFoundations.PrimPf.cyclotomic_primitive_root_product_identities_of_adjoin_root
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities := etale_torsion_cohomology_primary_part_basic
end LateralTheory.Fin.PrimitiveRootsOfUnityBasicIdentities
