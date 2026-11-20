import Development.EtaleCohomology.TateTwists.IsTensorFlip

namespace LateralTheory.Fin.EtaleComplexPairingFlipExists
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_cup_product_flip_exists_of_components : LateralTheory.EtaleFoundations.EtaleComplexPairingFlipExists := by
  apply LateralTheory.EtaleFoundations.etale_complex_pairing_flip_exists
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleComplexPairingFlipExists := etale_cup_product_flip_exists_of_components
end LateralTheory.Fin.EtaleComplexPairingFlipExists
