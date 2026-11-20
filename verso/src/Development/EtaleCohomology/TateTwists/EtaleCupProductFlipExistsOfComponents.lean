import Development.EtaleCohomology.TateTwists.IsTensorFlip

namespace LateralTheory.Fin.EtaleComplexPairingFlipExists
/- English proof (translation)
Apply `LateralTheory.EtaleFoundations.etale_complex_pairing_flip_exists` to reduce the goal to its premises.
-/
theorem etale_cup_product_flip_exists_of_components : LateralTheory.EtaleFoundations.EtaleComplexPairingFlipExists := by
  apply LateralTheory.EtaleFoundations.etale_complex_pairing_flip_exists
/- English proof (translation)
The claim follows from `etale_cup_product_flip_exists_of_components`.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleComplexPairingFlipExists := etale_cup_product_flip_exists_of_components
end LateralTheory.Fin.EtaleComplexPairingFlipExists
