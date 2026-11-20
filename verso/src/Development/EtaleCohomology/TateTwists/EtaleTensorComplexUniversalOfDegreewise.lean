import Development.EtaleCohomology.TateTwists.EtaleTensorPairingDegreewiseUniversalOfSheafific
import Development.EtaleCohomology.TateTwists.EtaleTensorUniversalPropertyOfDegreewise

namespace LateralTheory.Fin.EtaleTensorPairUniversalProperty
/- English proof (translation)
Apply `LateralTheory.EtaleFoundations.etale_tensor_pairing_degreewise_universal_of_sheafification` to reduce the goal to its premises.
-/
theorem etale_tensor_complex_degreewise_universal : LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists := by
  apply LateralTheory.EtaleFoundations.etale_tensor_pairing_degreewise_universal_of_sheafification
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.EtaleFoundations.etale_tensor_universal_property_of_degreewise <;> first | exact etale_tensor_complex_degreewise_universal`.
-/
theorem etale_tensor_complex_universal_of_degreewise : LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty := by
  apply LateralTheory.EtaleFoundations.etale_tensor_universal_property_of_degreewise <;> first | exact etale_tensor_complex_degreewise_universal
/- English proof (translation)
The claim follows from `etale_tensor_complex_universal_of_degreewise`.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty := etale_tensor_complex_universal_of_degreewise
end LateralTheory.Fin.EtaleTensorPairUniversalProperty
