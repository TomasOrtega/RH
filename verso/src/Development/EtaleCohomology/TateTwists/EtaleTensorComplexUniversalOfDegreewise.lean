import Development.EtaleCohomology.TateTwists.EtaleTensorPairingDegreewiseUniversalOfSheafific
import Development.EtaleCohomology.TateTwists.EtaleTensorUniversalPropertyOfDegreewise

namespace LateralTheory.Fin.EtaleTensorPairUniversalProperty
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_tensor_complex_degreewise_universal : LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists := by
  apply LateralTheory.EtaleFoundations.etale_tensor_pairing_degreewise_universal_of_sheafification
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_tensor_complex_universal_of_degreewise : LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty := by
  apply LateralTheory.EtaleFoundations.etale_tensor_universal_property_of_degreewise <;> first | exact etale_tensor_complex_degreewise_universal
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty := etale_tensor_complex_universal_of_degreewise
end LateralTheory.Fin.EtaleTensorPairUniversalProperty
