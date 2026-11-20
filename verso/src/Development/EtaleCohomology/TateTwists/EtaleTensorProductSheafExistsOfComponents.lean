import Development.EtaleCohomology.TateTwists.EtaleSheafTensorComplexExists
import Development.EtaleCohomology.TateTwists.EtaleTensorComplexExistsOfSheafTensorComplex

namespace LateralTheory.Fin.EtaleComplexTensorPairingExists
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_tensor_product_sheaf_exists_of_components : LateralTheory.EtaleFoundations.EtaleSheafTensorComplexExists := by
  apply LateralTheory.EtaleFoundations.etale_sheaf_tensor_complex_exists
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_tensor_product_exists_of_components : LateralTheory.EtaleFoundations.EtaleComplexTensorPairingExists := by
  apply LateralTheory.EtaleFoundations.etale_tensor_complex_exists_of_sheaf_tensor_complex <;> first | exact etale_tensor_product_sheaf_exists_of_components
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleComplexTensorPairingExists := etale_tensor_product_exists_of_components
end LateralTheory.Fin.EtaleComplexTensorPairingExists
