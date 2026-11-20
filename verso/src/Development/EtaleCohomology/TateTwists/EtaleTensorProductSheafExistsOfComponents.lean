import Development.EtaleCohomology.TateTwists.EtaleSheafTensorComplexExists
import Development.EtaleCohomology.TateTwists.EtaleTensorComplexExistsOfSheafTensorComplex

namespace LateralTheory.Fin.EtaleComplexTensorPairingExists
/- English proof (translation)
Apply `LateralTheory.EtaleFoundations.etale_sheaf_tensor_complex_exists` to reduce the goal to its premises.
-/
theorem etale_tensor_product_sheaf_exists_of_components : LateralTheory.EtaleFoundations.EtaleSheafTensorComplexExists := by
  apply LateralTheory.EtaleFoundations.etale_sheaf_tensor_complex_exists
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.EtaleFoundations.etale_tensor_complex_exists_of_sheaf_tensor_complex <;> first | exact etale_tensor_product_sheaf_exists_of_components`.
-/
theorem etale_tensor_product_exists_of_components : LateralTheory.EtaleFoundations.EtaleComplexTensorPairingExists := by
  apply LateralTheory.EtaleFoundations.etale_tensor_complex_exists_of_sheaf_tensor_complex <;> first | exact etale_tensor_product_sheaf_exists_of_components
/- English proof (translation)
The claim follows from `etale_tensor_product_exists_of_components`.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleComplexTensorPairingExists := etale_tensor_product_exists_of_components
end LateralTheory.Fin.EtaleComplexTensorPairingExists
