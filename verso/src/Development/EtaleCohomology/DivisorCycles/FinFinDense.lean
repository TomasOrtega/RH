import Development.EtaleCohomology.DivisorCycles.SepPolyProof
import Development.EtaleCohomology.DivisorCycles.ChainPf
import Development.EtaleCohomology.DivisorCycles.OpenCosetPf
import Development.EtaleCohomology.DivisorCycles.FinDensePf

namespace LateralTheory.Fin.FinDense
/- English proof (translation)
Apply `LateralTheory.DivDb.SepPoly_of` to reduce the goal to its premises.
-/
theorem etale_frobenius_charpoly_separable : LateralTheory.DivDb.SepPoly := by
  apply LateralTheory.DivDb.SepPoly_of
/- English proof (translation)
Apply `LateralTheory.DivDb.Chain_of` to reduce the goal to its premises.
-/
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.DivDb.OpenCoset_of <;> first | exact etale_divisibility_chain_of_key`.
-/
theorem etale_open_coset_condition_holds_assembled : LateralTheory.DivDb.OpenCoset := by
  apply LateralTheory.DivDb.OpenCoset_of <;> first | exact etale_divisibility_chain_of_key
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.DivDb.FinDense_of <;> first | exact etale_frobenius_charpoly_separable | exact etale_open_coset_condition_holds_assembled`.
-/
theorem etale_finite_image_dense_holds_assembled : LateralTheory.DivDb.FinDense := by
  apply LateralTheory.DivDb.FinDense_of <;> first | exact etale_frobenius_charpoly_separable | exact etale_open_coset_condition_holds_assembled
/- English proof (translation)
The claim follows from `etale_finite_image_dense_holds_assembled`.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinDense := etale_finite_image_dense_holds_assembled
end LateralTheory.Fin.FinDense
