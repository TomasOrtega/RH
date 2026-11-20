import Development.EtaleCohomology.DivisorCycles.ChainPf
import Development.EtaleCohomology.DivisorCycles.SepPolyProof
import Development.EtaleCohomology.DivisorCycles.DenseAlg2

namespace LateralTheory.Fin.DenseAlg
/- English proof (translation)
Apply `LateralTheory.DivDb.Chain_of` to reduce the goal to its premises.
-/
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
/- English proof (translation)
Apply `LateralTheory.DivDb.SepPoly_of` to reduce the goal to its premises.
-/
theorem etale_frobenius_charpoly_separable : LateralTheory.DivDb.SepPoly := by
  apply LateralTheory.DivDb.SepPoly_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.DivDb.DenseAlg₂.DenseAlg_of <;> first | exact etale_divisibility_chain_of_key | exact etale_frobenius_charpoly_separable`.
-/
theorem etale_rep_dense_algebraic_hull_holds_assembled : LateralTheory.DivDb.DenseAlg := by
  apply LateralTheory.DivDb.DenseAlg₂.DenseAlg_of <;> first | exact etale_divisibility_chain_of_key | exact etale_frobenius_charpoly_separable
/- English proof (translation)
The claim follows from `etale_rep_dense_algebraic_hull_holds_assembled`.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.DenseAlg := etale_rep_dense_algebraic_hull_holds_assembled
end LateralTheory.Fin.DenseAlg
