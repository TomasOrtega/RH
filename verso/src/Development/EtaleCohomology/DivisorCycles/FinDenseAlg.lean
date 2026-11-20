import Development.EtaleCohomology.DivisorCycles.ChainPf
import Development.EtaleCohomology.DivisorCycles.SepPolyProof
import Development.EtaleCohomology.DivisorCycles.DenseAlg2

namespace LateralTheory.Fin.DenseAlg
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_frobenius_charpoly_separable : LateralTheory.DivDb.SepPoly := by
  apply LateralTheory.DivDb.SepPoly_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_rep_dense_algebraic_hull_holds_assembled : LateralTheory.DivDb.DenseAlg := by
  apply LateralTheory.DivDb.DenseAlg₂.DenseAlg_of <;> first | exact etale_divisibility_chain_of_key | exact etale_frobenius_charpoly_separable
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.DenseAlg := etale_rep_dense_algebraic_hull_holds_assembled
end LateralTheory.Fin.DenseAlg
