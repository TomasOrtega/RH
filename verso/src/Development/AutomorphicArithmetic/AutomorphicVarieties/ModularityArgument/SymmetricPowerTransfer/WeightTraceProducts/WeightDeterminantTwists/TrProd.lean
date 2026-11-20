import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.CoeffScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.FinMH
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.MemHomogeneousExponentsOneBlock

open Polynomial UpperTheory.V.Z.Sym.Wt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.V.Z.Sym.Wt.trProd :
    UpperTheory.V.Z.Sym.Wt.TrProd := by
  classical
  intro K _ d n g
  rw [trace_blocks n (sbs g).toLinearMap (mRep d n g) (fun P => rfl)]
  simp only [AlgHom.toLinearMap_apply]
  simp_rw [coeff_sbs_glue, symPowTrace_eq_sum_coeff]
  rw [Finset.prod_univ_sum]
