import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.CoeffScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.FinMH
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.MemHomogeneousExponentsOneBlock

open Polynomial UpperTheory.V.Z.Sym.Wt

/- English proof (translation)
Introduce `K _ d n g`. Rewrite using `[trace_blocks n (sbs g).toLinearMap (mRep d n g) (fun P => rfl)]`. Simplify using `only [AlgHom.toLinearMap_apply]`. Repeatedly rewrite using `[coeff_sbs_glue, symPowTrace_eq_sum_coeff]`. Rewrite using `[Finset.prod_univ_sum]`.
-/
theorem UpperTheory.V.Z.Sym.Wt.trProd :
    UpperTheory.V.Z.Sym.Wt.TrProd := by
  classical
  intro K _ d n g
  rw [trace_blocks n (sbs g).toLinearMap (mRep d n g) (fun P => rfl)]
  simp only [AlgHom.toLinearMap_apply]
  simp_rw [coeff_sbs_glue, symPowTrace_eq_sum_coeff]
  rw [Finset.prod_univ_sum]
