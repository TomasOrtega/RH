import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoCubeMulDerivWeierstrassPNegTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTendstoCubeMulDerivWeierstrassPNegTwo.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.tendsto_cube_mul_derivWeierstrassP_neg_two : ∀ (L : PeriodPair), Filter.Tendsto (fun z : ℂ => z ^ 3 * L.derivWeierstrassP z) (𝓝[≠] 0) (𝓝 (-2)) := by
  first | exact @GlobalTheory.CMModel.tendsto_cube_mul_derivWeierstrassP | exact GlobalTheory.CMModel.tendsto_cube_mul_derivWeierstrassP | (intros; apply GlobalTheory.CMModel.tendsto_cube_mul_derivWeierstrassP <;> assumption)
