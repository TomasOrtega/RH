import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPKerRepsPowFourMul
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMModel.prod_derivWeierstrassP_kerReps_pow_four_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProdDerivWeierstrassPKerRepsPowFourMul.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.prod_derivWeierstrassP_kerReps_pow_four_mul' : ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S → Even S.card → (∏ t ∈ S, L.derivWeierstrassP t) ^ 4 * α ^ 12 = (latticeCurve L).Δ ^ S.card := by
  first | exact @GlobalTheory.CMModel.prod_derivWeierstrassP_kerReps_pow_four_mul | exact GlobalTheory.CMModel.prod_derivWeierstrassP_kerReps_pow_four_mul | (intros; apply GlobalTheory.CMModel.prod_derivWeierstrassP_kerReps_pow_four_mul <;> assumption)
