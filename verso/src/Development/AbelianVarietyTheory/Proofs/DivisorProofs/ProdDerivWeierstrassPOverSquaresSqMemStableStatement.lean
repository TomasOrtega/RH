import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresSqMemStable
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMModel.sqProd_sq_mem_and_stable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProdDerivWeierstrassPOverSquaresSqMemStable.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.prodDerivWeierstrassPOverSquares_sq_mem_stable : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ^ 2 ∈ F ∧ (sqProd p L t ∈ F → Stable L F (sqPt p t)) := by
  first | exact @GlobalTheory.CMModel.sqProd_sq_mem_and_stable | exact GlobalTheory.CMModel.sqProd_sq_mem_and_stable | (intros; apply GlobalTheory.CMModel.sqProd_sq_mem_and_stable <;> assumption)
