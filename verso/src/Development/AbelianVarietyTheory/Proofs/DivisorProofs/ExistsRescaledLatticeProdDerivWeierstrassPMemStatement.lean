import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledLatticeProdDerivWeierstrassPMem
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsRescaledLatticeProdDerivWeierstrassPMem.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.exists_rescaled_lattice_prodDerivWeierstrassP_mem : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∃ (L' : PeriodPair) (t' : ℂ), Datum p F L' t' ∧ (latticeCurve L').j = (latticeCurve L).j ∧ sqProd p L' t' ∈ F := by
  first | exact @GlobalTheory.CMModel.exists_datum_sqProd_mem | exact GlobalTheory.CMModel.exists_datum_sqProd_mem | (intros; apply GlobalTheory.CMModel.exists_datum_sqProd_mem <;> assumption)
