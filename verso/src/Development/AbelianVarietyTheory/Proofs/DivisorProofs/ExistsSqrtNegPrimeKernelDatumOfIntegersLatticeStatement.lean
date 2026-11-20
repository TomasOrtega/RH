import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtNegPrimeKernelDatumOfIntegersLattice
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSqrtNegPrimeKernelDatumOfIntegersLattice.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.exists_sqrtNegPrimeKernelDatum_of_integersLattice : ∀ (p : ℕ) (L₀ : PeriodPair), p.Prime → p % 4 = 3 → 3 < p → IsIntegersLattice p L₀ → ∃ (L : PeriodPair) (t : ℂ), Datum p ℚ⟮(latticeCurve L₀).j⟯ L t ∧ (latticeCurve L).j = (latticeCurve L₀).j := by
  first | exact @GlobalTheory.CMModel.exists_datum_of_isIntegersLattice | exact GlobalTheory.CMModel.exists_datum_of_isIntegersLattice | (intros; apply GlobalTheory.CMModel.exists_datum_of_isIntegersLattice <;> assumption)
