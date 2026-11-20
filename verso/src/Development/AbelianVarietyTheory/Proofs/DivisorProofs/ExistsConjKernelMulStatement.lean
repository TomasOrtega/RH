import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjKernelMul
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMModel.exists_conj_kernel_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsConjKernelMul.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_conj_kernel_mul' : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → ∃ c : ℕ, ¬ p ∣ c ∧ ∀ k : ℕ, GlobalTheory.ConjPoint.IsConj L L σ ((k : ℂ) * t) ((k : ℂ) * ((c : ℂ) * t)) := by
  first | exact @GlobalTheory.CMModel.exists_conj_kernel_mul | exact GlobalTheory.CMModel.exists_conj_kernel_mul | (intros; apply GlobalTheory.CMModel.exists_conj_kernel_mul <;> assumption)
