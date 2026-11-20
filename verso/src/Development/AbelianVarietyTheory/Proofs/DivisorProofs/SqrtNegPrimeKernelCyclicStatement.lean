import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqrtNegPrimeKernelCyclic
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMModel.ker_sqrtNegNat_cyclic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSqrtNegPrimeKernelCyclic.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.sqrtNegPrime_kernel_cyclic : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → (∀ k : ℤ, (k : ℂ) * t ∈ L.lattice ↔ (p : ℤ) ∣ k) ∧ (∀ z, sqrtNegNat p * z ∈ L.lattice → ∃ k : ℕ, k < p ∧ z - (k : ℂ) * t ∈ L.lattice) ∧ IsKerReps L (sqrtNegNat p) ((Finset.Ico 1 p).image fun k : ℕ => (k : ℂ) * t) := by
  first | exact @GlobalTheory.CMModel.ker_sqrtNegNat_cyclic | exact GlobalTheory.CMModel.ker_sqrtNegNat_cyclic | (intros; apply GlobalTheory.CMModel.ker_sqrtNegNat_cyclic <;> assumption)
