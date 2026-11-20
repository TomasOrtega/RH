import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdKernelMultiplierTranslateNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProdKernelMultiplierTranslateNeg.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.prod_kernel_multiplier_translate_neg : ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ) (φ : ℂ → ℂ), IsKerReps L α S → MulStable L α → (∀ z l, l ∈ L.lattice → φ (z + l) = φ z) → (∀ z s, α * s ∈ L.lattice → φ (z + s) * ∏ t ∈ S, φ (z + s + t) = φ z * ∏ t ∈ S, φ (z + t)) ∧ ∀ z, ∏ t ∈ S, φ (z - t) = ∏ t ∈ S, φ (z + t) := by
  first | exact @GlobalTheory.KerPerm.prod_ker_translate_neg | exact GlobalTheory.KerPerm.prod_ker_translate_neg | (intros; apply GlobalTheory.KerPerm.prod_ker_translate_neg <;> assumption)
