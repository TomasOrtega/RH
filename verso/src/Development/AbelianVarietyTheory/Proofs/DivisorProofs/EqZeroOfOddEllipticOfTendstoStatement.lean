import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfOddEllipticOfTendsto
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.eq_zero_of_odd_elliptic_of_tendsto` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEqZeroOfOddEllipticOfTendsto.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.eq_zero_of_odd_elliptic_of_tendsto' : ∀ (L : PeriodPair) (f : ℂ → ℂ), (∀ z, z ∉ L.lattice → DifferentiableAt ℂ f z) → (∀ z l, z ∉ L.lattice → l ∈ L.lattice → f (z + l) = f z) → (∀ z, z ∉ L.lattice → f (-z) = -f z) → Filter.Tendsto (fun z : ℂ => z ^ 3 * f z) (𝓝[≠] 0) (𝓝 0) → ∀ z, z ∉ L.lattice → f z = 0 := by
  first | exact @GlobalTheory.eq_zero_of_odd_elliptic_of_tendsto | exact GlobalTheory.eq_zero_of_odd_elliptic_of_tendsto | (intros; apply GlobalTheory.eq_zero_of_odd_elliptic_of_tendsto <;> assumption)
