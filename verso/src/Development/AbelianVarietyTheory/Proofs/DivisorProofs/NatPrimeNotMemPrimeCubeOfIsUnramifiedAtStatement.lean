import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatPrimeNotMemPrimeCubeOfIsUnramifiedAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNatPrimeNotMemPrimeCubeOfIsUnramifiedAt.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.natPrime_not_mem_prime_cube_of_isUnramifiedAt : ∀ (p : ℕ) (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] (x : K) (P : Ideal (𝓞 H)) [P.IsPrime], p.Prime → Module.finrank ℚ K = 2 → x ^ 2 = -(p : K) → P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) P → (p : 𝓞 H) ∉ P ^ 3 := by
  first | exact @GlobalTheory.natPrime_not_mem_cube_of_isUnramifiedAt | exact GlobalTheory.natPrime_not_mem_cube_of_isUnramifiedAt | (intros; apply GlobalTheory.natPrime_not_mem_cube_of_isUnramifiedAt <;> assumption)
