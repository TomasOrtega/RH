import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFreeAtPrimesOfConstantRank
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FKernelFreeAtPrimesOfConstantRank.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.kernel_free_at_primes_of_constant_rank : ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] (d : Q →ₗ[R] P) (g : ℕ), Module.Finite R (LinearMap.ker d) → Module.Projective R (LinearMap.ker d) → (∀ p : PrimeSpectrum R, Module.rankAtStalk (LinearMap.ker d) p = g) → ∀ (p : Ideal R) [p.IsPrime], Module.Free (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧ Module.Finite (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧ Module.finrank (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) = g := by
  first | exact @GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free | exact GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free | (intros; apply GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free <;> assumption)
