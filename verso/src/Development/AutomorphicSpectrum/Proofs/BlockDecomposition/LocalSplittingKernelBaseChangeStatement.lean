import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSplittingKernelBaseChange
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalSplittingKernelBaseChange.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.local_splitting_kernel_base_change : ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] [Module.Finite R Q] [Module.Projective R Q] [Module.Finite R P] [Module.Projective R P] (d : Q →ₗ[R] P), (∀ (p : Ideal R) [p.IsMaximal], ∃ r : Localization.AtPrime p ⊗[R] P →ₗ[Localization.AtPrime p] Localization.AtPrime p ⊗[R] Q, d.baseChange (Localization.AtPrime p) ∘ₗ r ∘ₗ d.baseChange (Localization.AtPrime p) = d.baseChange (Localization.AtPrime p)) → ∃ r : P →ₗ[R] Q, d ∘ₗ r ∘ₗ d = d := by
  first | exact @GlobalTheory.CompanionTheory.RegularLocal.regular_of_regular_at_maximal | exact GlobalTheory.CompanionTheory.RegularLocal.regular_of_regular_at_maximal | (intros; apply GlobalTheory.CompanionTheory.RegularLocal.regular_of_regular_at_maximal <;> assumption)
