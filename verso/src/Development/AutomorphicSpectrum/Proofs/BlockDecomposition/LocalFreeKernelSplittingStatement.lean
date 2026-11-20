import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFreeKernelSplitting
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LocalSplit.exists_idempotent_of_residueField` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalFreeKernelSplitting.lean&line=94#L94)
-/
theorem _root_.GlobalTheory.T.local_free_kernel_splitting : ∀ (A Q P : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [AddCommGroup P] [Module A P] [Module.Finite A Q] [Module.Free A Q] [Module.Finite A P] [Module.Free A P] (d : Q →ₗ[A] P), ∃ r : P →ₗ[A] Q, (r ∘ₗ d ∘ₗ r ∘ₗ d = r ∘ₗ d) ∧ Module.Free A (LinearMap.ker (r ∘ₗ d)) ∧ Module.Finite A (LinearMap.ker (r ∘ₗ d)) ∧ Module.finrank A (LinearMap.ker (r ∘ₗ d)) = Module.finrank (IsLocalRing.ResidueField A) (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A))) := by
  first | exact @GlobalTheory.CompanionTheory.LocalSplit.exists_idempotent_of_residueField | exact GlobalTheory.CompanionTheory.LocalSplit.exists_idempotent_of_residueField | (intros; apply GlobalTheory.CompanionTheory.LocalSplit.exists_idempotent_of_residueField <;> assumption)
