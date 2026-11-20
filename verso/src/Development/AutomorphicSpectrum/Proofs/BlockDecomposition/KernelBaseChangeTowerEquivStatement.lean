import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelBaseChangeTowerEquiv
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FKernelBaseChangeTowerEquiv.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.kernel_base_change_tower_equiv : ∀ (R A K Q P : Type) [CommRing R] [CommRing A] [CommRing K] [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] (d : Q →ₗ[R] P), Nonempty (LinearMap.ker ((d.baseChange A).baseChange K) ≃ₗ[K] LinearMap.ker (d.baseChange K)) := by
  first | exact @GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_baseChange_tower | exact GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_baseChange_tower | (intros; apply GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_baseChange_tower <;> assumption)
