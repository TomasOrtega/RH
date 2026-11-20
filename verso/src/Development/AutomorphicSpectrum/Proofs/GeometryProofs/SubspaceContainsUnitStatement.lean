import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubspaceContainsUnit
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FSubspaceContainsUnit.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.subspace_contains_unit : ∀ (k : Type) [Field k] [IsAlgClosed k] (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R]
    (U : Submodule k R), (∀ x : R →ₐ[k] k, ∃ t ∈ U, x t ≠ 0) → ∃ w ∈ U, IsUnit w := by
  first | exact @GlobalTheory.CompanionTheory.FiniteAlgebraUnit.exists_isUnit_mem_of_forall_point | exact GlobalTheory.CompanionTheory.FiniteAlgebraUnit.exists_isUnit_mem_of_forall_point | (intros; apply GlobalTheory.CompanionTheory.FiniteAlgebraUnit.exists_isUnit_mem_of_forall_point <;> assumption)
