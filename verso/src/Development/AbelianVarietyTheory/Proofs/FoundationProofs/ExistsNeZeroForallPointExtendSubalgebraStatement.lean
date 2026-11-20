import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroForallPointExtendSubalgebra
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsNeZeroForallPointExtendSubalgebra.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_ne_zero_point_extends_to_subalgebra : ∀ (k A R : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [CommRing R] [IsDomain R] [Algebra k R] (ξ : A →ₐ[k] R), Function.Injective ξ → ∀ T : Finset R,
 ∃ (a : A) (S : Subalgebra k R) (hξ : ∀ u, ξ u ∈ S), a ≠ 0 ∧ (∀ t ∈ T, t ∈ S) ∧ ∀ φ : A →ₐ[k] k, φ a ≠ 0 → ∃ ψ : S →ₐ[k] k, ∀ u, ψ ⟨ξ u, hξ u⟩ = φ u := by
  first | exact @GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra | exact GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra | (intros; apply GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra <;> assumption)
