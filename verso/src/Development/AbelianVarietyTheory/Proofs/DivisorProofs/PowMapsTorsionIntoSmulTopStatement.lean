import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMapsTorsionIntoSmulTop
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPowMapsTorsionIntoSmulTop.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_pow_apply_mem_smul_univ_of_torsion : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (M : Type) [AddCommGroup M] [Module R M] (I J : Ideal R) (f : M →ₗ[R] M) (m : ℕ), I.IsMaximal → J ≠ ⊥ → (∀ x, (f ^ m) x ∈ I • (⊤ : Submodule R M)) → ∃ j : ℕ, ∀ y : M, (∀ a ∈ I, a • y ∈ J • (⊤ : Submodule R M)) → (f ^ j) y ∈ J • (⊤ : Submodule R M) := by
  first | exact @GlobalTheory.pow_maps_torsion_into_smul_top | exact GlobalTheory.pow_maps_torsion_into_smul_top | (intros; apply GlobalTheory.pow_maps_torsion_into_smul_top <;> assumption)
