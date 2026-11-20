import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem dualform : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z : mixedEmbedding.mixedSpace F, z ≠ 0 → ∃ u, ℓ (z * u) ≠ 0) →
    ∀ lam : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ, ∃ u : κ → mixedEmbedding.mixedSpace F,
      ∀ x, ℓ (∑ k, x k * u k) = lam x := by
  intro F _ _ κ _ ℓ hℓ lam
  set M := mixedEmbedding.mixedSpace F
  let Φ : (κ → M) →ₗ[ℝ] Module.Dual ℝ (κ → M) :=
    { toFun := fun u =>
        { toFun := fun x => ℓ (∑ k, x k * u k)
          map_add' := by intro x y; simp [add_mul, Finset.sum_add_distrib]
          map_smul' := by intro c x; simp [smul_mul_assoc, ← Finset.smul_sum] }
      map_add' := by
        intro u v; refine LinearMap.ext fun x => ?_
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c u; refine LinearMap.ext fun x => ?_
        simp [mul_smul_comm, ← Finset.smul_sum] }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    funext k
    by_contra hne
    obtain ⟨w, hw⟩ := hℓ (u k) hne
    apply hw
    have := LinearMap.congr_fun hu (Pi.single k w)
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] at this
    rw [Finset.sum_eq_single k] at this
    · simpa [mul_comm] using this
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hsurj : Function.Surjective Φ := by
    have : Module.finrank ℝ (κ → M) = Module.finrank ℝ (Module.Dual ℝ (κ → M)) :=
      (Subspace.dual_finrank_eq).symm
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank this).mp hinj
  obtain ⟨u, hu⟩ := hsurj lam
  exact ⟨u, fun x => by rw [← hu]; rfl⟩

end GlobalTheory
