import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ κ _ ℓ hℓ lam`. Use `set M := mixedEmbedding.mixedSpace F`. Set `Φ : (κ → M) →ₗ[ℝ] Module.Dual ℝ (κ → M)` to `{ toFun := fun u => { toFun := fun x => ℓ (∑ k, x k * u k) map_add' := by intro x y; simp [add_mul, Finset.sum_add_distrib] map_smul' := by intro c x; simp [smul_mul_assoc, ← Finset.smul_sum] } map_add' := by`. Introduce `u v`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Simplify using `[mul_add, Finset.sum_add_distrib]`. Use the proof step `map_smul' := by`. Introduce `c u`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Simplify using `[mul_smul_comm, ← Finset.smul_sum] }`.

Establish `hinj : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `u hu`. Use function extensionality and compare the values at `k`. Assume the negation of the conclusion as `hne`.

Take `⟨w, hw⟩` from `hℓ (u k) hne`. Apply `hw` to reduce the goal to its premises. Use `LinearMap.congr_fun hu (Pi.single k w)` as an intermediate fact. Simplify using `only [Φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] at this`. Rewrite `this` using `[Finset.sum_eq_single k]`.

Simplify `this` using `[mul_comm]`. Introduce `b _ hb`. Simplify using `[Pi.single_apply, hb]`. Simplify using the standard rewrite rules. Establish `hsurj : Function.Surjective Φ`.

Establish `: Module.finrank ℝ (κ → M) = Module.finrank ℝ (Module.Dual ℝ (κ → M))` using `(Subspace.dual_finrank_eq).symm`. Conclude with `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank this).mp hinj`. Take `⟨u, hu⟩` from `hsurj lam`. Conclude with `⟨u, fun x => by rw [← hu]; rfl⟩`.
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
