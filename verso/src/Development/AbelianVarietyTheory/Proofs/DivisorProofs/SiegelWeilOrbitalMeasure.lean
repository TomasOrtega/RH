import Mathlib
open NumberField

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[← PadicAlgCl.norm_extends q (c : ℚ_[q]), map_ratCast]`.
-/
theorem padicAlgCl_norm_ratCast (q : ℕ) [Fact q.Prime] (c : ℚ) :
    ‖(c : PadicAlgCl q)‖ = ‖((c : ℚ) : ℚ_[q])‖ := by
  rw [← PadicAlgCl.norm_extends q (c : ℚ_[q]), map_ratCast]

/- English proof (translation)
Introduce `M _ _ q _ ι _ f hf a B hB τ`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.mpr hf)`. Establish `hgf : ∀ m, g (f m) = m` using `fun m => by`. Simplify using `using LinearMap.congr_fun hg m`. Establish `hsmul : ∀ (c : ℚ) (m : M), τ (c • m) = (c : PadicAlgCl q) * τ m`.

Introduce `c m`. Rewrite using `[Algebra.smul_def, map_mul]`. Use `congr 1`. Conclude with `eq_ratCast (τ.comp (algebraMap ℚ M)) c`. Use `set C : ℝ := ∑ i, ‖τ (g (Pi.single i 1))‖ with hC`.

Establish `hbound : ∀ k : ℕ, ‖τ a‖ ^ k ≤ B * C`. Introduce `k`. Rewrite using `[← norm_pow, ← map_pow, ← hgf (a ^ k)]`. Establish `hv : f (a ^ k) = ∑ i, f (a ^ k) i • (Pi.single i 1 : ι → ℚ)`. Use extensionality with `j`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hv, map_sum, map_sum, hC, Finset.mul_sum]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, hsmul, norm_mul, padicAlgCl_norm_ratCast]`. Conclude with `mul_le_mul_of_nonneg_right (hB k i) (norm_nonneg _)`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (B * C) h`. Conclude with `(lt_irrefl _ ((hbound k).trans_lt hk))`.
-/
theorem norm_conj_le_one_of_bounded_coords :
    ∀ (M : Type) [CommRing M] [Algebra ℚ M] (q : ℕ) [Fact q.Prime] (ι : Type) [Fintype ι]
      (f : M →ₗ[ℚ] (ι → ℚ)), Function.Injective f → ∀ (a : M) (B : ℝ),
      (∀ (k : ℕ) (i : ι), ‖((f (a ^ k) i : ℚ) : ℚ_[q])‖ ≤ B) →
      ∀ τ : M →+* PadicAlgCl q, ‖τ a‖ ≤ 1 := by
  intro M _ _ q _ ι _ f hf a B hB τ
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.mpr hf)
  have hgf : ∀ m, g (f m) = m := fun m => by
    simpa using LinearMap.congr_fun hg m
  have hsmul : ∀ (c : ℚ) (m : M), τ (c • m) = (c : PadicAlgCl q) * τ m := by
    intro c m
    rw [Algebra.smul_def, map_mul]
    congr 1
    exact eq_ratCast (τ.comp (algebraMap ℚ M)) c
  set C : ℝ := ∑ i, ‖τ (g (Pi.single i 1))‖ with hC
  have hbound : ∀ k : ℕ, ‖τ a‖ ^ k ≤ B * C := by
    intro k
    rw [← norm_pow, ← map_pow, ← hgf (a ^ k)]
    have hv : f (a ^ k) = ∑ i, f (a ^ k) i • (Pi.single i 1 : ι → ℚ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum, map_sum, hC, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_smul, hsmul, norm_mul, padicAlgCl_norm_ratCast]
    exact mul_le_mul_of_nonneg_right (hB k i) (norm_nonneg _)
  by_contra h
  push_neg at h
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (B * C) h
  exact (lt_irrefl _ ((hbound k).trans_lt hk))

end GlobalTheory
