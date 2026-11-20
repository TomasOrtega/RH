import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `C _ σ τ _ _ P f F F' h0 hk hF`. Establish `hs : MvPowerSeries.HasSubst f` using `MvPowerSeries.hasSubst_of_constantCoeff_zero h0`. Use extensionality with `ν`. Rewrite using `[MvPowerSeries.coeff_subst hs, MvPowerSeries.coeff_subst hs]`. Use `finsum_congr fun μ => ?_` and prove the remaining obligations.

Distinguish the cases in `h : ∀ w ∈ μ.support, P w`. Rewrite using `[hF μ h]`. Use `push Not at h`. Take `⟨w, hw, hP⟩` from `h`. Establish `hz : (μ.prod fun s e => f s ^ e) = 0`.

Use `Finset.prod_eq_zero hw ?_` and prove the remaining obligations. Use `show f w ^ μ w = 0`. Rewrite using `[hk w hP]`. Conclude with `zero_pow (Finsupp.mem_support_iff.mp hw)`. Rewrite using `[hz]`.

Simplify using the standard rewrite rules.
-/
theorem subst_eq_of_coeff_eq_of_killed :
    ∀ (C : Type) [Field C] (σ τ : Type) [Fintype σ] [Fintype τ] (P : σ → Prop) (f : σ → MvPowerSeries τ C) (F F' : MvPowerSeries σ C), (∀ w, MvPowerSeries.constantCoeff (f w) = 0) → (∀ w, ¬ P w → f w = 0) → (∀ μ : σ →₀ ℕ, (∀ w ∈ μ.support, P w) → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ F') → MvPowerSeries.subst f F = MvPowerSeries.subst f F' := by
  intro C _ σ τ _ _ P f F F' h0 hk hF
  have hs : MvPowerSeries.HasSubst f := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  ext ν
  rw [MvPowerSeries.coeff_subst hs, MvPowerSeries.coeff_subst hs]
  refine finsum_congr fun μ => ?_
  by_cases h : ∀ w ∈ μ.support, P w
  · rw [hF μ h]
  · push Not at h
    obtain ⟨w, hw, hP⟩ := h
    have hz : (μ.prod fun s e => f s ^ e) = 0 := by
      refine Finset.prod_eq_zero hw ?_
      show f w ^ μ w = 0
      rw [hk w hP]
      exact zero_pow (Finsupp.mem_support_iff.mp hw)
    rw [hz]
    simp

end GlobalTheory
