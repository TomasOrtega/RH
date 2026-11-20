import Mathlib

open Filter Topology
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.SpecBound

/- English proof (translation)
Break down `subsingleton_or_nontrivial W with hW | hW` into its components or cases. Use `⟨0, fun j => ?_⟩` and prove the remaining obligations. Establish `h0 : T ^ j = 0`. Use extensionality with `x`. Conclude with `Subsingleton.elim _ _`.

Simplify using `[h0]`. Establish `: CompleteSpace W` using `FiniteDimensional.complete ℂ W`. Establish `: Nontrivial (W →L[ℂ] W)` using `(Module.End.toContinuousLinearMap (𝕜 := ℂ) W).injective.nontrivial`. Take `⟨z, hz, hzr⟩` from `spectrum.exists_nnnorm_eq_spectralRadius T`. Establish `hzE : Module.End.HasEigenvalue (T : Module.End ℂ W) z`.

Rewrite using `[Module.End.hasEigenvalue_iff_mem_spectrum]`. Establish `hT : (Module.End.toContinuousLinearMap (𝕜` using `ℂ) W) (T : Module.End ℂ W) = T := by`. Use extensionality with `x`. Both sides reduce to the same expression. Rewrite using `[← AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap (𝕜 := ℂ) W), hT]`.

Conclude with `hz`. Establish `hlt : ‖z‖ < ρ` using `h z hzE`. Establish `hρ : 0 < ρ` using `(norm_nonneg z).trans_lt hlt`. Set `ρ' : ℝ≥0` to `⟨ρ, hρ.le⟩`. Establish `hr : spectralRadius ℂ T < (ρ' : ℝ≥0∞)`.

Rewrite using `[← hzr]`. Establish `: ‖z‖₊ < ρ'`. Rewrite using `[← NNReal.coe_lt_coe]`. Conclude with `hlt`. Conclude with `this` after adjusting the coercions.

Establish `hev` using `(spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius T).eventually_lt_const hr`. Take `⟨N, hN⟩` from `eventually_atTop.1 (hev.and (eventually_gt_atTop 0))`. Establish `key : ∀ n, N ≤ n → ‖T ^ n‖ ≤ ρ ^ n`. Introduce `n hn`. Take `⟨h1, h0⟩` from `hN n hn`.

Establish `hn0 : (n : ℝ) ≠ 0` using `by exact_mod_cast h0.ne'`. Establish `h2 : (‖T ^ n‖₊ : ℝ≥0∞) ≤ (ρ' : ℝ≥0∞) ^ n`. Establish `h3` using `ENNReal.rpow_le_rpow h1.le (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))`. Rewrite `h3` using `[← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hn0, ENNReal.rpow_one, ENNReal.rpow_natCast]`. Conclude with `h3`.

Establish `h4 : ‖T ^ n‖₊ ≤ ρ' ^ n` using `by exact_mod_cast h2`. Establish `h5 : ((‖T ^ n‖₊ : ℝ≥0) : ℝ) ≤ ((ρ' ^ n : ℝ≥0) : ℝ)` using `NNReal.coe_le_coe.2 h4`. Rewrite `h5` using `[NNReal.coe_pow, coe_nnnorm]`. Conclude with `h5`. Use `⟨1 + ∑ i ∈ Finset.range N, ‖T ^ i‖ / ρ ^ i, fun j => ?_⟩` and prove the remaining obligations.

Establish `hpow : 0 < ρ ^ j` using `pow_pos hρ j`. Establish `hsum : 0 ≤ ∑ i ∈ Finset.range N, ‖T ^ i‖ / ρ ^ i` using `Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) (pow_pos hρ i).le`. Distinguish the cases in `hj : j < N`. Establish `h6 : ‖T ^ j‖ / ρ ^ j ≤ ∑ i ∈ Finset.range N, ‖T ^ i‖ / ρ ^ i` using `Finset.single_le_sum (f := fun i => ‖T ^ i‖ / ρ ^ i) (fun i _ => div_nonneg (norm_nonneg _) (pow_pos hρ i).le) (Finset.mem_range.2 hj)`. Establish `h7 : ‖T ^ j‖ / ρ ^ j ≤ 1 + ∑ i ∈ Finset.range N, ‖T ^ i‖ / ρ ^ i` using `by linarith`.

Conclude with `(div_le_iff₀ hpow).1 h7`. Establish `h8` using `key j (not_lt.1 hj)`. Use polynomial arithmetic with `[mul_nonneg hsum hpow.le]`.
-/
theorem norm_pow_le_of_eigenvalues_lt (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (T : W →L[ℂ] W) (ρ : ℝ)
    (h : ∀ μ : ℂ, Module.End.HasEigenvalue (T : Module.End ℂ W) μ → ‖μ‖ < ρ) :
    ∃ C : ℝ, ∀ j : ℕ, ‖T ^ j‖ ≤ C * ρ ^ j := by
  rcases subsingleton_or_nontrivial W with hW | hW
  · refine ⟨0, fun j => ?_⟩
    have h0 : T ^ j = 0 := by
      ext x
      exact Subsingleton.elim _ _
    simp [h0]
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have : Nontrivial (W →L[ℂ] W) :=
    (Module.End.toContinuousLinearMap (𝕜 := ℂ) W).injective.nontrivial
  obtain ⟨z, hz, hzr⟩ := spectrum.exists_nnnorm_eq_spectralRadius T
  have hzE : Module.End.HasEigenvalue (T : Module.End ℂ W) z := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum]
    have hT : (Module.End.toContinuousLinearMap (𝕜 := ℂ) W) (T : Module.End ℂ W) = T := by
      ext x
      rfl
    rw [← AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap (𝕜 := ℂ) W), hT]
    exact hz
  have hlt : ‖z‖ < ρ := h z hzE
  have hρ : 0 < ρ := (norm_nonneg z).trans_lt hlt
  let ρ' : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hr : spectralRadius ℂ T < (ρ' : ℝ≥0∞) := by
    rw [← hzr]
    have : ‖z‖₊ < ρ' := by
      rw [← NNReal.coe_lt_coe]
      exact hlt
    exact_mod_cast this
  have hev := (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius T).eventually_lt_const hr
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and (eventually_gt_atTop 0))
  have key : ∀ n, N ≤ n → ‖T ^ n‖ ≤ ρ ^ n := by
    intro n hn
    obtain ⟨h1, h0⟩ := hN n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
    have h2 : (‖T ^ n‖₊ : ℝ≥0∞) ≤ (ρ' : ℝ≥0∞) ^ n := by
      have h3 := ENNReal.rpow_le_rpow h1.le (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hn0, ENNReal.rpow_one,
        ENNReal.rpow_natCast] at h3
      exact h3
    have h4 : ‖T ^ n‖₊ ≤ ρ' ^ n := by exact_mod_cast h2
    have h5 : ((‖T ^ n‖₊ : ℝ≥0) : ℝ) ≤ ((ρ' ^ n : ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 h4
    rw [NNReal.coe_pow, coe_nnnorm] at h5
    exact h5
  refine ⟨1 + ∑ i ∈ Finset.range N, ‖T ^ i‖ / ρ ^ i, fun j => ?_⟩
  have hpow : 0 < ρ ^ j := pow_pos hρ j
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, ‖T ^ i‖ / ρ ^ i :=
    Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) (pow_pos hρ i).le
  by_cases hj : j < N
  · have h6 : ‖T ^ j‖ / ρ ^ j ≤ ∑ i ∈ Finset.range N, ‖T ^ i‖ / ρ ^ i :=
      Finset.single_le_sum (f := fun i => ‖T ^ i‖ / ρ ^ i)
        (fun i _ => div_nonneg (norm_nonneg _) (pow_pos hρ i).le) (Finset.mem_range.2 hj)
    have h7 : ‖T ^ j‖ / ρ ^ j ≤ 1 + ∑ i ∈ Finset.range N, ‖T ^ i‖ / ρ ^ i := by linarith
    exact (div_le_iff₀ hpow).1 h7
  · have h8 := key j (not_lt.1 hj)
    nlinarith [mul_nonneg hsum hpow.le]

end GlobalTheory.CompanionTheory.SpecBound
