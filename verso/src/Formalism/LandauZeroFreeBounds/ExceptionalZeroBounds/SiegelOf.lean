import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelProductCharacterInequality

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Introduce `hP hR hB hL1 hZ hLP hS ε hε`. Take `⟨C, K, hK0, hKey⟩` from `hB`. Take `⟨CL, hL⟩` from `hL1`. Use `set σ₀ : ℝ := max (7 / 8) (1 - ε / (2 * (K + 1))) with hσ₀`. Establish `hK1 : 0 < K + 1` using `by linarith`.

Establish `h78 : 7 / 8 ≤ σ₀` using `le_max_left _ _`. Establish `hσ₀1 : σ₀ < 1`. Apply `max_lt (by norm_num)` to reduce the goal to its premises. Establish `: 0 < ε / (2 * (K + 1))` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hKa : ∀ σ : ℝ, σ₀ ≤ σ → σ < 1 → K * (1 - σ) ≤ ε / 2`. Introduce `σ hσ hσ1`. Establish `h1 : 1 - ε / (2 * (K + 1)) ≤ σ` using `le_trans (le_max_right _ _) hσ`. Establish `h2 : 1 - σ ≤ ε / (2 * (K + 1))` using `by linarith`. Establish `h3 : 0 ≤ 1 - σ` using `by linarith`.

Establish `h4 : (K + 1) * (ε / (2 * (K + 1))) = ε / 2`. Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation. Distinguish the cases in `hex : ∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁) (β : ℝ), χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ σ₀ ≤ β ∧ β < 1 ∧ DirichletCharacter.LFunction χ₁ β = 0`. Take `⟨q₁, hq₁, χ₁, β, h1sq, h1ne, hβ0, hβ1, hzero⟩` from `hex`.

Use `siegel_product_character_inequality hP hS hKey hL hε χ₁ h1sq h1ne (le_trans h78 hβ0) hβ1 (hKa β hβ0 hβ1) ?_` and prove the remaining obligations. Introduce `q _ χ ψ _ _ _ _`. Simplify using `[Fbq, hzero]`. Use `push_neg at hex`. Take `⟨q₁, hq₁, χ₁, h1sq, h1ne⟩` from `hR`.

Establish `hnz : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 → ∀ σ : ℝ, σ₀ ≤ σ → DirichletCharacter.LFunction χ σ ≠ 0`. Introduce `q _ χ hsq hne σ hσ`. Break down `lt_or_ge σ 1 with h | h` into its components or cases. Conclude with `hex q inferInstance χ σ hsq hne hσ h`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by simpa using h)`.

Establish `hpos : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 → (DirichletCharacter.LFunction χ σ₀).im = 0 ∧ 0 < (DirichletCharacter.LFunction χ σ₀).re`. Introduce `q _ χ hsq hne`. Conclude with `hLP q χ hsq hne σ₀ (hnz q χ hsq hne) σ₀ le_rfl`. Use `siegel_product_character_inequality hP hS hKey hL hε χ₁ h1sq h1ne h78 hσ₀1 (hKa σ₀ le_rfl hσ₀1) ?_` and prove the remaining obligations. Introduce `q _ χ ψ hsq hne hψne hψ`.

Establish `hψsq` using `product_real_characters_sq_eq_one χ₁ χ ψ h1sq hsq hψ`. Take `⟨hz_im, hz_re⟩` from `hZ σ₀ (by linarith) hσ₀1`. Take `⟨a_im, a_re⟩` from `hpos q₁ χ₁ h1sq h1ne`. Take `⟨b_im, b_re⟩` from `hpos q χ hsq hne`. Take `⟨c_im, c_re⟩` from `hpos (q₁ * q) ψ hψsq hψne`.

Establish `hre : (Fbq χ₁ χ ψ σ₀).re = (riemannZeta σ₀).re * (DirichletCharacter.LFunction χ₁ σ₀).re * (DirichletCharacter.LFunction χ σ₀).re * (DirichletCharacter.LFunction ψ σ₀).re`. Simplify using `[Fbq, Complex.mul_re, Complex.mul_im, hz_im, a_im, b_im, c_im]`. Rewrite using `[hre]`. Establish `hp` using `mul_pos (mul_pos a_re b_re) c_re`. Establish `hn` using `mul_neg_of_neg_of_pos hz_re hp`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem siegel_theorem_of : SiegelOf := by
  intro hP hR hB hL1 hZ hLP hS ε hε
  obtain ⟨C, K, hK0, hKey⟩ := hB
  obtain ⟨CL, hL⟩ := hL1
  set σ₀ : ℝ := max (7 / 8) (1 - ε / (2 * (K + 1))) with hσ₀
  have hK1 : 0 < K + 1 := by linarith
  have h78 : 7 / 8 ≤ σ₀ := le_max_left _ _
  have hσ₀1 : σ₀ < 1 := by
    apply max_lt (by norm_num)
    have : 0 < ε / (2 * (K + 1)) := by positivity
    linarith
  have hKa : ∀ σ : ℝ, σ₀ ≤ σ → σ < 1 → K * (1 - σ) ≤ ε / 2 := by
    intro σ hσ hσ1
    have h1 : 1 - ε / (2 * (K + 1)) ≤ σ := le_trans (le_max_right _ _) hσ
    have h2 : 1 - σ ≤ ε / (2 * (K + 1)) := by linarith
    have h3 : 0 ≤ 1 - σ := by linarith
    have h4 : (K + 1) * (ε / (2 * (K + 1))) = ε / 2 := by
      field_simp
    calc K * (1 - σ) ≤ (K + 1) * (1 - σ) := by nlinarith
      _ ≤ (K + 1) * (ε / (2 * (K + 1))) := mul_le_mul_of_nonneg_left h2 hK1.le
      _ = ε / 2 := h4
  by_cases hex : ∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁) (β : ℝ),
      χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ σ₀ ≤ β ∧ β < 1 ∧ DirichletCharacter.LFunction χ₁ β = 0
  ·
    obtain ⟨q₁, hq₁, χ₁, β, h1sq, h1ne, hβ0, hβ1, hzero⟩ := hex
    refine siegel_product_character_inequality hP hS hKey hL hε χ₁ h1sq h1ne (le_trans h78 hβ0) hβ1
      (hKa β hβ0 hβ1) ?_
    intro q _ χ ψ _ _ _ _
    simp [Fbq, hzero]
  ·
    push_neg at hex
    obtain ⟨q₁, hq₁, χ₁, h1sq, h1ne⟩ := hR
    have hnz : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 →
        ∀ σ : ℝ, σ₀ ≤ σ → DirichletCharacter.LFunction χ σ ≠ 0 := by
      intro q _ χ hsq hne σ hσ
      rcases lt_or_ge σ 1 with h | h
      · exact hex q inferInstance χ σ hsq hne hσ h
      · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by simpa using h)
    have hpos : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 →
        (DirichletCharacter.LFunction χ σ₀).im = 0 ∧ 0 < (DirichletCharacter.LFunction χ σ₀).re := by
      intro q _ χ hsq hne
      exact hLP q χ hsq hne σ₀ (hnz q χ hsq hne) σ₀ le_rfl
    refine siegel_product_character_inequality hP hS hKey hL hε χ₁ h1sq h1ne h78 hσ₀1 (hKa σ₀ le_rfl hσ₀1) ?_
    intro q _ χ ψ hsq hne hψne hψ
    have hψsq := product_real_characters_sq_eq_one χ₁ χ ψ h1sq hsq hψ
    obtain ⟨hz_im, hz_re⟩ := hZ σ₀ (by linarith) hσ₀1
    obtain ⟨a_im, a_re⟩ := hpos q₁ χ₁ h1sq h1ne
    obtain ⟨b_im, b_re⟩ := hpos q χ hsq hne
    obtain ⟨c_im, c_re⟩ := hpos (q₁ * q) ψ hψsq hψne
    have hre : (Fbq χ₁ χ ψ σ₀).re = (riemannZeta σ₀).re * (DirichletCharacter.LFunction χ₁ σ₀).re *
        (DirichletCharacter.LFunction χ σ₀).re * (DirichletCharacter.LFunction ψ σ₀).re := by
      simp [Fbq, Complex.mul_re, Complex.mul_im, hz_im, a_im, b_im, c_im]
    rw [hre]
    have hp := mul_pos (mul_pos a_re b_re) c_re
    have hn := mul_neg_of_neg_of_pos hz_re hp
    nlinarith

end Formalism.ZeroFreeDirichlet
