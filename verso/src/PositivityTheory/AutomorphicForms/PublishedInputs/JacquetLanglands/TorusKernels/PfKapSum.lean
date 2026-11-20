import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

/- English proof (translation)
Introduce `hPack hMult hKap F I Gf _ _ _ D hD k hk c₀ hc₀`. Take `⟨C₁, hC₁⟩` from `hPack F I Gf D hD`. Take `⟨C₃, A₃, hK⟩` from `hKap I k hk`. Take `⟨C₂, hC₂⟩` from `hMult F I Gf D hD (1 / 16) c₀ (by norm_num) hc₀`. Use `⟨(C₁ : ℝ) * A₃ * max C₂ 0 * C₃, ?_⟩` and prove the remaining obligations.

Introduce `y s hs hy ω' z`. Take `⟨hfin, hcard⟩` from `hC₂ y s hs hy`. Take `⟨hmeas, hint, -, hnear⟩` from `hK z`. Establish `hpos : 0 ≤ 1 + D.HtY s y` using `by linarith`. Establish `key : ∀ n : ℕ, (n : ℝ) ≤ C₂ * (1 + D.HtY s y) → (n : ℝ≥0∞) ≤ ENNReal.ofReal (max C₂ 0 * (1 + D.HtY s y))`.

Introduce `n hn`. Rewrite using `[← ENNReal.ofReal_natCast]`. Conclude with `ENNReal.ofReal_le_ofReal (hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos))`. Establish `hA : ∀ w w' : D.Xs, Near (1 / 2) w w' → ENNReal.ofReal (Kap k z w) ≤ (A₃ : ℝ≥0∞) * ENNReal.ofReal (Kap k z w')`. Introduce `w w' hww`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]`. Establish `hpack` using `hC₁ y ω' (fun w => ENNReal.ofReal (Kap k z w)) A₃ (ENNReal.measurable_ofReal.comp hmeas) hA hfin`. Use `hpack.trans ((mul_le_mul' (mul_le_mul' le_rfl (key _ hcard)) hint).trans (le_of_eq ?_))` and prove the remaining obligations. Rewrite using `[show (C₁ : ℝ) * A₃ * max C₂ 0 * C₃ * (1 + D.HtY s y) = ((C₁ * A₃ * C₃ : ℝ≥0) : ℝ) * (max C₂ 0 * (1 + D.HtY s y)) by push_cast; ring, ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Esk.pf_KapSum : UpperTheory.Esk.Pack → UpperTheory.Esk.Mult → UpperTheory.Esk.KapInt → UpperTheory.Esk.KapSum := by
  intro hPack hMult hKap F I Gf _ _ _ D hD k hk c₀ hc₀
  obtain ⟨C₁, hC₁⟩ := hPack F I Gf D hD
  obtain ⟨C₃, A₃, hK⟩ := hKap I k hk
  obtain ⟨C₂, hC₂⟩ := hMult F I Gf D hD (1 / 16) c₀ (by norm_num) hc₀
  refine ⟨(C₁ : ℝ) * A₃ * max C₂ 0 * C₃, ?_⟩
  intro y s hs hy ω' z
  obtain ⟨hfin, hcard⟩ := hC₂ y s hs hy
  obtain ⟨hmeas, hint, -, hnear⟩ := hK z
  have hpos : 0 ≤ 1 + D.HtY s y := by linarith
  have key : ∀ n : ℕ, (n : ℝ) ≤ C₂ * (1 + D.HtY s y) →
      (n : ℝ≥0∞) ≤ ENNReal.ofReal (max C₂ 0 * (1 + D.HtY s y)) := by
    intro n hn
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos))
  have hA : ∀ w w' : D.Xs, Near (1 / 2) w w' →
      ENNReal.ofReal (Kap k z w) ≤ (A₃ : ℝ≥0∞) * ENNReal.ofReal (Kap k z w') := by
    intro w w' hww
    calc ENNReal.ofReal (Kap k z w) ≤ ENNReal.ofReal (A₃ * Kap k z w') :=
          ENNReal.ofReal_le_ofReal (hnear w w' hww).1
      _ = (A₃ : ℝ≥0∞) * ENNReal.ofReal (Kap k z w') := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  have hpack := hC₁ y ω' (fun w => ENNReal.ofReal (Kap k z w)) A₃
    (ENNReal.measurable_ofReal.comp hmeas) hA hfin
  refine hpack.trans ((mul_le_mul' (mul_le_mul' le_rfl (key _ hcard)) hint).trans (le_of_eq ?_))
  rw [show (C₁ : ℝ) * A₃ * max C₂ 0 * C₃ * (1 + D.HtY s y)
      = ((C₁ * A₃ * C₃ : ℝ≥0) : ℝ) * (max C₂ 0 * (1 + D.HtY s y)) by push_cast; ring,
    ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  push_cast
  ring
