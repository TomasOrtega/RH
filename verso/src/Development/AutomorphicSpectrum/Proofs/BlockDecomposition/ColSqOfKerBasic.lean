import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelColumn

/- English proof (translation)
Introduce `hK X φ B Ω hT hB hΩ hS y`. Use `letI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩`. Use `haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩`. Establish `hker` using `(hK X φ hT).2.2.2.2.2`. Establish `hBe : ∀ z, ‖φ z‖ₑ ≤ ENNReal.ofReal B` using `fun z => by`.

Rewrite using `[← ofReal_norm]`. Conclude with `ENNReal.ofReal_le_ofReal (hB z)`. Set `A : X.G → ℝ≥0∞` to `fun x => ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ`. Establish `hterm : ∀ γ : X.Γ, Measurable fun x : X.G => ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ` using `fun γ => (hT.1.comp (by fun_prop)).enorm.measurable`. Establish `hAm : Measurable A` using `Measurable.ennreal_tsum hterm`.

Establish `hAinv : ∀ (δ : X.Γ) (x : X.G), A ((δ : X.G) * x) = A x`. Introduce `δ x`. Simplify using `only [A]`. Rewrite using `[← (Equiv.mulLeft δ).tsum_eq (fun γ : X.Γ => ‖φ (((δ : X.G) * x)⁻¹ * (γ : X.G) * y)‖ₑ)]`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations.

Simplify using `[mul_assoc]`. Set `g : X.G → ℝ≥0∞` to `fun x => ‖φ (x⁻¹ * y)‖ₑ * A x`. Establish `hgm : Measurable g` using `((hT.1.comp (by fun_prop : Continuous fun x : X.G => x⁻¹ * y)).enorm.measurable).mul hAm`. Establish `hsq : ∀ x, A x ^ 2 = ∑' γ : X.Γ, g (γ⁻¹ • x)`. Introduce `x`.

Rewrite using `[sq]`. Combine the equalities or inequalities in the displayed calculation. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Establish `e : γ⁻¹ • x = ((γ⁻¹ : X.Γ) : X.G) * x` using `rfl`. Simplify using `only [g]`.

Rewrite using `[e, hAinv]`. Simplify using `[mul_assoc]`. Set `c : ℝ≥0∞` to `ENNReal.ofReal B * (ENNReal.ofReal B * cnt X.Γ (Ω⁻¹ * Ω) y)`. Establish `hg : ∀ x, g x ≤ (y • Ω⁻¹).indicator (fun _ => c) x`. Introduce `x`.

Distinguish the cases in `h0 : φ (x⁻¹ * y) = 0`. Simplify using `[g, h0]`. Establish `hω : x⁻¹ * y ∈ Ω` using `hS h0`. Establish `hx : x ∈ y • Ω⁻¹`. Rewrite using `[Set.mem_smul_set]`.

Conclude with `⟨y⁻¹ * x, by simpa [Set.mem_inv] using hω, by simp⟩`. Rewrite using `[Set.indicator_of_mem hx]`. Establish `h2 : A x ≤ ENNReal.ofReal B * cnt X.Γ (Ω⁻¹ * Ω) y`. Simplify using `only [A, cnt]`. Rewrite using `[← ENNReal.tsum_mul_left]`.

Use `ENNReal.tsum_le_tsum fun γ => ?_` and prove the remaining obligations. Distinguish the cases in `h3 : φ (x⁻¹ * (γ : X.G) * y) = 0`. Simplify using `[h3]`. Establish `hm : y⁻¹ * (γ : X.G) * y ∈ Ω⁻¹ * Ω` using `Set.mem_mul.2 ⟨(x⁻¹ * y)⁻¹, Set.inv_mem_inv.2 hω, x⁻¹ * (γ : X.G) * y, hS h3, by group⟩`. Rewrite using `[Set.indicator_of_mem hm]`.

Simplify using `using hBe _`. Conclude with `mul_le_mul' (hBe _) h2`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hsq]`. Both sides reduce to the same expression.

Use `_ = ∑' γ : X.Γ, ∫⁻ x in X.F, g (γ⁻¹ • x) ∂X.μ := lintegral_tsum fun γ => (hgm.comp (measurable_const_mul ((γ⁻¹ : X.Γ) : X.G))).aemeasurable`. Use `_ = ∫⁻ x, g x ∂X.μ := (X.fd.lintegral_eq_tsum' g).symm`. Use `_ ≤ ∫⁻ x, (y • Ω⁻¹).indicator (fun _ => c) x ∂X.μ := lintegral_mono hg`. Use `_ ≤ c * X.μ (y • Ω⁻¹) := lintegral_indicator_const_le _ _`. Use `_ = ENNReal.ofReal B ^ 2 * X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y := by`.

Rewrite using `[measure_smul]`. Simplify using `only [c]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem colSq_of_kerBasic : KerBasic → ColSq := by
  intro hK X φ B Ω hT hB hΩ hS y
  letI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have hker := (hK X φ hT).2.2.2.2.2
  have hBe : ∀ z, ‖φ z‖ₑ ≤ ENNReal.ofReal B := fun z => by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hB z)
  let A : X.G → ℝ≥0∞ := fun x => ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ
  have hterm : ∀ γ : X.Γ, Measurable fun x : X.G => ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ := fun γ =>
    (hT.1.comp (by fun_prop)).enorm.measurable
  have hAm : Measurable A := Measurable.ennreal_tsum hterm
  have hAinv : ∀ (δ : X.Γ) (x : X.G), A ((δ : X.G) * x) = A x := by
    intro δ x
    simp only [A]
    rw [← (Equiv.mulLeft δ).tsum_eq (fun γ : X.Γ => ‖φ (((δ : X.G) * x)⁻¹ * (γ : X.G) * y)‖ₑ)]
    refine tsum_congr fun γ => ?_
    simp [mul_assoc]
  let g : X.G → ℝ≥0∞ := fun x => ‖φ (x⁻¹ * y)‖ₑ * A x
  have hgm : Measurable g :=
    ((hT.1.comp (by fun_prop : Continuous fun x : X.G => x⁻¹ * y)).enorm.measurable).mul hAm
  have hsq : ∀ x, A x ^ 2 = ∑' γ : X.Γ, g (γ⁻¹ • x) := by
    intro x
    rw [sq]
    calc A x * A x = (∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ) * A x := rfl
      _ = ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ * A x := ENNReal.tsum_mul_right.symm
      _ = ∑' γ : X.Γ, g (γ⁻¹ • x) := by
        refine tsum_congr fun γ => ?_
        have e : γ⁻¹ • x = ((γ⁻¹ : X.Γ) : X.G) * x := rfl
        simp only [g]
        rw [e, hAinv]
        simp [mul_assoc]
  let c : ℝ≥0∞ := ENNReal.ofReal B * (ENNReal.ofReal B * cnt X.Γ (Ω⁻¹ * Ω) y)
  have hg : ∀ x, g x ≤ (y • Ω⁻¹).indicator (fun _ => c) x := by
    intro x
    by_cases h0 : φ (x⁻¹ * y) = 0
    · simp [g, h0]
    · have hω : x⁻¹ * y ∈ Ω := hS h0
      have hx : x ∈ y • Ω⁻¹ := by
        rw [Set.mem_smul_set]
        exact ⟨y⁻¹ * x, by simpa [Set.mem_inv] using hω, by simp⟩
      rw [Set.indicator_of_mem hx]
      have h2 : A x ≤ ENNReal.ofReal B * cnt X.Γ (Ω⁻¹ * Ω) y := by
        simp only [A, cnt]
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun γ => ?_
        by_cases h3 : φ (x⁻¹ * (γ : X.G) * y) = 0
        · simp [h3]
        · have hm : y⁻¹ * (γ : X.G) * y ∈ Ω⁻¹ * Ω :=
            Set.mem_mul.2 ⟨(x⁻¹ * y)⁻¹, Set.inv_mem_inv.2 hω, x⁻¹ * (γ : X.G) * y, hS h3, by group⟩
          rw [Set.indicator_of_mem hm]
          simpa using hBe _
      exact mul_le_mul' (hBe _) h2
  calc ∫⁻ x, ‖ker X.Γ φ x y‖ₑ ^ 2 ∂X.ν ≤ ∫⁻ x, A x ^ 2 ∂X.ν :=
        lintegral_mono fun x => pow_le_pow_left' (hker x y) 2
    _ = ∫⁻ x in X.F, ∑' γ : X.Γ, g (γ⁻¹ • x) ∂X.μ := by
        simp only [hsq]; rfl
    _ = ∑' γ : X.Γ, ∫⁻ x in X.F, g (γ⁻¹ • x) ∂X.μ :=
        lintegral_tsum fun γ => (hgm.comp (measurable_const_mul ((γ⁻¹ : X.Γ) : X.G))).aemeasurable
    _ = ∫⁻ x, g x ∂X.μ := (X.fd.lintegral_eq_tsum' g).symm
    _ ≤ ∫⁻ x, (y • Ω⁻¹).indicator (fun _ => c) x ∂X.μ := lintegral_mono hg
    _ ≤ c * X.μ (y • Ω⁻¹) := lintegral_indicator_const_le _ _
    _ = ENNReal.ofReal B ^ 2 * X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y := by
        rw [measure_smul]
        simp only [c]
        ring

end GlobalTheory.CompanionTheory.KernelColumn
