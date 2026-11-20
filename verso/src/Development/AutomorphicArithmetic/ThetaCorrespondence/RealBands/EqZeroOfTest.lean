import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ _ F hF h y₀`. Assume the negation of the conclusion as `hy`. Take `⟨χ, hχc, hχ0, hχy⟩` from `exists_continuous_nonneg_pos y₀`. Establish `hχcont : Continuous (fun y => χ y)` using `χ.continuous`. Establish `hc1 : Continuous (fun y => (χ y : ℂ) * (starRingEnd ℂ) (F y))` using `(Complex.continuous_ofReal.comp hχcont).mul (Complex.continuous_conj.comp hF)`.

Establish `hs0 : HasCompactSupport (fun y => (χ y : ℂ))` using `hχc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)`. Establish `hs1 : HasCompactSupport (fun y => (χ y : ℂ) * (starRingEnd ℂ) (F y))` using `hs0.mul_right (f' := fun y => (starRingEnd ℂ) (F y))`. Establish `h1` using `h (fun z => (χ z⁻¹ : ℂ) * (starRingEnd ℂ) (F z⁻¹)) (hc1.comp continuous_inv) (hs1.comp_homeomorph (Homeomorph.inv G))`. Establish `h2 : ∀ y, (χ y⁻¹⁻¹ : ℂ) * (starRingEnd ℂ) (F y⁻¹⁻¹) * F y = ((χ y * ‖F y‖ ^ 2 : ℝ) : ℂ)`. Introduce `y`.

Rewrite using `[inv_inv, mul_assoc, Complex.conj_mul']`. Use `push_cast`. Both sides reduce to the same expression. Simplify using `only [h2] at h1`. Rewrite `h1` using `[integral_complex_ofReal, Complex.ofReal_eq_zero]`.

Establish `hc2 : Continuous (fun y => χ y * ‖F y‖ ^ 2)` using `hχcont.mul (hF.norm.pow 2)`. Establish `hs2 : HasCompactSupport (fun y => χ y * ‖F y‖ ^ 2)` using `hχc.mul_right (f' := fun y => ‖F y‖ ^ 2)`. Establish `hpos` using `hc2.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := y₀) hs2 (fun y => mul_nonneg (hχ0 y) (sq_nonneg _)) (mul_ne_zero hχy (pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)))`. Conclude with `hpos.ne' h1`.
-/
theorem UpperTheory.Lit.Cusp.eq_zero_of_test :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (F : G → ℂ), Continuous F →
      (∀ ψ : G → ℂ, Continuous ψ → HasCompactSupport ψ → ∫ y, ψ y⁻¹ * F y ∂μ = 0) → ∀ y, F y = 0 := by
  intro G _ _ _ _ _ _ _ _ μ _ F hF h y₀
  by_contra hy
  obtain ⟨χ, hχc, hχ0, hχy⟩ := exists_continuous_nonneg_pos y₀
  have hχcont : Continuous (fun y => χ y) := χ.continuous
  have hc1 : Continuous (fun y => (χ y : ℂ) * (starRingEnd ℂ) (F y)) :=
    (Complex.continuous_ofReal.comp hχcont).mul (Complex.continuous_conj.comp hF)
  have hs0 : HasCompactSupport (fun y => (χ y : ℂ)) :=
    hχc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hs1 : HasCompactSupport (fun y => (χ y : ℂ) * (starRingEnd ℂ) (F y)) :=
    hs0.mul_right (f' := fun y => (starRingEnd ℂ) (F y))
  have h1 := h (fun z => (χ z⁻¹ : ℂ) * (starRingEnd ℂ) (F z⁻¹)) (hc1.comp continuous_inv)
    (hs1.comp_homeomorph (Homeomorph.inv G))
  have h2 : ∀ y, (χ y⁻¹⁻¹ : ℂ) * (starRingEnd ℂ) (F y⁻¹⁻¹) * F y
      = ((χ y * ‖F y‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    rw [inv_inv, mul_assoc, Complex.conj_mul']
    push_cast
    rfl
  simp only [h2] at h1
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h1
  have hc2 : Continuous (fun y => χ y * ‖F y‖ ^ 2) := hχcont.mul (hF.norm.pow 2)
  have hs2 : HasCompactSupport (fun y => χ y * ‖F y‖ ^ 2) :=
    hχc.mul_right (f' := fun y => ‖F y‖ ^ 2)
  have hpos := hc2.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := y₀) hs2
    (fun y => mul_nonneg (hχ0 y) (sq_nonneg _))
    (mul_ne_zero hχy (pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)))
  exact hpos.ne' h1
