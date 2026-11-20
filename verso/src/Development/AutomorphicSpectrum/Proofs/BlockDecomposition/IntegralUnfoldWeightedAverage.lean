import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan

/- English proof (translation)
Take `⟨K, hK⟩ : ∃ K : G → ℂ, K = fun g => F g * ((ρ g).toReal : ℂ)` from `⟨_, rfl⟩`. Establish `hKm : Measurable K`. Rewrite using `[hK]`. Conclude with `hF.mul (Complex.measurable_ofReal.comp hρ.ennreal_toReal)`. Rewrite using `[show (∫ g, F g * ((ρ g).toReal : ℂ) ∂μ) = ∫ g, K g ∂μ by rw [hK]]`.

Distinguish the cases in `hKi : Integrable K μ`. Use `swap`. Conclude with `integral_undef hKi`. Take `⟨wT, hwT⟩ : ∃ wT : G → ℝ, wT = fun g => (w g).toReal` from `⟨_, rfl⟩`. Establish `hwTm : Measurable wT` using `by rw [hwT]; exact hw.ennreal_toReal`.

Establish `hs : Measurable (fun p : H × G => (u p.1)⁻¹ * p.2)` using `(hu.comp measurable_fst).inv.mul measurable_snd`. Establish `hone : ∀ g, ∫ h, wT ((u h)⁻¹ * g) ∂ν = 1`. Introduce `g`. Establish `hm : Measurable fun h => w ((u h)⁻¹ * g)` using `hw.comp (hu.inv.mul_const g)`. Establish `hfin : ∀ᵐ h ∂ν, w ((u h)⁻¹ * g) < ⊤` using `ae_lt_top hm (by rw [hw1]; simp)`.

Rewrite using `[hwT]`. Simplify using `only []`. Rewrite using `[integral_toReal hm.aemeasurable hfin, hw1]`. Simplify using the standard rewrite rules. Take `⟨φ, hφ⟩ : ∃ φ : H × G → ℂ, φ = fun p => K p.2 * (wT ((u p.1)⁻¹ * p.2) : ℂ)` from `⟨_, rfl⟩`.

Establish `hφm : Measurable φ`. Rewrite using `[hφ]`. Conclude with `(hKm.comp measurable_snd).mul (Complex.measurable_ofReal.comp (hwTm.comp hs))`. Establish `hφi : Integrable φ (ν.prod μ)`. Use `⟨hφm.aestronglyMeasurable, ?_⟩` and prove the remaining obligations.

Rewrite using `[hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hφm.enorm.aemeasurable]`. Use `lt_of_le_of_lt (lintegral_mono (g := fun g => ‖K g‖ₑ) ?_) hKi.2` and prove the remaining obligations. Introduce `g`. Establish `hb : ∀ h, ‖φ (h, g)‖ₑ ≤ ‖K g‖ₑ * w ((u h)⁻¹ * g)`. Introduce `h`.

Rewrite using `[hφ, hwT]`. Simplify using `only [enorm_mul]`. Use `gcongr`. Rewrite using `[← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]`. Conclude with `ENNReal.ofReal_toReal_le`.

Combine the equalities or inequalities in the displayed calculation. Establish `hm : Measurable fun h => w ((u h)⁻¹ * g)` using `hw.comp (hu.inv.mul_const g)`. Rewrite using `[lintegral_const_mul _ hm, hw1, mul_one]`. Take `⟨ψ, hψ⟩ : ∃ ψ : H × G → ℂ, ψ = fun p => K (u p.1 * p.2) * (wT p.2 : ℂ)` from `⟨_, rfl⟩`. Establish `hshear : MeasurePreserving (fun p : H × G => (p.1, u p.1 * p.2)) (ν.prod μ) (ν.prod μ)`.

Use `MeasurePreserving.skew_product (g := fun h x => u h * x) (MeasurePreserving.id ν) ((hu.comp measurable_fst).mul measurable_snd) ?_` and prove the remaining obligations. Conclude with `Filter.Eventually.of_forall fun h => map_mul_left_eq_self μ (u h)`. Establish `hψφ : ψ = φ ∘ (fun p : H × G => (p.1, u p.1 * p.2))`. Use function extensionality and compare the values at `p`. Simplify using `[hψ, hφ]`.

Establish `hψi : Integrable ψ (ν.prod μ)`. Rewrite using `[hψφ]`. Conclude with `hshear.integrable_comp hφm.aestronglyMeasurable |>.mpr hφi`. Establish `step1 : ∫ g, K g ∂μ = ∫ g, ∫ h, φ (h, g) ∂ν ∂μ`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations.

Establish `: ∫ h, φ (h, g) ∂ν = K g * ((∫ h, wT ((u h)⁻¹ * g) ∂ν : ℝ) : ℂ)`. Rewrite using `[hφ, ← integral_complex_ofReal, ← integral_const_mul]`. Simplify using `only [this, hone g, Complex.ofReal_one, mul_one]`. Establish `step2 : ∫ g, ∫ h, φ (h, g) ∂ν ∂μ = ∫ h, ∫ g, φ (h, g) ∂μ ∂ν` using `(integral_integral_swap (f := fun h g => φ (h, g)) hφi).symm`. Establish `step3 : ∫ h, ∫ g, φ (h, g) ∂μ ∂ν = ∫ h, ∫ g, ψ (h, g) ∂μ ∂ν`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)` and prove the remaining obligations. Use `integral_mul_left_eq_self (μ := μ) (fun g => φ (h, g)) (u h)` as an intermediate fact. Simplify using `only []`. Rewrite using `[← this]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations.

Simplify using `[hψ, hφ]`. Establish `step4 : ∫ h, ∫ g, ψ (h, g) ∂μ ∂ν = ∫ g, ∫ h, ψ (h, g) ∂ν ∂μ` using `integral_integral_swap (f := fun h g => ψ (h, g)) hψi`. Establish `step5 : ∫ g, ∫ h, ψ (h, g) ∂ν ∂μ = 0`. Establish `: ∀ g, ∫ h, ψ (h, g) ∂ν = 0`. Introduce `g`.

Establish `e : ∀ h, ψ (h, g) = (((ρ g).toReal : ℂ) * (wT g : ℂ)) * F (u h * g)`. Introduce `h`. Rewrite using `[hψ, hK]`. Simplify using `only [hρu]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [e]`. Rewrite using `[integral_const_mul, hF0, mul_zero]`. Simplify using `[this]`. Rewrite using `[step1, step2, step3, step4, step5]`.
-/
theorem integral_eq_zero_of_unfolding {G H : Type} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] [MeasurableSpace H] (ν : Measure H)
    [SFinite ν] (u : H → G) (hu : Measurable u) (w ρ : G → ℝ≥0∞) (F : G → ℂ)
    (hw : Measurable w) (hρ : Measurable ρ) (hF : Measurable F)
    (hw1 : ∀ g, ∫⁻ h, w ((u h)⁻¹ * g) ∂ν = 1) (hρu : ∀ h g, ρ (u h * g) = ρ g)
    (hF0 : ∀ q, ∫ h, F (u h * q) ∂ν = 0) : ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ = 0 := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : G → ℂ, K = fun g => F g * ((ρ g).toReal : ℂ) := ⟨_, rfl⟩
  have hKm : Measurable K := by
    rw [hK]; exact hF.mul (Complex.measurable_ofReal.comp hρ.ennreal_toReal)
  rw [show (∫ g, F g * ((ρ g).toReal : ℂ) ∂μ) = ∫ g, K g ∂μ by rw [hK]]
  by_cases hKi : Integrable K μ
  swap
  · exact integral_undef hKi
  obtain ⟨wT, hwT⟩ : ∃ wT : G → ℝ, wT = fun g => (w g).toReal := ⟨_, rfl⟩
  have hwTm : Measurable wT := by rw [hwT]; exact hw.ennreal_toReal
  have hs : Measurable (fun p : H × G => (u p.1)⁻¹ * p.2) :=
    (hu.comp measurable_fst).inv.mul measurable_snd
  have hone : ∀ g, ∫ h, wT ((u h)⁻¹ * g) ∂ν = 1 := by
    intro g
    have hm : Measurable fun h => w ((u h)⁻¹ * g) := hw.comp (hu.inv.mul_const g)
    have hfin : ∀ᵐ h ∂ν, w ((u h)⁻¹ * g) < ⊤ := ae_lt_top hm (by rw [hw1]; simp)
    rw [hwT]
    simp only []
    rw [integral_toReal hm.aemeasurable hfin, hw1]; simp
  obtain ⟨φ, hφ⟩ : ∃ φ : H × G → ℂ, φ = fun p => K p.2 * (wT ((u p.1)⁻¹ * p.2) : ℂ) := ⟨_, rfl⟩
  have hφm : Measurable φ := by
    rw [hφ]
    exact (hKm.comp measurable_snd).mul
      (Complex.measurable_ofReal.comp (hwTm.comp hs))
  have hφi : Integrable φ (ν.prod μ) := by
    refine ⟨hφm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hφm.enorm.aemeasurable]
    refine lt_of_le_of_lt (lintegral_mono (g := fun g => ‖K g‖ₑ) ?_) hKi.2
    intro g
    have hb : ∀ h, ‖φ (h, g)‖ₑ ≤ ‖K g‖ₑ * w ((u h)⁻¹ * g) := by
      intro h
      rw [hφ, hwT]
      simp only [enorm_mul]
      gcongr
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_toReal_le
    calc ∫⁻ h, ‖φ (h, g)‖ₑ ∂ν ≤ ∫⁻ h, ‖K g‖ₑ * w ((u h)⁻¹ * g) ∂ν := lintegral_mono hb
      _ = ‖K g‖ₑ := by
        have hm : Measurable fun h => w ((u h)⁻¹ * g) := hw.comp (hu.inv.mul_const g)
        rw [lintegral_const_mul _ hm, hw1, mul_one]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : H × G → ℂ, ψ = fun p => K (u p.1 * p.2) * (wT p.2 : ℂ) := ⟨_, rfl⟩
  have hshear : MeasurePreserving (fun p : H × G => (p.1, u p.1 * p.2)) (ν.prod μ) (ν.prod μ) := by
    refine MeasurePreserving.skew_product (g := fun h x => u h * x) (MeasurePreserving.id ν)
      ((hu.comp measurable_fst).mul measurable_snd) ?_
    exact Filter.Eventually.of_forall fun h => map_mul_left_eq_self μ (u h)
  have hψφ : ψ = φ ∘ (fun p : H × G => (p.1, u p.1 * p.2)) := by
    funext p
    simp [hψ, hφ]
  have hψi : Integrable ψ (ν.prod μ) := by
    rw [hψφ]
    exact hshear.integrable_comp hφm.aestronglyMeasurable |>.mpr hφi
  have step1 : ∫ g, K g ∂μ = ∫ g, ∫ h, φ (h, g) ∂ν ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have : ∫ h, φ (h, g) ∂ν = K g * ((∫ h, wT ((u h)⁻¹ * g) ∂ν : ℝ) : ℂ) := by
      rw [hφ, ← integral_complex_ofReal, ← integral_const_mul]
    simp only [this, hone g, Complex.ofReal_one, mul_one]
  have step2 : ∫ g, ∫ h, φ (h, g) ∂ν ∂μ = ∫ h, ∫ g, φ (h, g) ∂μ ∂ν :=
    (integral_integral_swap (f := fun h g => φ (h, g)) hφi).symm
  have step3 : ∫ h, ∫ g, φ (h, g) ∂μ ∂ν = ∫ h, ∫ g, ψ (h, g) ∂μ ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    have := integral_mul_left_eq_self (μ := μ) (fun g => φ (h, g)) (u h)
    simp only []
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp [hψ, hφ]
  have step4 : ∫ h, ∫ g, ψ (h, g) ∂μ ∂ν = ∫ g, ∫ h, ψ (h, g) ∂ν ∂μ :=
    integral_integral_swap (f := fun h g => ψ (h, g)) hψi
  have step5 : ∫ g, ∫ h, ψ (h, g) ∂ν ∂μ = 0 := by
    have : ∀ g, ∫ h, ψ (h, g) ∂ν = 0 := by
      intro g
      have e : ∀ h, ψ (h, g) = (((ρ g).toReal : ℂ) * (wT g : ℂ)) * F (u h * g) := by
        intro h
        rw [hψ, hK]
        simp only [hρu]
        ring
      simp only [e]
      rw [integral_const_mul, hF0, mul_zero]
    simp [this]
  rw [step1, step2, step3, step4, step5]

end GlobalTheory.CompanionTheory.LocVan
