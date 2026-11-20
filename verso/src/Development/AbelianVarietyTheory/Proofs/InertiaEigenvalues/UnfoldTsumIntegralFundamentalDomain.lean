import Mathlib
open MeasureTheory

namespace GlobalTheory

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {ν : Measure G} [ν.IsHaarMeasure]
    {Γ : Subgroup G} [Countable Γ] {𝓖 : Set G}

/- English proof (translation)
Rewrite using `[lintegral_tsum (fun γ => by fun_prop)]`. Use `set F : G → ENNReal := fun g => ‖P (x⁻¹ * g)‖ₑ * ‖a x‖ₑ * ‖b g‖ₑ with hF`. Establish `key : ∀ γ : Γ, ∀ y, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ = F (γ⁻¹ • y)`. Introduce `γ y`. Establish `h1 : γ⁻¹ • y = (γ : G)⁻¹ * y` using `by simp [Subgroup.smul_def]`.

Rewrite using `[hF, h1]`. Use `show _ = ‖P (x⁻¹ * ((γ : G)⁻¹ * y))‖ₑ * ‖a x‖ₑ * ‖b ((γ : G)⁻¹ * y)‖ₑ`. Rewrite using `[hb _ (Γ.inv_mem γ.2)]`. Simplify using `only [mul_assoc]`. Repeatedly rewrite using `[key]`.

Rewrite using `[← h𝓖.lintegral_eq_tsum' F, ← lintegral_mul_left_eq_self _ x]`. Simplify using `[hF]`.
-/
theorem fundamentalDomain_lintegral_unfold_left (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) {a b P : G → ℂ}
    (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) (hbm : Measurable b) (hPm : Measurable P) (x : G) :
    ∫⁻ y in 𝓖, ∑' γ : Γ, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ ∂ν
      = ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν := by
  rw [lintegral_tsum (fun γ => by fun_prop)]
  set F : G → ENNReal := fun g => ‖P (x⁻¹ * g)‖ₑ * ‖a x‖ₑ * ‖b g‖ₑ with hF
  have key : ∀ γ : Γ, ∀ y, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ = F (γ⁻¹ • y) := by
    intro γ y
    have h1 : γ⁻¹ • y = (γ : G)⁻¹ * y := by simp [Subgroup.smul_def]
    rw [hF, h1]
    show _ = ‖P (x⁻¹ * ((γ : G)⁻¹ * y))‖ₑ * ‖a x‖ₑ * ‖b ((γ : G)⁻¹ * y)‖ₑ
    rw [hb _ (Γ.inv_mem γ.2)]; simp only [mul_assoc]
  simp_rw [key]
  rw [← h𝓖.lintegral_eq_tsum' F, ← lintegral_mul_left_eq_self _ x]
  simp [hF]

/- English proof (translation)
Use `set F : G → ℂ := fun g => star (a x) * b g * P (x⁻¹ * g) with hF`. Establish `hFi : Integrable F ν`. Use `⟨by fun_prop, ?_⟩` and prove the remaining obligations. Unfold `HasFiniteIntegral`. Rewrite using `[← lintegral_mul_left_eq_self _ x]`.

Use `lt_of_le_of_lt (le_of_eq ?_) hfin.lt_top` and prove the remaining obligations. Use `lintegral_congr (fun g => ?_)` and prove the remaining obligations. Establish `hs : ‖star (a x)‖ₑ = ‖a x‖ₑ` using `by rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]`. Simplify using `only [hF, enorm_mul, hs, inv_mul_cancel_left]`. Expand and normalize the polynomial expressions, which then agree.

Establish `key : ∀ γ : Γ, ∀ y, star (a x) * b y * P (x⁻¹ * (γ : G)⁻¹ * y) = F (γ⁻¹ • y)`. Introduce `γ y`. Establish `h1 : γ⁻¹ • y = (γ : G)⁻¹ * y` using `by simp [Subgroup.smul_def]`. Rewrite using `[hF, h1]`. Use `show _ = star (a x) * b ((γ : G)⁻¹ * y) * P (x⁻¹ * ((γ : G)⁻¹ * y))`.

Rewrite using `[hb _ (Γ.inv_mem γ.2)]`. Simplify using `only [mul_assoc]`. Repeatedly rewrite using `[key]`. Rewrite using `[← h𝓖.integral_eq_tsum' F hFi, ← integral_mul_left_eq_self F x]`. Simplify using `[hF]`.
-/
theorem fundamentalDomain_integral_unfold_left (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) {a b P : G → ℂ}
    (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) (hbm : Measurable b) (hPm : Measurable P) (x : G)
    (hfin : ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν ≠ ⊤) :
    ∑' γ : Γ, ∫ y in 𝓖, star (a x) * b y * P (x⁻¹ * (γ : G)⁻¹ * y) ∂ν
      = ∫ g, star (a x) * b (x * g) * P g ∂ν := by
  set F : G → ℂ := fun g => star (a x) * b g * P (x⁻¹ * g) with hF
  have hFi : Integrable F ν := by
    refine ⟨by fun_prop, ?_⟩
    unfold HasFiniteIntegral
    rw [← lintegral_mul_left_eq_self _ x]
    refine lt_of_le_of_lt (le_of_eq ?_) hfin.lt_top
    refine lintegral_congr (fun g => ?_)
    have hs : ‖star (a x)‖ₑ = ‖a x‖ₑ := by rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]
    simp only [hF, enorm_mul, hs, inv_mul_cancel_left]
    ring
  have key : ∀ γ : Γ, ∀ y, star (a x) * b y * P (x⁻¹ * (γ : G)⁻¹ * y) = F (γ⁻¹ • y) := by
    intro γ y
    have h1 : γ⁻¹ • y = (γ : G)⁻¹ * y := by simp [Subgroup.smul_def]
    rw [hF, h1]
    show _ = star (a x) * b ((γ : G)⁻¹ * y) * P (x⁻¹ * ((γ : G)⁻¹ * y))
    rw [hb _ (Γ.inv_mem γ.2)]; simp only [mul_assoc]
  simp_rw [key]
  rw [← h𝓖.integral_eq_tsum' F hFi, ← integral_mul_left_eq_self F x]
  simp [hF]

/- English proof (translation)
Establish `ham : Measurable a` using `ha.measurable`. Establish `hbm : Measurable b` using `hbc.measurable`. Establish `hPm : Measurable P` using `hP.measurable`. Establish `hs : ∀ z : ℂ, ‖star z‖ₑ = ‖z‖ₑ` using `fun z => by rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]`. Use `set μ := ν.restrict 𝓖 with hμ`.

Establish `hT : ∫⁻ x, ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν ∂μ ≠ ⊤`. Rewrite using `[← lintegral_congr (fun x => fundamentalDomain_lintegral_unfold_left h𝓖 hb hbm hPm (a := a) x)]`. Conclude with `hfin`. Use `set k : G → G → ℂ := fun x g => star (a x) * b (x * g) * P g with hk`. Establish `hkm : Measurable (Function.uncurry k)`.

Simplify using `only [hk, Function.uncurry_def]`. Use `fun_prop`. Establish `hki : Integrable (Function.uncurry k) (μ.prod ν)`. Use `⟨hkm.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Unfold `HasFiniteIntegral`.

Rewrite using `[lintegral_prod _ (by fun_prop)]`. Use `lt_of_le_of_lt (le_of_eq ?_) hT.lt_top` and prove the remaining obligations. Use `lintegral_congr (fun x => lintegral_congr (fun g => ?_))` and prove the remaining obligations. Simplify using `only [hk, Function.uncurry_apply_pair, enorm_mul, hs]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hki.swap.integral_prod_left`. Use `h1.congr (Filter.Eventually.of_forall (fun g => ?_))` and prove the remaining obligations. Simplify using `only [hk, Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair]`. Rewrite using `[integral_mul_const, mul_comm]`.

Use `set f : Γ → G × G → ℂ := fun γ z => star (a z.1) * b z.2 * P (z.1⁻¹ * (γ : G)⁻¹ * z.2) with hf`. Establish `hfm : ∀ γ, Measurable (f γ)` using `fun γ => by simp only [hf]; fun_prop`. Establish `hfe : ∀ γ x y, ‖f γ (x, y)‖ₑ = ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ`. Introduce `γ x y`. Simplify using `only [hf, enorm_mul, hs]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsum : ∑' γ : Γ, ∫⁻ x, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ ∂μ ≠ ⊤`. Rewrite using `[← lintegral_tsum (fun γ => ((hfm γ).enorm.lintegral_prod_right').aemeasurable)]`. Establish `hx : ∀ x, ∑' γ : Γ, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ = ∫⁻ y, ∑' γ : Γ, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ ∂μ` using `fun x => by`. Rewrite using `[← lintegral_tsum (f := fun γ y => ‖f γ (x, y)‖ₑ) (fun γ => ((hfm γ).comp measurable_prodMk_left).enorm.aemeasurable)]`.

Simplify using `only [hfe]`. Rewrite using `[lintegral_congr hx]`. Conclude with `hfin`. Establish `hfi : ∀ γ, Integrable (f γ) (μ.prod μ)` using `fun γ => ⟨(hfm γ).aestronglyMeasurable, by`. Unfold `HasFiniteIntegral`.

Rewrite using `[lintegral_prod _ (hfm γ).enorm.aemeasurable]`. Conclude with `lt_of_le_of_lt (ENNReal.le_tsum (f := fun γ : Γ => ∫⁻ x, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ ∂μ) γ) hsum.lt_top⟩`. Establish `lhs : ∀ γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν) = ∫ x, ∫ y, f γ (x, y) ∂μ ∂μ`. Introduce `γ`. Rewrite using `[← Measure.prod_restrict, ← integral_prod _ (hfi γ)]`.

Rewrite using `[tsum_congr lhs, ← integral_tsum (fun γ => (hfi γ).integral_prod_left.aestronglyMeasurable) (ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun γ => lintegral_mono fun x => enorm_integral_le_lintegral_enorm _))]`. Establish `hae : ∀ᵐ x ∂μ, ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν < ⊤` using `ae_lt_top (show Measurable (fun z : G × G => ‖P z.2‖ₑ * ‖a z.1‖ₑ * ‖b (z.1 * z.2)‖ₑ) by fun_prop).lintegral_prod_right' hT`. Establish `step : (∫ x, ∑' γ : Γ, ∫ y, f γ (x, y) ∂μ ∂μ) = ∫ x, ∫ g, k x g ∂ν ∂μ` using `integral_congr_ae (hae.mono fun x hx => fundamentalDomain_integral_unfold_left h𝓖 hb hbm hPm x hx.ne)`. Rewrite using `[step, integral_integral_swap hki]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations.

Simplify using `only [hk]`. Rewrite using `[integral_mul_const, mul_comm]`.
-/
theorem unfold_tsum_fundamentalDomain (ν : Measure G) [ν.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (a b P : G → ℂ)
    (ha : Continuous a) (hbc : Continuous b) (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g)
    (hP : StronglyMeasurable P)
    (hfin : ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' γ : Γ, ‖P (g₁⁻¹ * (γ : G)⁻¹ * g₂)‖ₑ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤) :
    Integrable (fun g => P g * ∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ν ∧
    ∑' γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν) =
      ∫ g, P g * (∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ∂ν := by
  have ham : Measurable a := ha.measurable
  have hbm : Measurable b := hbc.measurable
  have hPm : Measurable P := hP.measurable
  have hs : ∀ z : ℂ, ‖star z‖ₑ = ‖z‖ₑ := fun z => by rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]
  set μ := ν.restrict 𝓖 with hμ

  have hT : ∫⁻ x, ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν ∂μ ≠ ⊤ := by
    rw [← lintegral_congr (fun x => fundamentalDomain_lintegral_unfold_left h𝓖 hb hbm hPm (a := a) x)]
    exact hfin
  set k : G → G → ℂ := fun x g => star (a x) * b (x * g) * P g with hk
  have hkm : Measurable (Function.uncurry k) := by
    simp only [hk, Function.uncurry_def]; fun_prop
  have hki : Integrable (Function.uncurry k) (μ.prod ν) := by
    refine ⟨hkm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod _ (by fun_prop)]
    refine lt_of_le_of_lt (le_of_eq ?_) hT.lt_top
    refine lintegral_congr (fun x => lintegral_congr (fun g => ?_))
    simp only [hk, Function.uncurry_apply_pair, enorm_mul, hs]
    ring
  refine ⟨?_, ?_⟩
  · have h1 := hki.swap.integral_prod_left
    refine h1.congr (Filter.Eventually.of_forall (fun g => ?_))
    simp only [hk, Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair]
    rw [integral_mul_const, mul_comm]

  · set f : Γ → G × G → ℂ := fun γ z => star (a z.1) * b z.2 * P (z.1⁻¹ * (γ : G)⁻¹ * z.2) with hf
    have hfm : ∀ γ, Measurable (f γ) := fun γ => by simp only [hf]; fun_prop
    have hfe : ∀ γ x y, ‖f γ (x, y)‖ₑ = ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ := by
      intro γ x y; simp only [hf, enorm_mul, hs]; ring
    have hsum : ∑' γ : Γ, ∫⁻ x, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ ∂μ ≠ ⊤ := by
      rw [← lintegral_tsum (fun γ => ((hfm γ).enorm.lintegral_prod_right').aemeasurable)]
      have hx : ∀ x, ∑' γ : Γ, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ
          = ∫⁻ y, ∑' γ : Γ, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ ∂μ := fun x => by
        rw [← lintegral_tsum (f := fun γ y => ‖f γ (x, y)‖ₑ)
          (fun γ => ((hfm γ).comp measurable_prodMk_left).enorm.aemeasurable)]
        simp only [hfe]
      rw [lintegral_congr hx]
      exact hfin
    have hfi : ∀ γ, Integrable (f γ) (μ.prod μ) := fun γ =>
      ⟨(hfm γ).aestronglyMeasurable, by
        unfold HasFiniteIntegral
        rw [lintegral_prod _ (hfm γ).enorm.aemeasurable]
        exact lt_of_le_of_lt (ENNReal.le_tsum (f := fun γ : Γ => ∫⁻ x, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ ∂μ) γ)
          hsum.lt_top⟩
    have lhs : ∀ γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν)
        = ∫ x, ∫ y, f γ (x, y) ∂μ ∂μ := by
      intro γ; rw [← Measure.prod_restrict, ← integral_prod _ (hfi γ)]
    rw [tsum_congr lhs, ← integral_tsum (fun γ => (hfi γ).integral_prod_left.aestronglyMeasurable)
      (ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun γ =>
        lintegral_mono fun x => enorm_integral_le_lintegral_enorm _))]
    have hae : ∀ᵐ x ∂μ, ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν < ⊤ :=
      ae_lt_top (show Measurable (fun z : G × G => ‖P z.2‖ₑ * ‖a z.1‖ₑ * ‖b (z.1 * z.2)‖ₑ) by
        fun_prop).lintegral_prod_right' hT
    have step : (∫ x, ∑' γ : Γ, ∫ y, f γ (x, y) ∂μ ∂μ) = ∫ x, ∫ g, k x g ∂ν ∂μ :=
      integral_congr_ae (hae.mono fun x hx => fundamentalDomain_integral_unfold_left h𝓖 hb hbm hPm x hx.ne)
    rw [step, integral_integral_swap hki]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [hk]
    rw [integral_mul_const, mul_comm]
end
end GlobalTheory
