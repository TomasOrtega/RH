import Mathlib

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

namespace Formalism.L2.S.Pv.SchurTens

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/- English proof (translation)
Rewrite using `[ENNReal.ofReal_pow (norm_nonneg z), ofReal_norm]`.
-/
theorem enorm_sq_eq (z : ℂ) : ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg z), ofReal_norm]

/- English proof (translation)
Conclude with `hu.norm.pow 2`.
-/
private theorem aestronglyMeasurable_norm_sq {u : X → ℂ} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x => ‖u x‖ ^ 2) μ := by
  exact hu.norm.pow 2

/- English proof (translation)
Use `(memLp_two_iff_integrable_sq_norm hu).2 ⟨aestronglyMeasurable_norm_sq hu, ?_⟩` and prove the remaining obligations. Establish `e : ∀ x, ‖‖u x‖ ^ 2‖ₑ = ‖u x‖ₑ ^ 2` using `fun x => by`. Rewrite using `[Real.enorm_of_nonneg (by positivity), enorm_sq_eq]`. Rewrite using `[hasFiniteIntegral_iff_enorm]`. Simplify using `only [e]`.

Conclude with `h`.
-/
theorem memLp_two_of_lintegral {u : X → ℂ} (hu : AEStronglyMeasurable u μ) (h : ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ < ⊤) :
    MemLp u 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm hu).2 ⟨aestronglyMeasurable_norm_sq hu, ?_⟩
  have e : ∀ x, ‖‖u x‖ ^ 2‖ₑ = ‖u x‖ₑ ^ 2 := fun x => by
    rw [Real.enorm_of_nonneg (by positivity), enorm_sq_eq]
  rw [hasFiniteIntegral_iff_enorm]
  simp only [e]
  exact h

/- English proof (translation)
Establish `h0 : 0 ≤ᵐ[μ] fun x => ‖u x‖ ^ 2` using `ae_of_all _ fun x => by`. Conclude with `sq_nonneg _`. Rewrite using `[integral_eq_lintegral_of_nonneg_ae h0 (aestronglyMeasurable_norm_sq hu.1)]`. Use `congr 1`. Conclude with `lintegral_congr fun x => (enorm_sq_eq (u x)).symm`.
-/
theorem lintegral_sq_eq {u : X → ℂ} (hu : MemLp u 2 μ) :
    ∫ x, ‖u x‖ ^ 2 ∂μ = (∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ).toReal := by
  have h0 : 0 ≤ᵐ[μ] fun x => ‖u x‖ ^ 2 := ae_of_all _ fun x => by
    exact sq_nonneg _
  rw [integral_eq_lintegral_of_nonneg_ae h0 (aestronglyMeasurable_norm_sq hu.1)]
  congr 1
  exact lintegral_congr fun x => (enorm_sq_eq (u x)).symm

/- English proof (translation)
The claim follows from `Complex.norm_conj z`.
-/
private theorem norm_conj_complex (z : ℂ) : ‖conj z‖ = ‖z‖ := Complex.norm_conj z

/- English proof (translation)
Establish `hu2` using `(memLp_two_iff_integrable_sq_norm hu.1).1 hu`. Establish `hv2` using `(memLp_two_iff_integrable_sq_norm hv.1).1 hv`. Establish `hm : AEStronglyMeasurable (fun x => u x * conj (v x)) μ` using `hu.1.mul (Complex.continuous_conj.comp_aestronglyMeasurable hv.1)`. Use `(hu2.add hv2).mono hm (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Use `show ‖u x * conj (v x)‖ ≤ ‖‖u x‖ ^ 2 + ‖v x‖ ^ 2‖`.

Rewrite using `[norm_mul, norm_conj_complex, Real.norm_of_nonneg (by positivity)]`. Use polynomial arithmetic with `[sq_nonneg (‖u x‖ - ‖v x‖), norm_nonneg (u x), norm_nonneg (v x), mul_nonneg (norm_nonneg (u x)) (norm_nonneg (v x))]`.
-/
theorem integrable_mul_conj {u v : X → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun x => u x * conj (v x)) μ := by
  have hu2 := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  have hv2 := (memLp_two_iff_integrable_sq_norm hv.1).1 hv
  have hm : AEStronglyMeasurable (fun x => u x * conj (v x)) μ :=
    hu.1.mul (Complex.continuous_conj.comp_aestronglyMeasurable hv.1)
  refine (hu2.add hv2).mono hm (ae_of_all _ fun x => ?_)
  show ‖u x * conj (v x)‖ ≤ ‖‖u x‖ ^ 2 + ‖v x‖ ^ 2‖
  rw [norm_mul, norm_conj_complex, Real.norm_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (‖u x‖ - ‖v x‖), norm_nonneg (u x), norm_nonneg (v x),
    mul_nonneg (norm_nonneg (u x)) (norm_nonneg (v x))]

/- English proof (translation)
Establish `h : 0 ≤ (t * a - b) ^ 2 / t` using `div_nonneg (sq_nonneg _) ht.le`. Establish `ht1 : t * t⁻¹ = 1` using `mul_inv_cancel₀ ht.ne'`. Establish `e : (t * a - b) ^ 2 / t = t * a ^ 2 - 2 * (a * b) + b ^ 2 / t`. Take the linear combination `(t * a ^ 2 - 2 * a * b) * ht1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem mul_le_weighted_sq_add_half {a b t : ℝ} (ht : 0 < t) : a * b ≤ (t * a ^ 2 + b ^ 2 / t) / 2 := by
  have h : 0 ≤ (t * a - b) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have ht1 : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have e : (t * a - b) ^ 2 / t = t * a ^ 2 - 2 * (a * b) + b ^ 2 / t := by
    linear_combination (t * a ^ 2 - 2 * a * b) * ht1
  linarith

/- English proof (translation)
Establish `hu2` using `(memLp_two_iff_integrable_sq_norm hu.1).1 hu`. Establish `hv2` using `(memLp_two_iff_integrable_sq_norm hv.1).1 hv`. Establish `hR : Integrable (fun x => (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2) μ` using `((hu2.const_mul t).add (hv2.div_const t)).div_const 2`. Establish `h1 : ∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2 ∂μ = (∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) ∂μ) / 2` using `integral_div _ _`. Establish `h2 : ∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) ∂μ = ∫ x, t * ‖u x‖ ^ 2 ∂μ + ∫ x, ‖v x‖ ^ 2 / t ∂μ` using `integral_add (hu2.const_mul t) (hv2.div_const t)`.

Establish `h3 : ∫ x, t * ‖u x‖ ^ 2 ∂μ = t * ∫ x, ‖u x‖ ^ 2 ∂μ` using `integral_const_mul _ _`. Establish `h4 : ∫ x, ‖v x‖ ^ 2 / t ∂μ = (∫ x, ‖v x‖ ^ 2 ∂μ) / t` using `integral_div _ _`. Rewrite using `[← h4, ← h3, ← h2, ← h1]`. Use `(norm_integral_le_integral_norm _).trans (integral_mono (integrable_mul_conj hu hv).norm hR fun x => ?_)` and prove the remaining obligations. Use `show ‖u x * conj (v x)‖ ≤ (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2`.

Rewrite using `[norm_mul, norm_conj_complex]`. Conclude with `mul_le_weighted_sq_add_half ht`.
-/
theorem norm_integral_mul_conj_le {u v : X → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) {t : ℝ} (ht : 0 < t) :
    ‖∫ x, u x * conj (v x) ∂μ‖ ≤ (t * ∫ x, ‖u x‖ ^ 2 ∂μ + (∫ x, ‖v x‖ ^ 2 ∂μ) / t) / 2 := by
  have hu2 := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  have hv2 := (memLp_two_iff_integrable_sq_norm hv.1).1 hv
  have hR : Integrable (fun x => (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2) μ :=
    ((hu2.const_mul t).add (hv2.div_const t)).div_const 2
  have h1 : ∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2 ∂μ
      = (∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) ∂μ) / 2 := integral_div _ _
  have h2 : ∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) ∂μ
      = ∫ x, t * ‖u x‖ ^ 2 ∂μ + ∫ x, ‖v x‖ ^ 2 / t ∂μ :=
    integral_add (hu2.const_mul t) (hv2.div_const t)
  have h3 : ∫ x, t * ‖u x‖ ^ 2 ∂μ = t * ∫ x, ‖u x‖ ^ 2 ∂μ := integral_const_mul _ _
  have h4 : ∫ x, ‖v x‖ ^ 2 / t ∂μ = (∫ x, ‖v x‖ ^ 2 ∂μ) / t := integral_div _ _
  rw [← h4, ← h3, ← h2, ← h1]
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono (integrable_mul_conj hu hv).norm hR fun x => ?_)
  show ‖u x * conj (v x)‖ ≤ (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2
  rw [norm_mul, norm_conj_complex]
  exact mul_le_weighted_sq_add_half ht

/- English proof (translation)
Establish `hlim : ∀ x, Tendsto (fun m => ‖f m x - f n x‖ₑ ^ 2) atTop (𝓝 (‖F x - f n x‖ₑ ^ 2))`. Introduce `x`. Establish `h1 : Tendsto (fun m => f m x - f n x) atTop (𝓝 (F x - f n x))` using `(hpt x).sub_const _`. Establish `h2 : Tendsto (fun m => ‖f m x - f n x‖ₑ) atTop (𝓝 ‖F x - f n x‖ₑ)` using `(continuous_enorm.tendsto _).comp h1`. Conclude with `((ENNReal.continuous_pow 2).tendsto _).comp h2`.

Establish `hmeas : ∀ m, AEMeasurable (fun x => ‖f m x - f n x‖ₑ ^ 2) μ` using `fun m => (((hf m).sub (hf n)).enorm).pow_const 2`. Establish `hfreq : ∃ᶠ m in atTop, ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ ≤ ε` using `(eventually_atTop.2 ⟨N, h⟩).frequently`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem lintegral_enorm_sub_limit_sq_le {f : ℕ → X → ℂ} {F : X → ℂ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hpt : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x))) (n N : ℕ) {ε : ℝ≥0∞}
    (h : ∀ m ≥ N, ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ ≤ ε) :
    ∫⁻ x, ‖F x - f n x‖ₑ ^ 2 ∂μ ≤ ε := by
  have hlim : ∀ x, Tendsto (fun m => ‖f m x - f n x‖ₑ ^ 2) atTop (𝓝 (‖F x - f n x‖ₑ ^ 2)) := by
    intro x
    have h1 : Tendsto (fun m => f m x - f n x) atTop (𝓝 (F x - f n x)) := (hpt x).sub_const _
    have h2 : Tendsto (fun m => ‖f m x - f n x‖ₑ) atTop (𝓝 ‖F x - f n x‖ₑ) :=
      (continuous_enorm.tendsto _).comp h1
    exact ((ENNReal.continuous_pow 2).tendsto _).comp h2
  have hmeas : ∀ m, AEMeasurable (fun x => ‖f m x - f n x‖ₑ ^ 2) μ := fun m =>
    (((hf m).sub (hf n)).enorm).pow_const 2
  have hfreq : ∃ᶠ m in atTop, ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ ≤ ε :=
    (eventually_atTop.2 ⟨N, h⟩).frequently
  calc ∫⁻ x, ‖F x - f n x‖ₑ ^ 2 ∂μ
      = ∫⁻ x, liminf (fun m => ‖f m x - f n x‖ₑ ^ 2) atTop ∂μ :=
        lintegral_congr fun x => ((hlim x).liminf_eq).symm
    _ ≤ liminf (fun m => ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ) atTop :=
        lintegral_liminf_le' (f := fun m x => ‖f m x - f n x‖ₑ ^ 2) hmeas
    _ ≤ ε := liminf_le_of_frequently_le' hfreq

/- English proof (translation)
Establish `hfm : ∀ n, AEStronglyMeasurable (f n) μ` using `fun n => (hf2 n).1`. Take `⟨N₀, hN₀⟩` from `hC 1 one_pos`. Establish `h0` using `lintegral_enorm_sub_limit_sq_le hfm hpt N₀ N₀ (hN₀ N₀ le_rfl)`. Establish `hsub0 : MemLp (fun x => F x - f N₀ x) 2 μ` using `memLp_two_of_lintegral (hFm.sub (hf2 N₀).1) (lt_of_le_of_lt h0 ENNReal.one_lt_top)`. Establish `hF : MemLp F 2 μ`.

Establish `hadd` using `hsub0.add (hf2 N₀)`. Use `hadd using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Establish `hFg : Integrable (fun x => F x * conj (g x)) μ` using `integrable_mul_conj hF hg`.

Use `⟨hF, hFg, ?_⟩` and prove the remaining obligations. Establish `hlim : Tendsto (fun n => ∫ x, f n x * conj (g x) ∂μ) atTop (𝓝 (∫ x, F x * conj (g x) ∂μ))`. Rewrite using `[Metric.tendsto_atTop]`. Introduce `δ hδ`. Take `⟨G, hGe⟩ : ∃ G, ∫ x, ‖g x‖ ^ 2 ∂μ = G` from `⟨_, rfl⟩`.

Establish `hG : 0 ≤ G`. Rewrite using `[← hGe]`. Conclude with `integral_nonneg fun x => sq_nonneg _`. Establish `hc : 0 < G + 1` using `by linarith`. Establish `hB : 0 < δ ^ 2 / (2 * (G + 1))` using `div_pos (pow_pos hδ 2) (mul_pos two_pos hc)`.

Take `⟨N, hN⟩` from `hC (ENNReal.ofReal (δ ^ 2 / (2 * (G + 1)))) (ENNReal.ofReal_pos.2 hB)`. Use `⟨N, fun n hn => ?_⟩` and prove the remaining obligations. Use `show dist (∫ x, f n x * conj (g x) ∂μ) (∫ x, F x * conj (g x) ∂μ) < δ`. Establish `hsub : MemLp (fun x => F x - f n x) 2 μ` using `hF.sub (hf2 n)`. Establish `hlin` using `lintegral_enorm_sub_limit_sq_le hfm hpt n N (hN n hn)`.

Establish `hA : ∫ x, ‖F x - f n x‖ ^ 2 ∂μ ≤ δ ^ 2 / (2 * (G + 1))`. Rewrite using `[lintegral_sq_eq hsub]`. Conclude with `ENNReal.toReal_le_of_le_ofReal hB.le hlin`. Establish `ht : 0 < (G + 1) / δ` using `div_pos hc hδ`. Establish `hbound` using `norm_integral_mul_conj_le hsub hg ht`.

Rewrite `hbound` using `[hGe]`. Establish `hdiff : ∫ x, F x * conj (g x) ∂μ - ∫ x, f n x * conj (g x) ∂μ = ∫ x, (F x - f n x) * conj (g x) ∂μ`. Rewrite using `[← integral_sub hFg (integrable_mul_conj (hf2 n) hg)]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[dist_eq_norm, norm_sub_rev, hdiff]`. Establish `hδ0 : δ ≠ 0` using `hδ.ne'`. Establish `hc0 : G + 1 ≠ 0` using `hc.ne'`. Establish `h1 : (G + 1) / δ * ∫ x, ‖F x - f n x‖ ^ 2 ∂μ ≤ δ / 2`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2 : G / ((G + 1) / δ) < δ`. Rewrite using `[div_div_eq_mul_div]`. Rewrite using `[div_lt_iff₀ hc]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `tendsto_nhds_unique hlim hL`.
-/
theorem limit_memLp_and_integral_eq (f : ℕ → X → ℂ) (F g : X → ℂ) (hf2 : ∀ n, MemLp (f n) 2 μ) (hFm : AEStronglyMeasurable F μ)
    (hg : MemLp g 2 μ) (hpt : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x)))
    (hC : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ ≤ ε)
    {L : ℂ} (hL : Tendsto (fun n => ∫ x, f n x * conj (g x) ∂μ) atTop (𝓝 L)) :
    MemLp F 2 μ ∧ Integrable (fun x => F x * conj (g x)) μ ∧ ∫ x, F x * conj (g x) ∂μ = L := by
  have hfm : ∀ n, AEStronglyMeasurable (f n) μ := fun n => (hf2 n).1
  obtain ⟨N₀, hN₀⟩ := hC 1 one_pos
  have h0 := lintegral_enorm_sub_limit_sq_le hfm hpt N₀ N₀ (hN₀ N₀ le_rfl)
  have hsub0 : MemLp (fun x => F x - f N₀ x) 2 μ :=
    memLp_two_of_lintegral (hFm.sub (hf2 N₀).1) (lt_of_le_of_lt h0 ENNReal.one_lt_top)
  have hF : MemLp F 2 μ := by
    have hadd := hsub0.add (hf2 N₀)
    convert hadd using 1
    funext x
    simp
  have hFg : Integrable (fun x => F x * conj (g x)) μ := integrable_mul_conj hF hg
  refine ⟨hF, hFg, ?_⟩
  have hlim : Tendsto (fun n => ∫ x, f n x * conj (g x) ∂μ) atTop (𝓝 (∫ x, F x * conj (g x) ∂μ)) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨G, hGe⟩ : ∃ G, ∫ x, ‖g x‖ ^ 2 ∂μ = G := ⟨_, rfl⟩
    have hG : 0 ≤ G := by
      rw [← hGe]
      exact integral_nonneg fun x => sq_nonneg _
    have hc : 0 < G + 1 := by linarith
    have hB : 0 < δ ^ 2 / (2 * (G + 1)) := div_pos (pow_pos hδ 2) (mul_pos two_pos hc)
    obtain ⟨N, hN⟩ := hC (ENNReal.ofReal (δ ^ 2 / (2 * (G + 1)))) (ENNReal.ofReal_pos.2 hB)
    refine ⟨N, fun n hn => ?_⟩
    show dist (∫ x, f n x * conj (g x) ∂μ) (∫ x, F x * conj (g x) ∂μ) < δ
    have hsub : MemLp (fun x => F x - f n x) 2 μ := hF.sub (hf2 n)
    have hlin := lintegral_enorm_sub_limit_sq_le hfm hpt n N (hN n hn)
    have hA : ∫ x, ‖F x - f n x‖ ^ 2 ∂μ ≤ δ ^ 2 / (2 * (G + 1)) := by
      rw [lintegral_sq_eq hsub]
      exact ENNReal.toReal_le_of_le_ofReal hB.le hlin
    have ht : 0 < (G + 1) / δ := div_pos hc hδ
    have hbound := norm_integral_mul_conj_le hsub hg ht
    rw [hGe] at hbound
    have hdiff : ∫ x, F x * conj (g x) ∂μ - ∫ x, f n x * conj (g x) ∂μ
        = ∫ x, (F x - f n x) * conj (g x) ∂μ := by
      rw [← integral_sub hFg (integrable_mul_conj (hf2 n) hg)]
      congr 1
      funext x
      ring
    rw [dist_eq_norm, norm_sub_rev, hdiff]
    have hδ0 : δ ≠ 0 := hδ.ne'
    have hc0 : G + 1 ≠ 0 := hc.ne'
    have h1 : (G + 1) / δ * ∫ x, ‖F x - f n x‖ ^ 2 ∂μ ≤ δ / 2 := by
      calc (G + 1) / δ * ∫ x, ‖F x - f n x‖ ^ 2 ∂μ
          ≤ (G + 1) / δ * (δ ^ 2 / (2 * (G + 1))) := mul_le_mul_of_nonneg_left hA ht.le
        _ = δ / 2 := by field_simp
    have h2 : G / ((G + 1) / δ) < δ := by
      rw [div_div_eq_mul_div]
      rw [div_lt_iff₀ hc]
      nlinarith
    linarith
  exact tendsto_nhds_unique hlim hL

end Formalism.L2.S.Pv.SchurTens
