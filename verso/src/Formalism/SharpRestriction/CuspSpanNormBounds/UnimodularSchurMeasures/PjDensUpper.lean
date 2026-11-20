import Mathlib

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

/- English proof (translation)
Establish `h1 : 2 * p * (q + r) ≤ t * p ^ 2 + (q + r) ^ 2 / t`. Rewrite using `[← sub_nonneg]`. Establish `: t * p ^ 2 + (q + r) ^ 2 / t - 2 * p * (q + r) = (t * p - (q + r)) ^ 2 / t`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Check the signs of the components of the expression. Establish `h2 : (q + r) ^ 2 ≤ 2 * q ^ 2 + 2 * r ^ 2` using `by nlinarith [sq_nonneg (q - r)]`. Establish `h3 : (1 + 1 / t) * (q + r) ^ 2 ≤ (1 + 1 / t) * (2 * q ^ 2 + 2 * r ^ 2)`. Establish `: 0 ≤ 1 + 1 / t` using `by positivity`.

Conclude with `mul_le_mul_of_nonneg_left h2 this`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pj_dens_real (t p q r : ℝ) (ht : 0 < t) :
    (p + q + r) ^ 2 ≤ (1 + t) * p ^ 2 + (1 + 1 / t) * (2 * q ^ 2 + 2 * r ^ 2) := by
  have h1 : 2 * p * (q + r) ≤ t * p ^ 2 + (q + r) ^ 2 / t := by
    rw [← sub_nonneg]
    have : t * p ^ 2 + (q + r) ^ 2 / t - 2 * p * (q + r) = (t * p - (q + r)) ^ 2 / t := by
      field_simp
      ring
    rw [this]
    positivity
  have h2 : (q + r) ^ 2 ≤ 2 * q ^ 2 + 2 * r ^ 2 := by nlinarith [sq_nonneg (q - r)]
  have h3 : (1 + 1 / t) * (q + r) ^ 2 ≤ (1 + 1 / t) * (2 * q ^ 2 + 2 * r ^ 2) := by
    have : 0 ≤ 1 + 1 / t := by positivity
    exact mul_le_mul_of_nonneg_left h2 this
  calc (p + q + r) ^ 2 = p ^ 2 + 2 * p * (q + r) + (q + r) ^ 2 := by ring
    _ ≤ p ^ 2 + (t * p ^ 2 + (q + r) ^ 2 / t) + (q + r) ^ 2 := by linarith
    _ = (1 + t) * p ^ 2 + (1 + 1 / t) * (q + r) ^ 2 := by ring
    _ ≤ _ := by linarith

section Dens

variable {G : Type} [MeasurableSpace G] (μ : Measure G) {Hs : Type} [NormedAddCommGroup Hs]
  [InnerProductSpace ℂ Hs] (σ : G → (Hs →L[ℂ] Hs))

/- English proof (translation)
The claim follows from `(hm x y).norm.pow 2`.
-/
theorem pj_dens_meas (hm : ∀ x y : Hs, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ) (x y : Hs) :
    AEStronglyMeasurable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ := (hm x y).norm.pow 2

/- English proof (translation)
Take `⟨u, hu, hux⟩` from `mem_closure_iff_seq_limit.1 (hV x)`. Take `⟨v, hv, hvy⟩` from `mem_closure_iff_seq_limit.1 (hV y)`. Use `set f : ℕ → G → ℝ≥0∞ := fun n g => ENNReal.ofReal (‖⟪v n, σ g (u n)⟫_ℂ‖ ^ 2) with hf`. Establish `hfm : ∀ n, AEMeasurable (f n) μ` using `fun n => (pj_dens_meas μ σ hm (u n) (v n)).aemeasurable.ennreal_ofReal`. Establish `hpt : ∀ g, Tendsto (fun n => f n g) atTop (𝓝 (ENNReal.ofReal (‖⟪y, σ g x⟫_ℂ‖ ^ 2)))` using `fun g => ENNReal.tendsto_ofReal (((hvy.inner (((σ g).continuous.tendsto x).comp hux)).norm).pow 2)`.

Establish `hF : ∫⁻ g, liminf (fun n => f n g) atTop ∂μ ≤ liminf (fun n => ∫⁻ g, f n g ∂μ) atTop` using `lintegral_liminf_le' hfm`. Establish `e1 : (fun g => liminf (fun n => f n g) atTop) = fun g => ENNReal.ofReal (‖⟪y, σ g x⟫_ℂ‖ ^ 2)`. Use function extensionality and compare the values at `fun g => (hpt g).liminf_eq`. Establish `e2 : ∀ n, ∫⁻ g, f n g ∂μ = ENNReal.ofReal (‖u n‖ ^ 2 * ‖v n‖ ^ 2 / d)` using `fun n => by`. Rewrite using `[← (h _ (hu n) _ (hv n)).2, ofReal_integral_eq_lintegral_ofReal (h _ (hu n) _ (hv n)).1 (ae_of_all _ fun g => by positivity)]`.

Establish `e3 : Tendsto (fun n => ENNReal.ofReal (‖u n‖ ^ 2 * ‖v n‖ ^ 2 / d)) atTop (𝓝 (ENNReal.ofReal (‖x‖ ^ 2 * ‖y‖ ^ 2 / d)))` using `ENNReal.tendsto_ofReal (((hux.norm.pow 2).mul (hvy.norm.pow 2)).div_const d)`. Rewrite `hF` using `[e1]`. Simplify using `only [e2] at hF`. Rewrite `hF` using `[e3.liminf_eq]`. Establish `hnn : 0 ≤ᵐ[μ] fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2` using `ae_of_all _ fun g => by positivity`.

Establish `hme` using `pj_dens_meas μ σ hm x y`. Use `⟨⟨hme, (hasFiniteIntegral_iff_ofReal hnn).2 (lt_of_le_of_lt hF ENNReal.ofReal_lt_top)⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_eq_lintegral_of_nonneg_ae hnn hme]`. Conclude with `ENNReal.toReal_le_of_le_ofReal (by positivity) hF`.
-/
theorem pj_dens_upper (hm : ∀ x y : Hs, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ)
    (V : Submodule ℂ Hs) (hV : Dense (V : Set Hs)) (d : ℝ)
    (h : ∀ x ∈ V, ∀ y ∈ V, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) (hd : 0 < d) (x y : Hs) :
    Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧ ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 / d := by
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.1 (hV x)
  obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.1 (hV y)
  set f : ℕ → G → ℝ≥0∞ := fun n g => ENNReal.ofReal (‖⟪v n, σ g (u n)⟫_ℂ‖ ^ 2) with hf
  have hfm : ∀ n, AEMeasurable (f n) μ := fun n => (pj_dens_meas μ σ hm (u n) (v n)).aemeasurable.ennreal_ofReal
  have hpt : ∀ g, Tendsto (fun n => f n g) atTop (𝓝 (ENNReal.ofReal (‖⟪y, σ g x⟫_ℂ‖ ^ 2))) := fun g =>
    ENNReal.tendsto_ofReal (((hvy.inner (((σ g).continuous.tendsto x).comp hux)).norm).pow 2)
  have hF : ∫⁻ g, liminf (fun n => f n g) atTop ∂μ ≤ liminf (fun n => ∫⁻ g, f n g ∂μ) atTop :=
    lintegral_liminf_le' hfm
  have e1 : (fun g => liminf (fun n => f n g) atTop) = fun g => ENNReal.ofReal (‖⟪y, σ g x⟫_ℂ‖ ^ 2) :=
    funext fun g => (hpt g).liminf_eq
  have e2 : ∀ n, ∫⁻ g, f n g ∂μ = ENNReal.ofReal (‖u n‖ ^ 2 * ‖v n‖ ^ 2 / d) := fun n => by
    rw [← (h _ (hu n) _ (hv n)).2,
      ofReal_integral_eq_lintegral_ofReal (h _ (hu n) _ (hv n)).1 (ae_of_all _ fun g => by positivity)]
  have e3 : Tendsto (fun n => ENNReal.ofReal (‖u n‖ ^ 2 * ‖v n‖ ^ 2 / d)) atTop
      (𝓝 (ENNReal.ofReal (‖x‖ ^ 2 * ‖y‖ ^ 2 / d))) :=
    ENNReal.tendsto_ofReal (((hux.norm.pow 2).mul (hvy.norm.pow 2)).div_const d)
  rw [e1] at hF
  simp only [e2] at hF
  rw [e3.liminf_eq] at hF
  have hnn : 0 ≤ᵐ[μ] fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2 := ae_of_all _ fun g => by positivity
  have hme := pj_dens_meas μ σ hm x y
  refine ⟨⟨hme, (hasFiniteIntegral_iff_ofReal hnn).2 (lt_of_le_of_lt hF ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hme]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hF

/- English proof (translation)
Introduce `x y`. Establish `up` using `pj_dens_upper μ σ hm V hV d h hd`. Use `⟨(up x y).1, le_antisymm (up x y).2 ?_⟩` and prove the remaining obligations. Take `⟨u, hu, hux⟩` from `mem_closure_iff_seq_limit.1 (hV x)`. Take `⟨v, hv, hvy⟩` from `mem_closure_iff_seq_limit.1 (hV y)`.

Use `set N : ℝ := ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ with hN`. Establish `hN0 : 0 ≤ N` using `integral_nonneg fun g => by positivity`. Establish `key : ∀ t : ℝ, 0 < t → ‖x‖ ^ 2 * ‖y‖ ^ 2 / d ≤ (1 + t) * N`. Introduce `t ht`. Establish `hn : ∀ n, ‖u n‖ ^ 2 * ‖v n‖ ^ 2 / d ≤ (1 + t) * N + (1 + 1 / t) * (2 * (‖u n - x‖ ^ 2 * ‖v n‖ ^ 2 / d) + 2 * (‖x‖ ^ 2 * ‖v n - y‖ ^ 2 / d))`.

Introduce `n`. Establish `i0` using `(up x y).1`. Establish `i1` using `(up (u n - x) (v n)).1`. Establish `i2` using `(up x (v n - y)).1`. Establish `hle : ∫ g, ‖⟪v n, σ g (u n)⟫_ℂ‖ ^ 2 ∂μ ≤ ∫ g, ((1 + t) * ‖⟪y, σ g x⟫_ℂ‖ ^ 2 + (1 + 1 / t) * (2 * ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 + 2 * ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2)) ∂μ`.

Use `integral_mono (h _ (hu n) _ (hv n)).1 ((i0.const_mul _).add (((i1.const_mul 2).add (i2.const_mul 2)).const_mul _)) fun g => ?_` and prove the remaining obligations. Establish `hsum : ⟪v n, σ g (u n)⟫_ℂ = ⟪y, σ g x⟫_ℂ + ⟪v n, σ g (u n - x)⟫_ℂ + ⟪v n - y, σ g x⟫_ℂ`. Rewrite using `[map_sub, inner_sub_right, inner_sub_left]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ‖⟪v n, σ g (u n)⟫_ℂ‖ ≤ ‖⟪y, σ g x⟫_ℂ‖ + ‖⟪v n, σ g (u n - x)⟫_ℂ‖ + ‖⟪v n - y, σ g x⟫_ℂ‖`.

Rewrite using `[hsum]`. Conclude with `norm_add₃_le`. Conclude with `le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) (pj_dens_real t _ _ _ ht)`. Establish `heq : ∫ g, ((1 + t) * ‖⟪y, σ g x⟫_ℂ‖ ^ 2 + (1 + 1 / t) * (2 * ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 + 2 * ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2)) ∂μ = (1 + t) * N + (1 + 1 / t) * (2 * (∫ g, ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 ∂μ) + 2 * ∫ g, ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2 ∂μ)`. Establish `i12 : Integrable (fun g => 2 * ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 + 2 * ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2) μ` using `(i1.const_mul 2).add (i2.const_mul 2)`.

Establish `i3 : Integrable (fun g => (1 + 1 / t) * (2 * ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 + 2 * ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2)) μ` using `i12.const_mul _`. Rewrite using `[integral_add (i0.const_mul (1 + t)) i3, integral_const_mul, integral_const_mul, integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul]`. Rewrite `hle` using `[(h _ (hu n) _ (hv n)).2, heq]`. Establish `b1` using `(up (u n - x) (v n)).2`. Establish `b2` using `(up x (v n - y)).2`.

Establish `hpos : 0 ≤ 1 + 1 / t` using `by positivity`. Establish `: (1 + 1 / t) * (2 * (∫ g, ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 ∂μ) + 2 * ∫ g, ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2 ∂μ) ≤ (1 + 1 / t) * (2 * (‖u n - x‖ ^ 2 * ‖v n‖ ^ 2 / d) + 2 * (‖x‖ ^ 2 * ‖v n - y‖ ^ 2 / d))` using `mul_le_mul_of_nonneg_left (by linarith) hpos`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0x : Tendsto (fun n => ‖u n - x‖) atTop (𝓝 0)` using `tendsto_iff_norm_sub_tendsto_zero.1 hux`. Establish `h0y : Tendsto (fun n => ‖v n - y‖) atTop (𝓝 0)` using `tendsto_iff_norm_sub_tendsto_zero.1 hvy`.

Establish `hL : Tendsto (fun n => ‖u n‖ ^ 2 * ‖v n‖ ^ 2 / d) atTop (𝓝 (‖x‖ ^ 2 * ‖y‖ ^ 2 / d))` using `((hux.norm.pow 2).mul (hvy.norm.pow 2)).div_const d`. Establish `a1` using `((h0x.pow 2).mul (hvy.norm.pow 2)).div_const d`. Establish `a2` using `((tendsto_const_nhds (x := ‖x‖ ^ 2) (f := atTop (α := ℕ))).mul (h0y.pow 2)).div_const d`. Establish `hR : Tendsto (fun n => (1 + t) * N + (1 + 1 / t) * (2 * (‖u n - x‖ ^ 2 * ‖v n‖ ^ 2 / d) + 2 * (‖x‖ ^ 2 * ‖v n - y‖ ^ 2 / d))) atTop (𝓝 ((1 + t) * N + (1 + 1 / t) * (2 * ((0 : ℝ) ^ 2 * ‖y‖ ^ 2 / d) + 2 * (‖x‖ ^ 2 * (0 : ℝ) ^ 2 / d))))` using `tendsto_const_nhds.add (((a1.const_mul 2).add (a2.const_mul 2)).const_mul _)`. Establish `hfin` using `le_of_tendsto_of_tendsto' hL hR hn`.

Simplify using `using hfin`. Use `le_of_forall_pos_le_add fun ε hε => ?_` and prove the remaining obligations. Establish `h1` using `key (ε / (N + 1)) (by positivity)`. Establish `h2 : ε / (N + 1) * N ≤ ε`. Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pj_dens (_hU : ∀ g x, ‖σ g x‖ = ‖x‖)
    (hm : ∀ x y : Hs, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ)
    (V : Submodule ℂ Hs) (hV : Dense (V : Set Hs)) (d : ℝ) (hd : 0 < d)
    (h : ∀ x ∈ V, ∀ y ∈ V, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) :
    ∀ x y : Hs, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d := by
  intro x y
  have up := pj_dens_upper μ σ hm V hV d h hd
  refine ⟨(up x y).1, le_antisymm (up x y).2 ?_⟩
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.1 (hV x)
  obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.1 (hV y)
  set N : ℝ := ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ with hN
  have hN0 : 0 ≤ N := integral_nonneg fun g => by positivity
  have key : ∀ t : ℝ, 0 < t → ‖x‖ ^ 2 * ‖y‖ ^ 2 / d ≤ (1 + t) * N := by
    intro t ht
    have hn : ∀ n, ‖u n‖ ^ 2 * ‖v n‖ ^ 2 / d ≤ (1 + t) * N +
        (1 + 1 / t) * (2 * (‖u n - x‖ ^ 2 * ‖v n‖ ^ 2 / d) + 2 * (‖x‖ ^ 2 * ‖v n - y‖ ^ 2 / d)) := by
      intro n
      have i0 := (up x y).1
      have i1 := (up (u n - x) (v n)).1
      have i2 := (up x (v n - y)).1
      have hle : ∫ g, ‖⟪v n, σ g (u n)⟫_ℂ‖ ^ 2 ∂μ ≤
          ∫ g, ((1 + t) * ‖⟪y, σ g x⟫_ℂ‖ ^ 2 + (1 + 1 / t) *
            (2 * ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 + 2 * ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2)) ∂μ := by
        refine integral_mono (h _ (hu n) _ (hv n)).1
          ((i0.const_mul _).add (((i1.const_mul 2).add (i2.const_mul 2)).const_mul _)) fun g => ?_
        have hsum : ⟪v n, σ g (u n)⟫_ℂ = ⟪y, σ g x⟫_ℂ + ⟪v n, σ g (u n - x)⟫_ℂ + ⟪v n - y, σ g x⟫_ℂ := by
          rw [map_sub, inner_sub_right, inner_sub_left]
          ring
        have h1 : ‖⟪v n, σ g (u n)⟫_ℂ‖ ≤ ‖⟪y, σ g x⟫_ℂ‖ + ‖⟪v n, σ g (u n - x)⟫_ℂ‖ + ‖⟪v n - y, σ g x⟫_ℂ‖ := by
          rw [hsum]
          exact norm_add₃_le
        exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) (pj_dens_real t _ _ _ ht)
      have heq : ∫ g, ((1 + t) * ‖⟪y, σ g x⟫_ℂ‖ ^ 2 + (1 + 1 / t) *
            (2 * ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 + 2 * ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2)) ∂μ =
          (1 + t) * N + (1 + 1 / t) * (2 * (∫ g, ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 ∂μ) +
            2 * ∫ g, ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2 ∂μ) := by
        have i12 : Integrable (fun g => 2 * ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 + 2 * ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2) μ :=
          (i1.const_mul 2).add (i2.const_mul 2)
        have i3 : Integrable (fun g => (1 + 1 / t) *
            (2 * ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 + 2 * ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2)) μ := i12.const_mul _
        rw [integral_add (i0.const_mul (1 + t)) i3, integral_const_mul, integral_const_mul,
          integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul]
      rw [(h _ (hu n) _ (hv n)).2, heq] at hle
      have b1 := (up (u n - x) (v n)).2
      have b2 := (up x (v n - y)).2
      have hpos : 0 ≤ 1 + 1 / t := by positivity
      have : (1 + 1 / t) * (2 * (∫ g, ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 ∂μ) + 2 * ∫ g, ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2 ∂μ) ≤
          (1 + 1 / t) * (2 * (‖u n - x‖ ^ 2 * ‖v n‖ ^ 2 / d) + 2 * (‖x‖ ^ 2 * ‖v n - y‖ ^ 2 / d)) :=
        mul_le_mul_of_nonneg_left (by linarith) hpos
      linarith
    have h0x : Tendsto (fun n => ‖u n - x‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hux
    have h0y : Tendsto (fun n => ‖v n - y‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hvy
    have hL : Tendsto (fun n => ‖u n‖ ^ 2 * ‖v n‖ ^ 2 / d) atTop (𝓝 (‖x‖ ^ 2 * ‖y‖ ^ 2 / d)) :=
      ((hux.norm.pow 2).mul (hvy.norm.pow 2)).div_const d
    have a1 := ((h0x.pow 2).mul (hvy.norm.pow 2)).div_const d
    have a2 := ((tendsto_const_nhds (x := ‖x‖ ^ 2) (f := atTop (α := ℕ))).mul (h0y.pow 2)).div_const d
    have hR : Tendsto (fun n => (1 + t) * N +
        (1 + 1 / t) * (2 * (‖u n - x‖ ^ 2 * ‖v n‖ ^ 2 / d) + 2 * (‖x‖ ^ 2 * ‖v n - y‖ ^ 2 / d))) atTop
        (𝓝 ((1 + t) * N + (1 + 1 / t) * (2 * ((0 : ℝ) ^ 2 * ‖y‖ ^ 2 / d) + 2 * (‖x‖ ^ 2 * (0 : ℝ) ^ 2 / d)))) :=
      tendsto_const_nhds.add (((a1.const_mul 2).add (a2.const_mul 2)).const_mul _)
    have hfin := le_of_tendsto_of_tendsto' hL hR hn
    simpa using hfin
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h1 := key (ε / (N + 1)) (by positivity)
  have h2 : ε / (N + 1) * N ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

end Dens

end Formalism.MainNotions.LeviCoordinates

end
