import Mathlib

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Measure Filter Topology
open scoped ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

variable {G : Type} [Group G] [MeasurableSpace G]

/- English proof (translation)
Establish `hsec : ∀ s, Measurable (f s)` using `fun s => hf.comp (by fun_prop : Measurable (fun s' : G => (s, s')))`. Establish `hin : ∀ s ∈ E, c * μS' E' ≤ ∫⁻ s', f s s' ∂μS'`. Introduce `s hs`. Combine the equalities or inequalities in the displayed calculation. Establish `hg : Measurable (fun s => ∫⁻ s', f s s' ∂μS')` using `hf.lintegral_prod_right'`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem lintegral_ge_rect {μS μS' : Measure G} [SFinite μS'] (f : G → G → ℝ≥0∞)
    (hf : Measurable (fun p : G × G => f p.1 p.2)) (E E' : Set G) (c : ℝ≥0∞)
    (h : ∀ s ∈ E, ∀ s' ∈ E', c ≤ f s s') : c * μS' E' * μS E ≤ ∫⁻ s, ∫⁻ s', f s s' ∂μS' ∂μS := by
  have hsec : ∀ s, Measurable (f s) := fun s =>
    hf.comp (by fun_prop : Measurable (fun s' : G => (s, s')))
  have hin : ∀ s ∈ E, c * μS' E' ≤ ∫⁻ s', f s s' ∂μS' := by
    intro s hs
    calc c * μS' E' ≤ c * μS' {s' | c ≤ f s s'} :=
          mul_le_mul' le_rfl (measure_mono fun s' hs' => h s hs s' hs')
      _ ≤ _ := mul_meas_ge_le_lintegral₀ (hsec s).aemeasurable c
  have hg : Measurable (fun s => ∫⁻ s', f s s' ∂μS') := hf.lintegral_prod_right'
  calc c * μS' E' * μS E ≤ c * μS' E' * μS {s | c * μS' E' ≤ ∫⁻ s', f s s' ∂μS'} :=
        mul_le_mul' le_rfl (measure_mono fun s hs => hin s hs)
    _ ≤ _ := mul_meas_ge_le_lintegral₀ hg.aemeasurable _

def folInt (Ω K : Set G) : Set G := {t | t ∈ Ω ∧ ∀ k ∈ K, k * t ∈ Ω}

/- English proof (translation)
Establish `e : (μS.map (MeasurableEquiv.inv G)) B = μS ((MeasurableEquiv.inv G) ⁻¹' B)` using `MeasurableEquiv.map_apply _ _`. Establish `hm : μS.map (MeasurableEquiv.inv G) = μS` using `hinv`. Rewrite `e` using `[hm]`. Conclude with `e.symm`.
-/
theorem measure_inv_preimage {μS : Measure G} [MeasurableInv G] (hinv : μS.map (fun x => x⁻¹) = μS)
    (B : Set G) : μS {s | s⁻¹ ∈ B} = μS B := by
  have e : (μS.map (MeasurableEquiv.inv G)) B = μS ((MeasurableEquiv.inv G) ⁻¹' B) :=
    MeasurableEquiv.map_apply _ _
  have hm : μS.map (MeasurableEquiv.inv G) = μS := hinv
  rw [hm] at e
  exact e.symm

/- English proof (translation)
Establish `hfin : ∀ n, a n / b n ≠ ⊤` using `fun n => ENNReal.div_ne_top (ne_top_of_le_ne_top (hbt n).ne (hab n)) (hb0 n).ne'`. Establish `hfun : (fun n => a n / b n) = fun n => ENNReal.ofReal ((a n).toReal / (b n).toReal)`. Use function extensionality and compare the values at `n`. Rewrite using `[← ENNReal.toReal_div, ENNReal.ofReal_toReal (hfin n)]`. Rewrite using `[hfun, ← ENNReal.ofReal_one]`.

Conclude with `ENNReal.tendsto_ofReal h`.
-/
theorem tendsto_ratio_ennreal {a b : ℕ → ℝ≥0∞} (hb0 : ∀ n, 0 < b n) (hbt : ∀ n, b n < ⊤)
    (hab : ∀ n, a n ≤ b n) (h : Tendsto (fun n => (a n).toReal / (b n).toReal) atTop (𝓝 1)) :
    Tendsto (fun n => a n / b n) atTop (𝓝 1) := by
  have hfin : ∀ n, a n / b n ≠ ⊤ := fun n =>
    ENNReal.div_ne_top (ne_top_of_le_ne_top (hbt n).ne (hab n)) (hb0 n).ne'
  have hfun : (fun n => a n / b n) = fun n => ENNReal.ofReal ((a n).toReal / (b n).toReal) := by
    funext n
    rw [← ENNReal.toReal_div, ENNReal.ofReal_toReal (hfin n)]
  rw [hfun, ← ENNReal.ofReal_one]
  exact ENNReal.tendsto_ofReal h

/- English proof (translation)
Use `set L := liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ * ∫⁻ s, ∫⁻ s', f n s s' ∂μS' ∂μS) atTop with hL`. Establish `step : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) ≤ L`. Introduce `ε hε`. Take `⟨K, K', hK, hK', hf'⟩` from `key ε hε`. Use `set c := ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) with hc`.

Establish `hlim : Tendsto (fun n => c * ((μS (folInt (Ω n) K) / μS (Ω n)) * (μS' (folInt (Ω' n) K') / μS' (Ω' n)))) atTop (𝓝 c)`. Establish `h1` using `ENNReal.Tendsto.mul hK (Or.inl one_ne_zero) hK' (Or.inl one_ne_zero)`. Establish `h2` using `ENNReal.Tendsto.const_mul h1 (a := c) (Or.inr ENNReal.ofReal_ne_top)`. Rewrite `h2` using `[mul_one, mul_one]`. Conclude with `h2`.

Rewrite using `[hL, ← hlim.liminf_eq]`. Use `liminf_le_liminf (Eventually.of_forall fun n => ?_)` and prove the remaining obligations. Establish `hA0` using `(hΩ0 n).ne'`. Establish `hAt` using `(hΩt n).ne`. Establish `hmain` using `lintegral_ge_rect (μS := μS) (μS' := μS') (f n) (hf n) {s | s⁻¹ ∈ folInt (Ω n) K} {s' | s'⁻¹ ∈ folInt (Ω' n) K'} c (fun s hs s' hs' => hf' n s s' hs hs')`.

Rewrite `hmain` using `[measure_inv_preimage hinv, measure_inv_preimage hinv']`. Rewrite using `[ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt), div_eq_mul_inv, div_eq_mul_inv]`. Combine the equalities or inequalities in the displayed calculation. Establish `hcont : Continuous (fun ε : ℝ => ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2))` using `ENNReal.continuous_ofReal.comp (((continuous_const.sub continuous_id).max continuous_const).pow 2)`. Establish `h0 : ENNReal.ofReal ((max (Real.sqrt h - 0) 0) ^ 2) = ENNReal.ofReal h`.

Rewrite using `[sub_zero, max_eq_left (Real.sqrt_nonneg h), Real.sq_sqrt hh]`. Establish `hg : Tendsto (fun ε : ℝ => ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal h))`. Rewrite using `[← h0]`. Conclude with `(hcont.tendsto 0).mono_left nhdsWithin_le_nhds`. Conclude with `le_of_tendsto hg (eventually_nhdsWithin_of_forall fun ε hε => step ε hε)`.
-/
theorem liminf_lower {μS μS' : Measure G} [SFinite μS'] [MeasurableInv G]
    (hinv : μS.map (fun x => x⁻¹) = μS) (hinv' : μS'.map (fun x => x⁻¹) = μS')
    (Ω Ω' : ℕ → Set G) (hΩ0 : ∀ n, 0 < μS (Ω n)) (hΩt : ∀ n, μS (Ω n) < ⊤)
    (hΩ0' : ∀ n, 0 < μS' (Ω' n)) (hΩt' : ∀ n, μS' (Ω' n) < ⊤)
    (f : ℕ → G → G → ℝ≥0∞) (hf : ∀ n, Measurable (fun p : G × G => f n p.1 p.2)) (h : ℝ) (hh : 0 ≤ h)
    (key : ∀ ε : ℝ, 0 < ε → ∃ K K' : Set G,
      Tendsto (fun n => μS (folInt (Ω n) K) / μS (Ω n)) atTop (𝓝 1) ∧
      Tendsto (fun n => μS' (folInt (Ω' n) K') / μS' (Ω' n)) atTop (𝓝 1) ∧
      ∀ n s s', s⁻¹ ∈ folInt (Ω n) K → s'⁻¹ ∈ folInt (Ω' n) K' →
        ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) ≤ f n s s') :
    ENNReal.ofReal h ≤
      liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ * ∫⁻ s, ∫⁻ s', f n s s' ∂μS' ∂μS) atTop := by
  set L := liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ * ∫⁻ s, ∫⁻ s', f n s s' ∂μS' ∂μS) atTop
    with hL
  have step : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) ≤ L := by
    intro ε hε
    obtain ⟨K, K', hK, hK', hf'⟩ := key ε hε
    set c := ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) with hc
    have hlim : Tendsto (fun n => c * ((μS (folInt (Ω n) K) / μS (Ω n)) *
        (μS' (folInt (Ω' n) K') / μS' (Ω' n)))) atTop (𝓝 c) := by
      have h1 := ENNReal.Tendsto.mul hK (Or.inl one_ne_zero) hK' (Or.inl one_ne_zero)
      have h2 := ENNReal.Tendsto.const_mul h1 (a := c) (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_one, mul_one] at h2
      exact h2
    rw [hL, ← hlim.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    have hA0 := (hΩ0 n).ne'
    have hAt := (hΩt n).ne
    have hmain := lintegral_ge_rect (μS := μS) (μS' := μS') (f n) (hf n)
      {s | s⁻¹ ∈ folInt (Ω n) K} {s' | s'⁻¹ ∈ folInt (Ω' n) K'} c
      (fun s hs s' hs' => hf' n s s' hs hs')
    rw [measure_inv_preimage hinv, measure_inv_preimage hinv'] at hmain
    rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt), div_eq_mul_inv, div_eq_mul_inv]
    calc c * (μS (folInt (Ω n) K) * (μS (Ω n))⁻¹ *
          (μS' (folInt (Ω' n) K') * (μS' (Ω' n))⁻¹))
        = (μS (Ω n))⁻¹ * (μS' (Ω' n))⁻¹ *
          (c * μS' (folInt (Ω' n) K') * μS (folInt (Ω n) K)) := by ring
      _ ≤ _ := mul_le_mul' le_rfl hmain
  have hcont : Continuous (fun ε : ℝ => ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2)) :=
    ENNReal.continuous_ofReal.comp (((continuous_const.sub continuous_id).max continuous_const).pow 2)
  have h0 : ENNReal.ofReal ((max (Real.sqrt h - 0) 0) ^ 2) = ENNReal.ofReal h := by
    rw [sub_zero, max_eq_left (Real.sqrt_nonneg h), Real.sq_sqrt hh]
  have hg : Tendsto (fun ε : ℝ => ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal h)) := by
    rw [← h0]
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hg (eventually_nhdsWithin_of_forall fun ε hε => step ε hε)

end Formalism.L2.S.Pv.EnergyAbs
