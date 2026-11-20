import Formalism.HermitianCurvature.StatementB

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P.B1

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

/- English proof (translation)
Introduce `V _ _ β hβ hnn x y`. Take `⟨ba1, ba2, bs1, bs2⟩` from `hβ`. Establish `hre : ∀ z, 0 ≤ (β z z).re`. Introduce `z`. Conclude with `(hnn z).2`.

Establish `hexp : ∀ t : ℝ, (β (x + ((-t : ℝ) : ℂ) • y) (x + ((-t : ℝ) : ℂ) • y)).re = (β y y).re * (t * t) + (-(β x y + β y x).re) * t + (β x x).re`. Introduce `t`. Simplify using `only [ba1, ba2, bs1, bs2, Complex.conj_ofReal, Complex.add_re, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hq : ∀ t : ℝ, 0 ≤ (β y y).re * (t * t) + (-(β x y + β y x).re) * t + (β x x).re`.

Introduce `t`. Rewrite using `[← hexp t]`. Conclude with `hre _`. Establish `hd` using `discrim_le_zero hq`. Simplify using `only [discrim] at hd`.

Establish `h1` using `hexp 1`. Rewrite using `[show x + ((-(1 : ℝ) : ℝ) : ℂ) • y = x - y by`. Rewrite `h1` using `[Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul, sub_eq_add_neg]]`. Rewrite using `[h1]`. Establish `ha` using `hre x`.

Establish `hb` using `hre y`. Establish `hsa` using `Real.sq_sqrt ha`. Establish `hsb` using `Real.sq_sqrt hb`. Establish `hpa` using `Real.sqrt_nonneg (β x x).re`. Establish `hpb` using `Real.sqrt_nonneg (β y y).re`.

Use polynomial arithmetic with `[mul_nonneg hpa hpb, sq_nonneg (Real.sqrt (β x x).re - Real.sqrt (β y y).re), sq_nonneg ((β x y + β y x).re + 2 * (Real.sqrt (β x x).re * Real.sqrt (β y y).re))]`.
-/
theorem semi : SeminormIneq := by
  intro V _ _ β hβ hnn x y
  obtain ⟨ba1, ba2, bs1, bs2⟩ := hβ
  have hre : ∀ z, 0 ≤ (β z z).re := by
    intro z
    exact (hnn z).2
  have hexp : ∀ t : ℝ, (β (x + ((-t : ℝ) : ℂ) • y) (x + ((-t : ℝ) : ℂ) • y)).re =
      (β y y).re * (t * t) + (-(β x y + β y x).re) * t + (β x x).re := by
    intro t
    simp only [ba1, ba2, bs1, bs2, Complex.conj_ofReal, Complex.add_re, Complex.re_ofReal_mul]
    ring
  have hq : ∀ t : ℝ, 0 ≤ (β y y).re * (t * t) + (-(β x y + β y x).re) * t + (β x x).re := by
    intro t
    rw [← hexp t]
    exact hre _
  have hd := discrim_le_zero hq
  simp only [discrim] at hd
  have h1 := hexp 1
  rw [show x + ((-(1 : ℝ) : ℝ) : ℂ) • y = x - y by
    rw [Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul, sub_eq_add_neg]] at h1
  rw [h1]
  have ha := hre x
  have hb := hre y
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hpa := Real.sqrt_nonneg (β x x).re
  have hpb := Real.sqrt_nonneg (β y y).re
  nlinarith [mul_nonneg hpa hpb, sq_nonneg (Real.sqrt (β x x).re - Real.sqrt (β y y).re),
    sq_nonneg ((β x y + β y x).re + 2 * (Real.sqrt (β x x).re * Real.sqrt (β y y).re))]

/- English proof (translation)
Introduce `V _ _ W β βi hβ hβi hnn hle hW`. Use `hpol V W β βi hβ hβi ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨Φ, c, t₀, _h0, hc0, hcc, hlim, U, hU, hae⟩` from `hW x hx`. Establish `hsq : ∀ t, (Real.sqrt (β (Φ t) (Φ t)).re - Real.sqrt (β x x).re) ^ 2 ≤ (βi (Φ t - x) (Φ t - x)).re` using `fun t => (hsemi V β hβ hnn (Φ t) x).trans (hle _)`.

Establish `hT1 : Tendsto (fun t => (Real.sqrt (β (Φ t) (Φ t)).re - Real.sqrt (β x x).re) ^ 2) (𝓝 t₀) (𝓝 0)` using `squeeze_zero (fun t => sq_nonneg _) hsq hlim`. Establish `hT2 : Tendsto (fun t => Real.sqrt (β (Φ t) (Φ t)).re) (𝓝 t₀) (𝓝 (Real.sqrt (β x x).re))`. Establish `h' : Tendsto (fun t => Real.sqrt (β (Φ t) (Φ t)).re - Real.sqrt (β x x).re) (𝓝 t₀) (𝓝 0)`. Establish `h2` using `hT1.sqrt`. Rewrite `h2` using `[Real.sqrt_zero]`.

Simplify using `only [Real.sqrt_sq_eq_abs] at h2`. Conclude with `(tendsto_zero_iff_abs_tendsto_zero _).mpr h2`. Simplify using `using h'.add_const (Real.sqrt (β x x).re)`. Establish `e : ∀ t, Real.sqrt (β (Φ t) (Φ t)).re ^ 2 = (β (Φ t) (Φ t)).re` using `fun t => Real.sq_sqrt (hnn _).2`. Establish `hT3 : Tendsto (fun t => (β (Φ t) (Φ t)).re) (𝓝 t₀) (𝓝 (β x x).re)`.

Simplify `hT2.pow 2` using `only [e, Real.sq_sqrt (hnn x).2]`. Establish `hNe : (ae (volume.restrict U) ⊓ 𝓝 t₀).NeBot`. Rewrite using `[Filter.inf_neBot_iff]`. Introduce `s₁ hs₁ s₂ hs₂`. Assume the negation of the conclusion as `hemp`.

Rewrite `hemp` using `[Set.not_nonempty_iff_eq_empty]`. Establish `hO : t₀ ∈ interior (s₂ ∩ U)` using `mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hs₂ hU)`. Establish `hpos : 0 < volume (interior (s₂ ∩ U))` using `isOpen_interior.measure_pos volume ⟨t₀, hO⟩`. Establish `hsub : interior (s₂ ∩ U) ⊆ s₁ᶜ`. Introduce `t ht hts`.

Establish `hmem : t ∈ s₁ ∩ s₂` using `⟨hts, (interior_subset ht).1⟩`. Rewrite `hmem` using `[hemp]`. Conclude with `hmem`. Establish `h0' : volume.restrict U s₁ᶜ = 0` using `mem_ae_iff.mp hs₁`. Establish `hle2 : volume.restrict U (interior (s₂ ∩ U)) ≤ volume.restrict U s₁ᶜ` using `measure_mono hsub`.

Rewrite `hle2` using `[h0', Measure.restrict_apply isOpen_interior.measurableSet, Set.inter_eq_left.mpr (interior_subset.trans Set.inter_subset_right)]`. Conclude with `lt_irrefl _ (hpos.trans_le hle2)`. Establish `hcL : Tendsto c (ae (volume.restrict U) ⊓ 𝓝 t₀) (𝓝 (βi x x))`. Rewrite using `[← hc0]`. Conclude with `hcc.tendsto.mono_left inf_le_right`.

Establish `hbL : Tendsto (fun t => β (Φ t) (Φ t)) (ae (volume.restrict U) ⊓ 𝓝 t₀) (𝓝 (βi x x))` using `hcL.congr' ((Filter.Eventually.filter_mono inf_le_left hae).mono fun t ht => ht.symm)`. Establish `hre : (β x x).re = (βi x x).re` using `tendsto_nhds_unique (hT3.mono_left inf_le_right) ((Complex.continuous_re.tendsto _).comp hbL)`. Establish `him : (0 : ℝ) = (βi x x).im`. Establish `e2 : (fun t => (β (Φ t) (Φ t)).im) = fun _ => (0 : ℝ)` using `funext fun t => (hnn (Φ t)).1`. Establish `h1 : Tendsto (fun t => (β (Φ t) (Φ t)).im) (ae (volume.restrict U) ⊓ 𝓝 t₀) (𝓝 0)`.

Rewrite using `[e2]`. Conclude with `tendsto_const_nhds`. Conclude with `tendsto_nhds_unique h1 ((Complex.continuous_im.tendsto _).comp hbL)`. Conclude with `Complex.ext hre (by rw [(hnn x).1, ← him])`.
-/
theorem core (hsemi : SeminormIneq) (hpol : Polarisation) : FormCoreC := by
  intro V _ _ W β βi hβ hβi hnn hle hW
  refine hpol V W β βi hβ hβi ?_
  intro x hx
  obtain ⟨Φ, c, t₀, _h0, hc0, hcc, hlim, U, hU, hae⟩ := hW x hx
  have hsq : ∀ t, (Real.sqrt (β (Φ t) (Φ t)).re - Real.sqrt (β x x).re) ^ 2 ≤
      (βi (Φ t - x) (Φ t - x)).re :=
    fun t => (hsemi V β hβ hnn (Φ t) x).trans (hle _)
  have hT1 : Tendsto (fun t => (Real.sqrt (β (Φ t) (Φ t)).re - Real.sqrt (β x x).re) ^ 2)
      (𝓝 t₀) (𝓝 0) :=
    squeeze_zero (fun t => sq_nonneg _) hsq hlim
  have hT2 : Tendsto (fun t => Real.sqrt (β (Φ t) (Φ t)).re) (𝓝 t₀)
      (𝓝 (Real.sqrt (β x x).re)) := by
    have h' : Tendsto (fun t => Real.sqrt (β (Φ t) (Φ t)).re - Real.sqrt (β x x).re) (𝓝 t₀)
        (𝓝 0) := by
      have h2 := hT1.sqrt
      rw [Real.sqrt_zero] at h2
      simp only [Real.sqrt_sq_eq_abs] at h2
      exact (tendsto_zero_iff_abs_tendsto_zero _).mpr h2
    simpa using h'.add_const (Real.sqrt (β x x).re)
  have e : ∀ t, Real.sqrt (β (Φ t) (Φ t)).re ^ 2 = (β (Φ t) (Φ t)).re :=
    fun t => Real.sq_sqrt (hnn _).2
  have hT3 : Tendsto (fun t => (β (Φ t) (Φ t)).re) (𝓝 t₀) (𝓝 (β x x).re) := by
    simpa only [e, Real.sq_sqrt (hnn x).2] using hT2.pow 2
  have hNe : (ae (volume.restrict U) ⊓ 𝓝 t₀).NeBot := by
    rw [Filter.inf_neBot_iff]
    intro s₁ hs₁ s₂ hs₂
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hO : t₀ ∈ interior (s₂ ∩ U) := mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hs₂ hU)
    have hpos : 0 < volume (interior (s₂ ∩ U)) := isOpen_interior.measure_pos volume ⟨t₀, hO⟩
    have hsub : interior (s₂ ∩ U) ⊆ s₁ᶜ := by
      intro t ht hts
      have hmem : t ∈ s₁ ∩ s₂ := ⟨hts, (interior_subset ht).1⟩
      rw [hemp] at hmem
      exact hmem
    have h0' : volume.restrict U s₁ᶜ = 0 := mem_ae_iff.mp hs₁
    have hle2 : volume.restrict U (interior (s₂ ∩ U)) ≤ volume.restrict U s₁ᶜ := measure_mono hsub
    rw [h0', Measure.restrict_apply isOpen_interior.measurableSet,
      Set.inter_eq_left.mpr (interior_subset.trans Set.inter_subset_right)] at hle2
    exact lt_irrefl _ (hpos.trans_le hle2)
  have hcL : Tendsto c (ae (volume.restrict U) ⊓ 𝓝 t₀) (𝓝 (βi x x)) := by
    rw [← hc0]
    exact hcc.tendsto.mono_left inf_le_right
  have hbL : Tendsto (fun t => β (Φ t) (Φ t)) (ae (volume.restrict U) ⊓ 𝓝 t₀) (𝓝 (βi x x)) :=
    hcL.congr' ((Filter.Eventually.filter_mono inf_le_left hae).mono fun t ht => ht.symm)
  have hre : (β x x).re = (βi x x).re :=
    tendsto_nhds_unique (hT3.mono_left inf_le_right) ((Complex.continuous_re.tendsto _).comp hbL)
  have him : (0 : ℝ) = (βi x x).im := by
    have e2 : (fun t => (β (Φ t) (Φ t)).im) = fun _ => (0 : ℝ) := funext fun t => (hnn (Φ t)).1
    have h1 : Tendsto (fun t => (β (Φ t) (Φ t)).im) (ae (volume.restrict U) ⊓ 𝓝 t₀) (𝓝 0) := by
      rw [e2]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 ((Complex.continuous_im.tendsto _).comp hbL)
  exact Complex.ext hre (by rw [(hnn x).1, ← him])

/- English proof (translation)
Introduce `V _ _ W β γ hβ hγ hW x hx y hy`. Take `⟨ba1, ba2, bs1, bs2⟩` from `hβ`. Take `⟨ga1, ga2, gs1, gs2⟩` from `hγ`. Establish `hxy` using `hW (x + y) (W.add_mem hx hy)`. Establish `hxiy` using `hW (x + Complex.I • y) (W.add_mem hx (W.smul_mem _ hy))`.

Establish `hxx` using `hW x hx`. Establish `hyy` using `hW y hy`. Simplify using `only [ba1, ba2, ga1, ga2] at hxy`. Simplify using `only [ba1, ba2, bs1, bs2, ga1, ga2, gs1, gs2, Complex.conj_I] at hxiy`. Take the linear combination `(1 / 2 : ℂ) * (hxy - hxx - hyy) + (Complex.I / 2) * (hxiy - hxx + Complex.I ^ 2 * hyy) - ((β y x - γ y x - (β x y - γ x y)) / 2) * Complex.I_sq`.
-/
theorem polar : Polarisation := by
  intro V _ _ W β γ hβ hγ hW x hx y hy
  obtain ⟨ba1, ba2, bs1, bs2⟩ := hβ
  obtain ⟨ga1, ga2, gs1, gs2⟩ := hγ
  have hxy := hW (x + y) (W.add_mem hx hy)
  have hxiy := hW (x + Complex.I • y) (W.add_mem hx (W.smul_mem _ hy))
  have hxx := hW x hx
  have hyy := hW y hy
  simp only [ba1, ba2, ga1, ga2] at hxy
  simp only [ba1, ba2, bs1, bs2, ga1, ga2, gs1, gs2, Complex.conj_I] at hxiy
  linear_combination (1 / 2 : ℂ) * (hxy - hxx - hyy) +
    (Complex.I / 2) * (hxiy - hxx + Complex.I ^ 2 * hyy) -
    ((β y x - γ y x - (β x y - γ x y)) / 2) * Complex.I_sq

/- English proof (translation)
The claim follows from `core semi polar`.
-/
theorem coreC : FormCoreC := core semi polar

/- English proof (translation)
Introduce `V _ _ W β βi hβ hβi hnn hle hW`. Use `coreC V W β βi hβ hβi hnn hle ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨Φ, t₀, h0, hc, ht, U, hU, hae⟩` from `hW x hx`. Conclude with `⟨Φ, fun t => βi (Φ t) (Φ t), t₀, h0, by simp only [h0], hc, ht, U, hU, hae⟩`.
-/
theorem core0 : FormCore := by
  intro V _ _ W β βi hβ hβi hnn hle hW
  refine coreC V W β βi hβ hβi hnn hle ?_
  intro x hx
  obtain ⟨Φ, t₀, h0, hc, ht, U, hU, hae⟩ := hW x hx
  exact ⟨Φ, fun t => βi (Φ t) (Φ t), t₀, h0, by simp only [h0], hc, ht, U, hU, hae⟩

/- English proof (translation)
Introduce `Q _ μ E _ U J c hU hJm hJc hc hae τ hτ`. Establish `hNe : (ae (volume.restrict U) ⊓ 𝓝 τ).NeBot`. Rewrite using `[Filter.inf_neBot_iff]`. Introduce `s₁ hs₁ s₂ hs₂`. Assume the negation of the conclusion as `hemp`.

Rewrite `hemp` using `[Set.not_nonempty_iff_eq_empty]`. Establish `hO : τ ∈ interior (s₂ ∩ U)` using `mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hs₂ (hU.mem_nhds hτ))`. Establish `hpos : 0 < volume (interior (s₂ ∩ U))` using `isOpen_interior.measure_pos volume ⟨τ, hO⟩`. Establish `hsub : interior (s₂ ∩ U) ⊆ s₁ᶜ`. Introduce `t ht hts`.

Establish `hmem : t ∈ s₁ ∩ s₂` using `⟨hts, (interior_subset ht).1⟩`. Rewrite `hmem` using `[hemp]`. Conclude with `hmem`. Establish `h0' : volume.restrict U s₁ᶜ = 0` using `mem_ae_iff.mp hs₁`. Establish `hle2 : volume.restrict U (interior (s₂ ∩ U)) ≤ volume.restrict U s₁ᶜ` using `measure_mono hsub`.

Rewrite `hle2` using `[h0', Measure.restrict_apply isOpen_interior.measurableSet, Set.inter_eq_left.mpr (interior_subset.trans Set.inter_subset_right)]`. Conclude with `lt_irrefl _ (hpos.trans_le hle2)`. Establish `hex : ∀ n : ℕ, ∃ σ, σ ∈ Metric.ball τ (1 / ((n : ℝ) + 1)) ∩ U ∧ ∫⁻ q, ‖J σ q‖ₑ ^ 2 ∂μ = ENNReal.ofReal (c σ)`. Introduce `n`. Establish `h1 : Metric.ball τ (1 / ((n : ℝ) + 1)) ∩ U ∈ 𝓝 τ` using `Filter.inter_mem (Metric.ball_mem_nhds τ (by positivity)) (hU.mem_nhds hτ)`.

Take `⟨σ, hσ1, hσ2⟩` from `Filter.inf_neBot_iff.mp hNe hae h1`. Conclude with `⟨σ, hσ2, hσ1⟩`. Use `choose σ hσ hσeq using hex`. Establish `hσT : Tendsto σ atTop (𝓝 τ)`. Rewrite using `[tendsto_iff_dist_tendsto_zero]`.

Use `squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat` and prove the remaining obligations. Conclude with `(Metric.mem_ball.mp (hσ n).1).le`. Establish `hσW : Tendsto σ atTop (𝓝[U] τ)` using `tendsto_nhdsWithin_iff.mpr ⟨hσT, Filter.Eventually.of_forall fun n => (hσ n).2⟩`. Establish `hpt : ∀ᵐ q ∂μ, Tendsto (fun n => ‖J (σ n) q‖ₑ ^ 2) atTop (𝓝 (‖J τ q‖ₑ ^ 2))` using `by filter_upwards [hJc] with q hq`. Establish `h2` using `((hq τ hτ).tendsto).comp hσW`.

Conclude with `((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp h2)`. Establish `hcT : Tendsto (fun n => ENNReal.ofReal (c (σ n))) atTop (𝓝 (ENNReal.ofReal (c τ)))` using `(ENNReal.continuous_ofReal.tendsto _).comp ((hc τ hτ).tendsto.comp hσW)`. Combine the equalities or inequalities in the displayed calculation. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hpt] with q hq`.

Conclude with `hq.liminf_eq.symm`. Use `_ ≤ liminf (fun n => ∫⁻ q, ‖J (σ n) q‖ₑ ^ 2 ∂μ) atTop := by`. Apply `lintegral_liminf_le'` to reduce the goal to its premises. Introduce `n`. Conclude with `((hJm (σ n) (hσ n).2).enorm).pow_const 2`.

Use `_ = liminf (fun n => ENNReal.ofReal (c (σ n))) atTop := by`. Simplify using `only [hσeq]`. Use `_ = ENNReal.ofReal (c τ) := hcT.liminf_eq`.
-/
theorem fatou : FatouParam := by
  intro Q _ μ E _ U J c hU hJm hJc hc hae τ hτ
  have hNe : (ae (volume.restrict U) ⊓ 𝓝 τ).NeBot := by
    rw [Filter.inf_neBot_iff]
    intro s₁ hs₁ s₂ hs₂
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hO : τ ∈ interior (s₂ ∩ U) :=
      mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hs₂ (hU.mem_nhds hτ))
    have hpos : 0 < volume (interior (s₂ ∩ U)) := isOpen_interior.measure_pos volume ⟨τ, hO⟩
    have hsub : interior (s₂ ∩ U) ⊆ s₁ᶜ := by
      intro t ht hts
      have hmem : t ∈ s₁ ∩ s₂ := ⟨hts, (interior_subset ht).1⟩
      rw [hemp] at hmem
      exact hmem
    have h0' : volume.restrict U s₁ᶜ = 0 := mem_ae_iff.mp hs₁
    have hle2 : volume.restrict U (interior (s₂ ∩ U)) ≤ volume.restrict U s₁ᶜ := measure_mono hsub
    rw [h0', Measure.restrict_apply isOpen_interior.measurableSet,
      Set.inter_eq_left.mpr (interior_subset.trans Set.inter_subset_right)] at hle2
    exact lt_irrefl _ (hpos.trans_le hle2)
  have hex : ∀ n : ℕ, ∃ σ, σ ∈ Metric.ball τ (1 / ((n : ℝ) + 1)) ∩ U ∧
      ∫⁻ q, ‖J σ q‖ₑ ^ 2 ∂μ = ENNReal.ofReal (c σ) := by
    intro n
    have h1 : Metric.ball τ (1 / ((n : ℝ) + 1)) ∩ U ∈ 𝓝 τ :=
      Filter.inter_mem (Metric.ball_mem_nhds τ (by positivity)) (hU.mem_nhds hτ)
    obtain ⟨σ, hσ1, hσ2⟩ := Filter.inf_neBot_iff.mp hNe hae h1
    exact ⟨σ, hσ2, hσ1⟩
  choose σ hσ hσeq using hex
  have hσT : Tendsto σ atTop (𝓝 τ) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    exact (Metric.mem_ball.mp (hσ n).1).le
  have hσW : Tendsto σ atTop (𝓝[U] τ) :=
    tendsto_nhdsWithin_iff.mpr ⟨hσT, Filter.Eventually.of_forall fun n => (hσ n).2⟩
  have hpt : ∀ᵐ q ∂μ, Tendsto (fun n => ‖J (σ n) q‖ₑ ^ 2) atTop (𝓝 (‖J τ q‖ₑ ^ 2)) := by
    filter_upwards [hJc] with q hq
    have h2 := ((hq τ hτ).tendsto).comp hσW
    exact ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp h2)
  have hcT : Tendsto (fun n => ENNReal.ofReal (c (σ n))) atTop (𝓝 (ENNReal.ofReal (c τ))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((hc τ hτ).tendsto.comp hσW)
  calc ∫⁻ q, ‖J τ q‖ₑ ^ 2 ∂μ = ∫⁻ q, liminf (fun n => ‖J (σ n) q‖ₑ ^ 2) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hpt] with q hq
        exact hq.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ q, ‖J (σ n) q‖ₑ ^ 2 ∂μ) atTop := by
        apply lintegral_liminf_le'
        intro n
        exact ((hJm (σ n) (hσ n).2).enorm).pow_const 2
    _ = liminf (fun n => ENNReal.ofReal (c (σ n))) atTop := by
        simp only [hσeq]
    _ = ENNReal.ofReal (c τ) := hcT.liminf_eq

/- English proof (translation)
Introduce `h hh hc x`. Use `set e : ℝ → ℂ := fun t => Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) with he`. Establish `hed : ∀ t, HasDerivAt e (Complex.I * x * e t) t`. Introduce `t`. Establish `h1 : HasDerivAt (fun t : ℝ => Complex.I * ((x * t : ℝ) : ℂ)) (Complex.I * x) t`.

Establish `h2 : HasDerivAt (fun t : ℝ => ((x * t : ℝ) : ℂ)) ((x : ℝ) : ℂ) t`. Use `((hasDerivAt_id t).const_mul x).ofReal_comp` as an intermediate fact. Simplify using `using this`. Conclude with `h2.const_mul _`. Use `h1.cexp` as an intermediate fact.

Simplify `this` using `[he, mul_comm, mul_left_comm, mul_assoc]`. Establish `hec : Continuous e`. Rewrite using `[he]`. Use `fun_prop`. Establish `hd1 : ContDiff ℝ 1 (deriv h)`.

Establish `: ContDiff ℝ (1 + 1) h` using `by simpa [one_add_one_eq_two] using hh`. Conclude with `((contDiff_succ_iff_deriv).1 this).2.2`. Establish `hh0 : Differentiable ℝ h` using `hh.differentiable (by norm_num)`. Establish `hh1 : Differentiable ℝ (deriv h)` using `hd1.differentiable (by norm_num)`. Establish `c0 : Continuous h` using `hh.continuous`.

Establish `c1 : Continuous (deriv h)` using `hd1.continuous`. Establish `c2 : Continuous (deriv (deriv h))` using `hd1.continuous_deriv (le_refl _)`. Establish `k1 : HasCompactSupport (deriv h)` using `hc.deriv`. Establish `k2 : HasCompactSupport (deriv (deriv h))` using `k1.deriv`. Establish `i2 : iteratedDeriv 2 h = deriv (deriv h)`.

Rewrite using `[iteratedDeriv_succ, iteratedDeriv_one]`. Establish `I0 : Integrable (fun t => e t * h t)` using `(hec.mul c0).integrable_of_hasCompactSupport hc.mul_left`. Establish `I1 : Integrable (fun t => e t * deriv h t)` using `(hec.mul c1).integrable_of_hasCompactSupport k1.mul_left`. Establish `I2 : Integrable (fun t => e t * deriv (deriv h) t)` using `(hec.mul c2).integrable_of_hasCompactSupport k2.mul_left`. Establish `J0 : Integrable (fun t => (Complex.I * x * e t) * h t)`.

Simplify `I0.const_mul (Complex.I * x)` using `[mul_assoc]`. Establish `J1 : Integrable (fun t => (Complex.I * x * e t) * deriv h t)`. Simplify `I1.const_mul (Complex.I * x)` using `[mul_assoc]`. Establish `s1 : (∫ t, e t * deriv (deriv h) t) = - ∫ t, (Complex.I * x * e t) * deriv h t` using `integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hed t) (fun t _ => (hh1 t).hasDerivAt) I2 J1 I1`. Establish `s2 : (∫ t, e t * deriv h t) = - ∫ t, (Complex.I * x * e t) * h t` using `integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hed t) (fun t _ => (hh0 t).hasDerivAt) I1 J0 I0`.

Establish `m1 : (∫ t, (Complex.I * x * e t) * deriv h t) = Complex.I * x * ∫ t, e t * deriv h t`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Expand and normalize the polynomial expressions, which then agree.

Establish `m0 : (∫ t, (Complex.I * x * e t) * h t) = Complex.I * x * ∫ t, e t * h t`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Expand and normalize the polynomial expressions, which then agree.

Establish `l : (∫ t : ℝ, (h t - iteratedDeriv 2 h t) * e t) = (∫ t, e t * h t) - ∫ t, e t * deriv (deriv h) t`. Rewrite using `[← integral_sub I0 I2, i2]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Expand and normalize the polynomial expressions, which then agree.

Establish `r : (∫ t : ℝ, h t * e t) = ∫ t, e t * h t` using `by congr 1; funext t; ring`. Rewrite using `[l, r, s1, m1, s2, m0]`. Use `push_cast`. Take the linear combination `(-(x:ℂ)^2 * ∫ t, e t * h t) * Complex.I_mul_I`.
-/
theorem ibp : RegIBP := by
  intro h hh hc x
  set e : ℝ → ℂ := fun t => Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) with he
  have hed : ∀ t, HasDerivAt e (Complex.I * x * e t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.I * ((x * t : ℝ) : ℂ)) (Complex.I * x) t := by
      have h2 : HasDerivAt (fun t : ℝ => ((x * t : ℝ) : ℂ)) ((x : ℝ) : ℂ) t := by
        have := ((hasDerivAt_id t).const_mul x).ofReal_comp
        simpa using this
      exact h2.const_mul _
    have := h1.cexp
    simpa [he, mul_comm, mul_left_comm, mul_assoc] using this
  have hec : Continuous e := by
    rw [he]; fun_prop
  have hd1 : ContDiff ℝ 1 (deriv h) := by
    have : ContDiff ℝ (1 + 1) h := by simpa [one_add_one_eq_two] using hh
    exact ((contDiff_succ_iff_deriv).1 this).2.2
  have hh0 : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hh1 : Differentiable ℝ (deriv h) := hd1.differentiable (by norm_num)
  have c0 : Continuous h := hh.continuous
  have c1 : Continuous (deriv h) := hd1.continuous
  have c2 : Continuous (deriv (deriv h)) := hd1.continuous_deriv (le_refl _)
  have k1 : HasCompactSupport (deriv h) := hc.deriv
  have k2 : HasCompactSupport (deriv (deriv h)) := k1.deriv
  have i2 : iteratedDeriv 2 h = deriv (deriv h) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have I0 : Integrable (fun t => e t * h t) := (hec.mul c0).integrable_of_hasCompactSupport hc.mul_left
  have I1 : Integrable (fun t => e t * deriv h t) := (hec.mul c1).integrable_of_hasCompactSupport k1.mul_left
  have I2 : Integrable (fun t => e t * deriv (deriv h) t) := (hec.mul c2).integrable_of_hasCompactSupport k2.mul_left
  have J0 : Integrable (fun t => (Complex.I * x * e t) * h t) := by
    simpa [mul_assoc] using I0.const_mul (Complex.I * x)
  have J1 : Integrable (fun t => (Complex.I * x * e t) * deriv h t) := by
    simpa [mul_assoc] using I1.const_mul (Complex.I * x)
  have s1 : (∫ t, e t * deriv (deriv h) t) = - ∫ t, (Complex.I * x * e t) * deriv h t :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hed t) (fun t _ => (hh1 t).hasDerivAt) I2 J1 I1
  have s2 : (∫ t, e t * deriv h t) = - ∫ t, (Complex.I * x * e t) * h t :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hed t) (fun t _ => (hh0 t).hasDerivAt) I1 J0 I0
  have m1 : (∫ t, (Complex.I * x * e t) * deriv h t) = Complex.I * x * ∫ t, e t * deriv h t := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  have m0 : (∫ t, (Complex.I * x * e t) * h t) = Complex.I * x * ∫ t, e t * h t := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  have l : (∫ t : ℝ, (h t - iteratedDeriv 2 h t) * e t) = (∫ t, e t * h t) - ∫ t, e t * deriv (deriv h) t := by
    rw [← integral_sub I0 I2, i2]; congr 1; funext t; ring
  have r : (∫ t : ℝ, h t * e t) = ∫ t, e t * h t := by congr 1; funext t; ring
  rw [l, r, s1, m1, s2, m0]
  push_cast
  linear_combination (-(x:ℂ)^2 * ∫ t, e t * h t) * Complex.I_mul_I

/- English proof (translation)
Unfold `TestDecay`. Unfold `RegIBP at hibp`. Introduce `wh hwh`. Unfold `om`. Unfold `IsTest at hwh`.

Take `⟨hcd, hcs, _⟩` from `hwh`. Establish `hcd' : ContDiff ℝ 2 (fun t : ℝ => (wh t : ℂ))` using `by first`. Consider the case `exact Complex.ofRealCLM.contDiff.comp hcd`. Consider the case `fun_prop`. Establish `hcs' : HasCompactSupport (fun t : ℝ => (wh t : ℂ))` using `hcs.comp_left Complex.ofReal_zero`.

Establish `hgc : Continuous (fun t : ℝ => (wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t)` using `hcd'.continuous.sub (hcd'.continuous_iteratedDeriv 2 (by norm_num))`. Establish `hgs : HasCompactSupport (fun t : ℝ => (wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t)` using `hcs'.sub (by first`. Consider the case `(rw [iteratedDeriv_succ, iteratedDeriv_one]; exact hcs'.deriv.deriv)`. Consider the case `(rw [iteratedDeriv_eq_iterate]; exact hcs'.deriv.deriv)`. Consider the case `exact hcs'.iteratedDeriv 2)`.

Establish `hn : ∀ y : ℝ, ‖Complex.exp (Complex.I * (y : ℂ))‖ = 1` using `fun y => by`. Rewrite using `[Complex.norm_exp]`. Simplify using the standard rewrite rules. Use `⟨2 * ∫ t, ‖(wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t‖, fun x => ?_⟩` and prove the remaining obligations. Establish `key` using `hibp (fun t : ℝ => (wh t : ℂ)) hcd' hcs' x`.

Use `beta_reduce at key`. Establish `hpos : (0 : ℝ) < 1 + x ^ 2` using `by positivity`. Establish `hbound : ‖∫ t, ((wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t) * Complex.exp (Complex.I * ↑(x * t))‖ ≤ ∫ t, ‖(wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t‖`. Use `(norm_integral_le_integral_norm _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`.

Use function extensionality and compare the values at `t`. Rewrite using `[norm_mul, hn, mul_one]`. Establish `e2 : ∫ τ, (wh τ : ℂ) * Complex.exp (Complex.I * ↑(τ * x)) = ∫ t, (wh t : ℂ) * Complex.exp (Complex.I * ↑(x * t))`. Use `congr 1`. Use function extensionality and compare the values at `t`.

Rewrite using `[mul_comm t x]`. Rewrite using `[e2]`. Establish `hI : ‖∫ t, (wh t : ℂ) * Complex.exp (Complex.I * ↑(x * t))‖ * (1 + x ^ 2) ≤ ∫ t, ‖(wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t‖`. Establish `h3` using `congrArg norm key`. Rewrite `h3` using `[norm_mul, Complex.norm_of_nonneg hpos.le]`.

Rewrite using `[mul_comm, ← h3]`. Conclude with `hbound`. Establish `hsq : (1 + |x|) ^ 2 ≤ 2 * (1 + x ^ 2)`. Use polynomial arithmetic with `[sq_abs x, abs_nonneg x, sq_nonneg (|x| - 1)]`. Establish `hq : 0 < (1 + |x|) ^ 2` using `by positivity`.

Rewrite using `[← div_eq_mul_inv, le_div_iff₀ hq]`. Establish `hm` using `mul_le_mul_of_nonneg_left hsq (norm_nonneg (∫ t, (wh t : ℂ) * Complex.exp (Complex.I * ↑(x * t))))`. Use polynomial arithmetic with `[hI, hm]`.
-/
theorem decay (hibp : RegIBP) : TestDecay := by
  unfold TestDecay
  unfold RegIBP at hibp
  intro wh hwh
  unfold om
  unfold IsTest at hwh
  obtain ⟨hcd, hcs, _⟩ := hwh
  have hcd' : ContDiff ℝ 2 (fun t : ℝ => (wh t : ℂ)) := by
    first
    | exact Complex.ofRealCLM.contDiff.comp hcd
    | fun_prop
  have hcs' : HasCompactSupport (fun t : ℝ => (wh t : ℂ)) := hcs.comp_left Complex.ofReal_zero
  have hgc : Continuous (fun t : ℝ => (wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t) :=
    hcd'.continuous.sub (hcd'.continuous_iteratedDeriv 2 (by norm_num))
  have hgs : HasCompactSupport
      (fun t : ℝ => (wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t) :=
    hcs'.sub (by
      first
      | (rw [iteratedDeriv_succ, iteratedDeriv_one]; exact hcs'.deriv.deriv)
      | (rw [iteratedDeriv_eq_iterate]; exact hcs'.deriv.deriv)
      | exact hcs'.iteratedDeriv 2)
  have hn : ∀ y : ℝ, ‖Complex.exp (Complex.I * (y : ℂ))‖ = 1 := fun y => by
    rw [Complex.norm_exp]
    simp
  refine ⟨2 * ∫ t, ‖(wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t‖, fun x => ?_⟩
  have key := hibp (fun t : ℝ => (wh t : ℂ)) hcd' hcs' x
  beta_reduce at key
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hbound : ‖∫ t, ((wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t) *
      Complex.exp (Complex.I * ↑(x * t))‖ ≤
      ∫ t, ‖(wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext t
    rw [norm_mul, hn, mul_one]
  have e2 : ∫ τ, (wh τ : ℂ) * Complex.exp (Complex.I * ↑(τ * x)) =
      ∫ t, (wh t : ℂ) * Complex.exp (Complex.I * ↑(x * t)) := by
    congr 1
    funext t
    rw [mul_comm t x]
  rw [e2]
  have hI : ‖∫ t, (wh t : ℂ) * Complex.exp (Complex.I * ↑(x * t))‖ * (1 + x ^ 2) ≤
      ∫ t, ‖(wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t‖ := by
    have h3 := congrArg norm key
    rw [norm_mul, Complex.norm_of_nonneg hpos.le] at h3
    rw [mul_comm, ← h3]
    exact hbound
  have hsq : (1 + |x|) ^ 2 ≤ 2 * (1 + x ^ 2) := by
    nlinarith [sq_abs x, abs_nonneg x, sq_nonneg (|x| - 1)]
  have hq : 0 < (1 + |x|) ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hq]
  have hm := mul_le_mul_of_nonneg_left hsq
    (norm_nonneg (∫ t, (wh t : ℂ) * Complex.exp (Complex.I * ↑(x * t))))
  nlinarith [hI, hm]

/- English proof (translation)
Introduce `n μ _ X h hinv hC1 hI hRI`. Use `set E : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => NormedSpace.exp ((t : ℂ) • X) with hE`. Establish `hEcont : Continuous E`. Use `letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra`.

Use `letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _`. Establish `h1 : Continuous fun t : ℝ => ((t : ℂ) • X)` using `by fun_prop`. Conclude with `NormedSpace.exp_continuous.comp h1`. Establish `hEadd : ∀ s t : ℝ, E (s + t) = E s * E t`. Introduce `s t`.

Simplify using `only [hE]`. Rewrite using `[← Matrix.exp_add_of_commute]`. Use `congr 1`. Use `push_cast`. Rewrite using `[add_smul]`.

Conclude with `((Commute.refl X).smul_left _).smul_right _`. Establish `hE0 : E 0 = 1` using `by simp [hE]`. Use `set k : (Fin n → Fin n → ℂ) → ℂ := fun g => RdV X h (Matrix.of g) with hk`. Use `set Ψ : (Fin n → Fin n → ℂ) × ℝ → (Fin n → Fin n → ℂ) := fun p => rmulF (E p.2) p.1 with hΨd`. Establish `hΨc : Continuous Ψ`.

Establish `: Continuous fun p : (Fin n → Fin n → ℂ) × ℝ => (Matrix.of p.1 : Matrix (Fin n) (Fin n) ℂ) * E p.2` using `Continuous.matrix_mul continuous_fst (hEcont.comp continuous_snd)`. Conclude with `this`. Establish `hΨ : Measurable Ψ` using `hΨc.measurable`. Establish `hR : ∀ s : ℝ, Measurable (rmulF (E s))` using `fun s => hΨ.comp measurable_prodMk_right`. Use `set ν : Measure ℝ := volume.restrict (Set.Ioc 0 1) with hν`.

Establish `hq : Measure.QuasiMeasurePreserving Ψ (μ.prod ν) μ`. Use `⟨hΨ, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply hΨ hs, Measure.prod_apply_symm (hΨ hs)]`. Establish `: ∀ y : ℝ, μ ((fun x => (x, y)) ⁻¹' (Ψ ⁻¹' s)) = 0`. Introduce `y`.

Establish `e : (fun x => (x, y)) ⁻¹' (Ψ ⁻¹' s) = rmulF (E y) ⁻¹' s` using `rfl`. Rewrite using `[e, ← Measure.map_apply (hR y) hs, hinv y, h0]`. Simplify using `[this]`. Establish `hkR : ∀ s : ℝ, Integrable (fun g => k (rmulF (E s) g)) μ`. Introduce `s`.

Establish `: Integrable k (μ.map (rmulF (E s)))` using `by rw [hinv s]; exact hRI`. Conclude with `this.comp_measurable (hR s)`. Establish `hkI : ∀ s : ℝ, (∫ g, k (rmulF (E s) g) ∂μ) = ∫ g, k g ∂μ`. Introduce `s`. Establish `hm : AEStronglyMeasurable k (μ.map (rmulF (E s)))` using `by rw [hinv s]; exact hRI.1`.

Rewrite using `[← integral_map (hR s).aemeasurable hm, hinv s]`. Establish `hkN : ∀ s : ℝ, (∫ g, ‖k (rmulF (E s) g)‖ ∂μ) = ∫ g, ‖k g‖ ∂μ`. Introduce `s`. Establish `hm : AEStronglyMeasurable (fun g => ‖k g‖) (μ.map (rmulF (E s)))` using `by rw [hinv s]; exact hRI.1.norm`. Rewrite using `[← integral_map (hR s).aemeasurable hm, hinv s]`.

Establish `hint : Integrable (fun p => k (Ψ p)) (μ.prod ν)`. Establish `hm : AEStronglyMeasurable (fun p => k (Ψ p)) (μ.prod ν)` using `hRI.1.comp_quasiMeasurePreserving hq`. Rewrite using `[integrable_prod_iff' hm]`. Use `⟨Filter.Eventually.of_forall fun s => hkR s, ?_⟩` and prove the remaining obligations. Establish `: (fun y : ℝ => ∫ x, ‖k (Ψ (x, y))‖ ∂μ) = fun _ => ∫ g, ‖k g‖ ∂μ`.

Use function extensionality and compare the values at `y`. Conclude with `hkN y`. Rewrite using `[this]`. Conclude with `integrable_const _`. Establish `hswap` using `integral_integral_swap (f := fun g s => k (Ψ (g, s))) (μ := μ) (ν := ν) hint`.

Establish `hrhs : (∫ s, ∫ g, k (Ψ (g, s)) ∂μ ∂ν) = ∫ g, k g ∂μ`. Establish `: (fun s : ℝ => ∫ g, k (Ψ (g, s)) ∂μ) = fun _ => ∫ g, k g ∂μ`. Use function extensionality and compare the values at `s`. Conclude with `hkI s`. Rewrite using `[this]`.

Simplify using `[hν]`. Establish `hftc : ∀ᵐ g ∂μ, (∫ s, k (Ψ (g, s)) ∂ν) = h (Matrix.of (rmulF (E 1) g)) - h (Matrix.of g)` using `by filter_upwards [hC1] with g hg set φ : ℝ → ℂ := fun t => h (Matrix.of g * E t) with hφ`. Establish `hd : ∀ s, deriv φ s = k (Ψ (g, s))`. Introduce `s`. Establish `e1 : k (Ψ (g, s)) = deriv (fun t : ℝ => φ (s + t)) 0`.

Simplify using `only [hk, RdV, hΨd, hφ]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Rewrite using `[hEadd, ← mul_assoc]`. Both sides reduce to the same expression.

Rewrite using `[e1, deriv_comp_const_add, add_zero]`. Establish `hf` using `intervalIntegral.integral_deriv_eq_sub (f := φ) (a := 0) (b := 1) (fun x _ => (hg.differentiable (by norm_num)) x) ((hg.continuous_deriv (le_refl _)).intervalIntegrable _ _)`. Rewrite `hf` using `[intervalIntegral.integral_of_le zero_le_one]`. Establish `e2 : (∫ s, k (Ψ (g, s)) ∂ν) = ∫ s in Set.Ioc 0 1, deriv φ s`. Rewrite using `[hν]`.

Use `congr 1`. Use function extensionality and compare the values at `s`. Conclude with `(hd s).symm`. Rewrite using `[e2, hf]`. Simplify using `only [hφ, hE0, mul_one]`.

Both sides reduce to the same expression. Establish `hhI : (∫ g, h (Matrix.of (rmulF (E 1) g)) ∂μ) = ∫ g, h (Matrix.of g) ∂μ`. Establish `hm : AEStronglyMeasurable (fun g => h (Matrix.of g)) (μ.map (rmulF (E 1)))` using `by rw [hinv 1]; exact hI.1`. Rewrite using `[← integral_map (hR 1).aemeasurable hm, hinv 1]`. Establish `hhR : Integrable (fun g => h (Matrix.of (rmulF (E 1) g))) μ`.

Establish `: Integrable (fun g => h (Matrix.of g)) (μ.map (rmulF (E 1)))` using `by rw [hinv 1]; exact hI`. Conclude with `this.comp_measurable (hR 1)`. Establish `hl : (∫ g, ∫ s, k (Ψ (g, s)) ∂ν ∂μ) = 0`. Rewrite using `[integral_congr_ae hftc, integral_sub hhR hI, hhI, sub_self]`. Rewrite using `[← hrhs, ← hswap, hl]`.
-/
theorem intZero : IntRdZeroInv := by
  intro n μ _ X h hinv hC1 hI hRI
  set E : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => NormedSpace.exp ((t : ℂ) • X) with hE
  have hEcont : Continuous E := by
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
    have h1 : Continuous fun t : ℝ => ((t : ℂ) • X) := by fun_prop
    exact NormedSpace.exp_continuous.comp h1
  have hEadd : ∀ s t : ℝ, E (s + t) = E s * E t := by
    intro s t
    simp only [hE]
    rw [← Matrix.exp_add_of_commute]
    · congr 1; push_cast; rw [add_smul]
    · exact ((Commute.refl X).smul_left _).smul_right _
  have hE0 : E 0 = 1 := by simp [hE]
  set k : (Fin n → Fin n → ℂ) → ℂ := fun g => RdV X h (Matrix.of g) with hk
  set Ψ : (Fin n → Fin n → ℂ) × ℝ → (Fin n → Fin n → ℂ) := fun p => rmulF (E p.2) p.1 with hΨd
  have hΨc : Continuous Ψ := by
    have : Continuous fun p : (Fin n → Fin n → ℂ) × ℝ => (Matrix.of p.1 : Matrix (Fin n) (Fin n) ℂ) * E p.2 :=
      Continuous.matrix_mul continuous_fst (hEcont.comp continuous_snd)
    exact this
  have hΨ : Measurable Ψ := hΨc.measurable
  have hR : ∀ s : ℝ, Measurable (rmulF (E s)) := fun s => hΨ.comp measurable_prodMk_right
  set ν : Measure ℝ := volume.restrict (Set.Ioc 0 1) with hν
  have hq : Measure.QuasiMeasurePreserving Ψ (μ.prod ν) μ := by
    refine ⟨hΨ, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
    rw [Measure.map_apply hΨ hs, Measure.prod_apply_symm (hΨ hs)]
    have : ∀ y : ℝ, μ ((fun x => (x, y)) ⁻¹' (Ψ ⁻¹' s)) = 0 := by
      intro y
      have e : (fun x => (x, y)) ⁻¹' (Ψ ⁻¹' s) = rmulF (E y) ⁻¹' s := rfl
      rw [e, ← Measure.map_apply (hR y) hs, hinv y, h0]
    simp [this]
  have hkR : ∀ s : ℝ, Integrable (fun g => k (rmulF (E s) g)) μ := by
    intro s
    have : Integrable k (μ.map (rmulF (E s))) := by rw [hinv s]; exact hRI
    exact this.comp_measurable (hR s)
  have hkI : ∀ s : ℝ, (∫ g, k (rmulF (E s) g) ∂μ) = ∫ g, k g ∂μ := by
    intro s
    have hm : AEStronglyMeasurable k (μ.map (rmulF (E s))) := by rw [hinv s]; exact hRI.1
    rw [← integral_map (hR s).aemeasurable hm, hinv s]
  have hkN : ∀ s : ℝ, (∫ g, ‖k (rmulF (E s) g)‖ ∂μ) = ∫ g, ‖k g‖ ∂μ := by
    intro s
    have hm : AEStronglyMeasurable (fun g => ‖k g‖) (μ.map (rmulF (E s))) := by rw [hinv s]; exact hRI.1.norm
    rw [← integral_map (hR s).aemeasurable hm, hinv s]
  have hint : Integrable (fun p => k (Ψ p)) (μ.prod ν) := by
    have hm : AEStronglyMeasurable (fun p => k (Ψ p)) (μ.prod ν) := hRI.1.comp_quasiMeasurePreserving hq
    rw [integrable_prod_iff' hm]
    refine ⟨Filter.Eventually.of_forall fun s => hkR s, ?_⟩
    have : (fun y : ℝ => ∫ x, ‖k (Ψ (x, y))‖ ∂μ) = fun _ => ∫ g, ‖k g‖ ∂μ := by
      funext y; exact hkN y
    rw [this]
    exact integrable_const _
  have hswap := integral_integral_swap (f := fun g s => k (Ψ (g, s))) (μ := μ) (ν := ν) hint
  have hrhs : (∫ s, ∫ g, k (Ψ (g, s)) ∂μ ∂ν) = ∫ g, k g ∂μ := by
    have : (fun s : ℝ => ∫ g, k (Ψ (g, s)) ∂μ) = fun _ => ∫ g, k g ∂μ := by
      funext s; exact hkI s
    rw [this]
    simp [hν]
  have hftc : ∀ᵐ g ∂μ, (∫ s, k (Ψ (g, s)) ∂ν) = h (Matrix.of (rmulF (E 1) g)) - h (Matrix.of g) := by
    filter_upwards [hC1] with g hg
    set φ : ℝ → ℂ := fun t => h (Matrix.of g * E t) with hφ
    have hd : ∀ s, deriv φ s = k (Ψ (g, s)) := by
      intro s
      have e1 : k (Ψ (g, s)) = deriv (fun t : ℝ => φ (s + t)) 0 := by
        simp only [hk, RdV, hΨd, hφ]
        congr 1
        funext t
        rw [hEadd, ← mul_assoc]
        rfl
      rw [e1, deriv_comp_const_add, add_zero]
    have hf := intervalIntegral.integral_deriv_eq_sub (f := φ) (a := 0) (b := 1)
      (fun x _ => (hg.differentiable (by norm_num)) x)
      ((hg.continuous_deriv (le_refl _)).intervalIntegrable _ _)
    rw [intervalIntegral.integral_of_le zero_le_one] at hf
    have e2 : (∫ s, k (Ψ (g, s)) ∂ν) = ∫ s in Set.Ioc 0 1, deriv φ s := by
      rw [hν]; congr 1; funext s; exact (hd s).symm
    rw [e2, hf]
    simp only [hφ, hE0, mul_one]
    rfl
  have hhI : (∫ g, h (Matrix.of (rmulF (E 1) g)) ∂μ) = ∫ g, h (Matrix.of g) ∂μ := by
    have hm : AEStronglyMeasurable (fun g => h (Matrix.of g)) (μ.map (rmulF (E 1))) := by rw [hinv 1]; exact hI.1
    rw [← integral_map (hR 1).aemeasurable hm, hinv 1]
  have hhR : Integrable (fun g => h (Matrix.of (rmulF (E 1) g))) μ := by
    have : Integrable (fun g => h (Matrix.of g)) (μ.map (rmulF (E 1))) := by rw [hinv 1]; exact hI
    exact this.comp_measurable (hR 1)
  have hl : (∫ g, ∫ s, k (Ψ (g, s)) ∂ν ∂μ) = 0 := by
    rw [integral_congr_ae hftc, integral_sub hhR hI, hhI, sub_self]
  rw [← hrhs, ← hswap, hl]

end Formalism.FourierDecayAlt.P.B1

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `B1.semi`.
-/
theorem seminorm_inequality : Formalism.FourierDecayAlt.B.SeminormIneq := B1.semi

/- English proof (translation)
The claim follows from `B1.coreC`.
-/
theorem bilinear_form_continuity : Formalism.FourierDecayAlt.B.FormCoreC := B1.coreC

/- English proof (translation)
The claim follows from `B1.core0`.
-/
theorem bilinear_form_at_zero : Formalism.FourierDecayAlt.B.FormCore := B1.core0

/- English proof (translation)
The claim follows from `B1.fatou`.
-/
theorem fatou_lemma_in_parameter : Formalism.FourierDecayAlt.B.FatouParam := B1.fatou

/- English proof (translation)
The claim follows from `B1.ibp`.
-/
theorem integration_by_parts_regularised : Formalism.FourierDecayAlt.B.RegIBP := B1.ibp

/- English proof (translation)
The claim follows from `B1.decay B1.ibp`.
-/
theorem test_function_decay : Formalism.FourierDecayAlt.B.TestDecay := B1.decay B1.ibp

/- English proof (translation)
The claim follows from `B1.intZero`.
-/
theorem integral_zero_frequency_invariant : Formalism.FourierDecayAlt.B.IntRdZeroInv := B1.intZero

end Formalism.FourierDecayAlt.P
