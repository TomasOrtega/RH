import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicDerivNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Filter Topology

/- English proof (translation)
Introduce `D f hD hf hinj a ha hder`. Establish `hDa : D ∈ 𝓝 a` using `hD.mem_nhds ha`. Use `set g : ℂ → ℂ := fun z ↦ f z - f a with hg`. Establish `hga : AnalyticAt ℂ g a` using `(hf.analyticAt hDa).sub analyticAt_const`. Establish `hntop : analyticOrderAt g a ≠ ⊤`.

Introduce `htop`. Rewrite `htop` using `[analyticOrderAt_eq_top]`. Establish `hev : ∀ᶠ z in 𝓝[≠] a, (g z = 0 ∧ z ∈ D) ∧ z ∈ ({a}ᶜ : Set ℂ)` using `((htop.and (hDa : ∀ᶠ z in 𝓝 a, z ∈ D)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin`. Take `⟨z, ⟨hz0, hzD⟩, hza⟩` from `hev.exists`. Conclude with `hza (hinj hzD ha (sub_eq_zero.mp hz0))`.

Take `⟨n, hn⟩` from `ENat.ne_top_iff_exists.mp hntop`. Take `⟨u, hu, hua, hfac⟩` from `hga.analyticOrderAt_eq_natCast.mp hn.symm`. Simplify using `only [smul_eq_mul] at hfac`. Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`.

Use `hfac.self_of_nhds` as an intermediate fact. Simplify using `[hg] at this`. Conclude with `hua this.symm`. Establish `hn1 : n ≠ 1`. Introduce and unpack `rfl`.

Establish `hd : HasDerivAt (fun z ↦ (z - a) ^ 1 * u z) (u a) a`. Use `((hasDerivAt_id' a).sub_const a).mul hu.differentiableAt.hasDerivAt` as an intermediate fact. Simplify using `only [pow_one]`. Conclude with `this.congr_deriv (by simp)`. Establish `: deriv g a = u a` using `(EventuallyEq.deriv_eq (hfac : g =ᶠ[𝓝 a] fun z ↦ (z - a) ^ 1 * u z)).trans hd.deriv`.

Rewrite `this` using `[hg, deriv_sub_const, hder]`. Conclude with `hua this.symm`. Use `set c : ℂ := u a ^ ((n : ℂ)⁻¹) with hc`. Use `set v : ℂ → ℂ := fun z ↦ c * (u z / u a) ^ ((n : ℂ)⁻¹) with hv`. Establish `hva : AnalyticAt ℂ v a` using `analyticAt_const.mul ((hu.div analyticAt_const hua).cpow analyticAt_const (by simp [hua, Complex.one_mem_slitPlane]))`.

Establish `hvpow : ∀ z, v z ^ n = u z`. Introduce `z`. Rewrite using `[hv, mul_pow, hc, Complex.cpow_nat_inv_pow _ hn0, Complex.cpow_nat_inv_pow _ hn0]`. Clear the denominators using the available nonvanishing facts. Establish `hv0 : v a ≠ 0`.

Introduce `h`. Use `hvpow a` as an intermediate fact. Rewrite `this` using `[h, zero_pow hn0]`. Conclude with `hua this.symm`. Use `set w : ℂ → ℂ := fun z ↦ (z - a) * v z with hw`.

Establish `hwd : HasDerivAt w (v a) a`. Use `((hasDerivAt_id' a).sub_const a).mul hva.differentiableAt.hasDerivAt` as an intermediate fact. Conclude with `this.congr_deriv (by simp)`. Establish `hwa : w a = 0` using `by simp [hw]`. Establish `hgw : ∀ z, g z = (z - a) ^ n * u z → g z = w z ^ n`.

Introduce `z hz`. Rewrite using `[hz, ← hvpow z, ← mul_pow]`. Establish `hmap : 𝓝 (w a) ≤ map w (𝓝 a)`. Establish `hwan : AnalyticAt ℂ w a` using `(analyticAt_id.sub analyticAt_const).mul hva`. Use `hwan.eventually_constant_or_nhds_le_map_nhds.resolve_left ?_` and prove the remaining obligations.

Introduce `hconst`. Establish `h1 : deriv w a = 0`. Rewrite using `[EventuallyEq.deriv_eq (hconst : w =ᶠ[𝓝 a] fun _ ↦ w a)]`. Simplify using the standard rewrite rules. Conclude with `hv0 (hwd.deriv.symm.trans h1)`.

Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.mp (hmap (image_mem_map (inter_mem hDa hfac)))`. Rewrite `hball` using `[hwa]`. Establish `hk : 1 < n` using `by omega`. Use `set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hζ`. Establish `hprim : IsPrimitiveRoot ζ n` using `Complex.isPrimitiveRoot_exp n hn0`.

Use `set t : ℂ := ((ε / 2 : ℝ) : ℂ) with ht`. Establish `htn : ‖t‖ = ε / 2` using `by rw [ht, Complex.norm_real, Real.norm_of_nonneg (by positivity)]`. Establish `ht0 : t ≠ 0`. Introduce `h`. Rewrite `htn` using `[h, norm_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨z₁, ⟨hz₁D, hz₁⟩, hw₁⟩` from `hball (by`. Rewrite using `[Metric.mem_ball, dist_zero_right, htn]`. Use the proof step `linarith)`. Take `⟨z₂, ⟨hz₂D, hz₂⟩, hw₂⟩` from `hball (show ζ * t ∈ Metric.ball 0 ε by`.

Rewrite using `[Metric.mem_ball, dist_zero_right, norm_mul, hprim.norm'_eq_one hn0, htn]`. Use the proof step `linarith)`. Establish `hg₁` using `hgw z₁ hz₁`. Establish `hg₂` using `hgw z₂ hz₂`. Rewrite `hg₁` using `[hw₁]`.

Rewrite `hg₂` using `[hw₂, mul_pow, hprim.pow_eq_one, one_mul]`. Establish `hf12 : f z₁ = f z₂`. Establish `: g z₁ = g z₂` using `hg₁.trans hg₂.symm`. Simplify `this` using `[hg]`. Establish `h12` using `hinj hz₁D hz₂D hf12`.

Rewrite `hw₁` using `[h12, hw₂]`. Establish `: (ζ - 1) * t = 0` using `by rw [sub_mul, one_mul, hw₁, sub_self]`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Conclude with `hprim.ne_one hk (sub_eq_zero.mp h)`. Conclude with `ht0 h`.
-/
theorem InjectiveHolomorphicDerivNeZero.proof : InjectiveHolomorphicDerivNeZero.Statement := by
  intro D f hD hf hinj a ha hder
  have hDa : D ∈ 𝓝 a := hD.mem_nhds ha
  set g : ℂ → ℂ := fun z ↦ f z - f a with hg
  have hga : AnalyticAt ℂ g a := (hf.analyticAt hDa).sub analyticAt_const

  have hntop : analyticOrderAt g a ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hev : ∀ᶠ z in 𝓝[≠] a, (g z = 0 ∧ z ∈ D) ∧ z ∈ ({a}ᶜ : Set ℂ) :=
      ((htop.and (hDa : ∀ᶠ z in 𝓝 a, z ∈ D)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨z, ⟨hz0, hzD⟩, hza⟩ := hev.exists
    exact hza (hinj hzD ha (sub_eq_zero.mp hz0))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hntop
  obtain ⟨u, hu, hua, hfac⟩ := hga.analyticOrderAt_eq_natCast.mp hn.symm
  simp only [smul_eq_mul] at hfac
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := hfac.self_of_nhds
    simp [hg] at this
    exact hua this.symm
  have hn1 : n ≠ 1 := by
    rintro rfl
    have hd : HasDerivAt (fun z ↦ (z - a) ^ 1 * u z) (u a) a := by
      have := ((hasDerivAt_id' a).sub_const a).mul hu.differentiableAt.hasDerivAt
      simp only [pow_one]
      exact this.congr_deriv (by simp)
    have : deriv g a = u a :=
      (EventuallyEq.deriv_eq (hfac : g =ᶠ[𝓝 a] fun z ↦ (z - a) ^ 1 * u z)).trans hd.deriv
    rw [hg, deriv_sub_const, hder] at this
    exact hua this.symm

  set c : ℂ := u a ^ ((n : ℂ)⁻¹) with hc
  set v : ℂ → ℂ := fun z ↦ c * (u z / u a) ^ ((n : ℂ)⁻¹) with hv
  have hva : AnalyticAt ℂ v a := analyticAt_const.mul
    ((hu.div analyticAt_const hua).cpow analyticAt_const (by simp [hua, Complex.one_mem_slitPlane]))
  have hvpow : ∀ z, v z ^ n = u z := by
    intro z
    rw [hv, mul_pow, hc, Complex.cpow_nat_inv_pow _ hn0, Complex.cpow_nat_inv_pow _ hn0]
    field_simp
  have hv0 : v a ≠ 0 := by
    intro h
    have := hvpow a
    rw [h, zero_pow hn0] at this
    exact hua this.symm
  set w : ℂ → ℂ := fun z ↦ (z - a) * v z with hw
  have hwd : HasDerivAt w (v a) a := by
    have := ((hasDerivAt_id' a).sub_const a).mul hva.differentiableAt.hasDerivAt
    exact this.congr_deriv (by simp)
  have hwa : w a = 0 := by simp [hw]
  have hgw : ∀ z, g z = (z - a) ^ n * u z → g z = w z ^ n := by
    intro z hz
    rw [hz, ← hvpow z, ← mul_pow]

  have hmap : 𝓝 (w a) ≤ map w (𝓝 a) := by
    have hwan : AnalyticAt ℂ w a := (analyticAt_id.sub analyticAt_const).mul hva
    refine hwan.eventually_constant_or_nhds_le_map_nhds.resolve_left ?_
    intro hconst
    have h1 : deriv w a = 0 := by
      rw [EventuallyEq.deriv_eq (hconst : w =ᶠ[𝓝 a] fun _ ↦ w a)]
      simp
    exact hv0 (hwd.deriv.symm.trans h1)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hmap (image_mem_map (inter_mem hDa hfac)))
  rw [hwa] at hball
  have hk : 1 < n := by omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hζ
  have hprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  set t : ℂ := ((ε / 2 : ℝ) : ℂ) with ht
  have htn : ‖t‖ = ε / 2 := by rw [ht, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, norm_zero] at htn
    linarith
  obtain ⟨z₁, ⟨hz₁D, hz₁⟩, hw₁⟩ := hball (by
    rw [Metric.mem_ball, dist_zero_right, htn]; linarith)
  obtain ⟨z₂, ⟨hz₂D, hz₂⟩, hw₂⟩ := hball (show ζ * t ∈ Metric.ball 0 ε by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hprim.norm'_eq_one hn0, htn]; linarith)
  have hg₁ := hgw z₁ hz₁
  have hg₂ := hgw z₂ hz₂
  rw [hw₁] at hg₁
  rw [hw₂, mul_pow, hprim.pow_eq_one, one_mul] at hg₂
  have hf12 : f z₁ = f z₂ := by
    have : g z₁ = g z₂ := hg₁.trans hg₂.symm
    simpa [hg] using this
  have h12 := hinj hz₁D hz₂D hf12
  rw [h12, hw₂] at hw₁
  have : (ζ - 1) * t = 0 := by rw [sub_mul, one_mul, hw₁, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact hprim.ne_one hk (sub_eq_zero.mp h)
  · exact ht0 h

end GroundTheory.Heights₂.Heights
