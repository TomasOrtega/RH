import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ExpCombine
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.StepB
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.StepC

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

/- English proof (translation)
The claim follows from `Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_ip)).neg)`.
-/
theorem continuous_cexp_ip (t : ℝ) : Continuous (fun p : E n × E n => Complex.exp (-(Complex.I * t * ip p.1 p.2))) :=
  Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_ip)).neg)

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `hexp` using `continuous_cexp_ip (n := n) t`. Establish `hbd : ∀ k y β, ‖ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))‖ ≤ ‖ρ y‖`. Introduce `k y β`. Rewrite using `[norm_mul, norm_mul, norm_cexp_neg_It, mul_one]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (norm_gauss_le _ (hε k) y)`.

Establish `hcont : ∀ k, Continuous (fun β : E n => ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y)))`. Introduce `k`. Use `continuous_of_dominated (bound := fun y => ‖ρ y‖) ?_ ?_ hρ.norm ?_` and prove the remaining obligations. Introduce `β`. Conclude with `(hρ.aestronglyMeasurable.mul (continuous_gam (ε k)).aestronglyMeasurable).mul (hexp.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable`.

Introduce `β`. Conclude with `Eventually.of_forall fun y => hbd k y β`. Conclude with `Eventually.of_forall fun y => continuous_const.mul (hexp.comp (continuous_id.prodMk continuous_const))`. Establish `hin : ∀ β : E n, Tendsto (fun k => ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))) atTop (𝓝 (∫ y, ρ y * Complex.exp (-(Complex.I * t * ip β y))))`. Introduce `β`.

Use `tendsto_integral_of_dominated_convergence (fun y => ‖ρ y‖) ?_ hρ.norm ?_ ?_` and prove the remaining obligations. Introduce `k`. Conclude with `(hρ.aestronglyMeasurable.mul (continuous_gam (ε k)).aestronglyMeasurable).mul (hexp.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable`. Introduce `k`. Conclude with `Eventually.of_forall fun y => hbd k y β`.

Use `Eventually.of_forall fun y => ?_` and prove the remaining obligations. Establish `h0 : Tendsto (fun k => -(((ε k * ip y y : ℝ)) : ℂ)) atTop (𝓝 0)`. Establish `h` using `hε0.mul_const (ip y y)`. Rewrite `h` using `[zero_mul]`. Establish `h'` using `((Complex.continuous_ofReal.tendsto 0).comp h).neg`.

Simplify `h'` using `[Function.comp_def]`. Establish `hg : Tendsto (fun k => gam (ε k) y) atTop (𝓝 1)`. Use `(Complex.continuous_exp.tendsto 0).comp h0` as an intermediate fact. Simplify `this` using `[gam, Function.comp_def]`. Use `((tendsto_const_nhds (x := ρ y)).mul hg).mul (tendsto_const_nhds (x := Complex.exp (-(Complex.I * t * ip β y))))` as an intermediate fact.

Simplify using `using this`. Use `tendsto_integral_of_dominated_convergence (fun β => ‖ψ β‖ * (‖C‖ * ∫ y, ‖ρ y‖)) ?_ (hψi.norm.mul_const _) ?_ ?_` and prove the remaining obligations. Introduce `k`. Conclude with `(hψc.mul (continuous_const.mul (hcont k))).aestronglyMeasurable`. Introduce `k`.

Use `Eventually.of_forall fun β => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul]`. Use `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (norm_nonneg _)` and prove the remaining obligations. Conclude with `norm_integral_le_of_norm_le hρ.norm (Eventually.of_forall fun y => hbd k y β)`. Conclude with `Eventually.of_forall fun β => tendsto_const_nhds.mul (tendsto_const_nhds.mul (hin β))`.
-/
theorem lim_one (ρ : E n → ℂ) (hρ : Integrable ρ) (t : ℝ) (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ)
    (C : ℂ) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ∫ β, ψ β * (C * ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))))
      atTop (𝓝 (∫ β, ψ β * (C * ∫ y, ρ y * Complex.exp (-(Complex.I * t * ip β y))))) := by
  have hexp := continuous_cexp_ip (n := n) t
  have hbd : ∀ k y β, ‖ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))‖ ≤ ‖ρ y‖ := by
    intro k y β
    rw [norm_mul, norm_mul, norm_cexp_neg_It, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_gauss_le _ (hε k) y)
  have hcont : ∀ k, Continuous (fun β : E n => ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))) := by
    intro k
    refine continuous_of_dominated (bound := fun y => ‖ρ y‖) ?_ ?_ hρ.norm ?_
    · intro β
      exact (hρ.aestronglyMeasurable.mul (continuous_gam (ε k)).aestronglyMeasurable).mul
        (hexp.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro β; exact Eventually.of_forall fun y => hbd k y β
    · exact Eventually.of_forall fun y => continuous_const.mul (hexp.comp (continuous_id.prodMk continuous_const))
  have hin : ∀ β : E n, Tendsto (fun k => ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y)))
      atTop (𝓝 (∫ y, ρ y * Complex.exp (-(Complex.I * t * ip β y)))) := by
    intro β
    refine tendsto_integral_of_dominated_convergence (fun y => ‖ρ y‖) ?_ hρ.norm ?_ ?_
    · intro k
      exact (hρ.aestronglyMeasurable.mul (continuous_gam (ε k)).aestronglyMeasurable).mul
        (hexp.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro k; exact Eventually.of_forall fun y => hbd k y β
    · refine Eventually.of_forall fun y => ?_
      have h0 : Tendsto (fun k => -(((ε k * ip y y : ℝ)) : ℂ)) atTop (𝓝 0) := by
        have h := hε0.mul_const (ip y y)
        rw [zero_mul] at h
        have h' := ((Complex.continuous_ofReal.tendsto 0).comp h).neg
        simpa [Function.comp_def] using h'
      have hg : Tendsto (fun k => gam (ε k) y) atTop (𝓝 1) := by
        have := (Complex.continuous_exp.tendsto 0).comp h0
        simpa [gam, Function.comp_def] using this
      have := ((tendsto_const_nhds (x := ρ y)).mul hg).mul
        (tendsto_const_nhds (x := Complex.exp (-(Complex.I * t * ip β y))))
      simpa using this
  refine tendsto_integral_of_dominated_convergence (fun β => ‖ψ β‖ * (‖C‖ * ∫ y, ‖ρ y‖)) ?_
    (hψi.norm.mul_const _) ?_ ?_
  · intro k
    exact (hψc.mul (continuous_const.mul (hcont k))).aestronglyMeasurable
  · intro k; refine Eventually.of_forall fun β => ?_
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (norm_nonneg _)
    exact norm_integral_le_of_norm_le hρ.norm (Eventually.of_forall fun y => hbd k y β)
  · exact Eventually.of_forall fun β => tendsto_const_nhds.mul (tendsto_const_nhds.mul (hin β))

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `hlim : ∫ x, ψ (qq x) * Ψ x ∂μ = ∫ x, Ψ x * ψ (qq x) ∂μ` using `by simp_rw [mul_comm]`. Rewrite using `[hlim]`. Use `tendsto_integral_of_dominated_convergence (fun x => ‖Ψ x‖ * B) ?_ (hΨ.norm.mul_const _) ?_ ?_` and prove the remaining obligations. Introduce `k`. Conclude with `hΨ.aestronglyMeasurable.mul ((continuous_mM ψ B hB hψc (l k)).measurable.comp hqq).aestronglyMeasurable`.

Introduce `k`. Use `Eventually.of_forall fun x => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (norm_mM_le ψ B hB hψc _ _) (norm_nonneg _)`. Conclude with `Eventually.of_forall fun x => tendsto_const_nhds.mul (tendsto_mM ψ B hB hψc l hl (qq x))`.
-/
theorem lim_two (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (ψ : E n → ℂ)
    (hψc : Continuous ψ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (l : ℕ → ℝ) (hl : Tendsto (fun k => (l k)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, Ψ x * mM ψ (l k) (qq x) ∂μ) atTop (𝓝 (∫ x, ψ (qq x) * Ψ x ∂μ)) := by
  have hlim : ∫ x, ψ (qq x) * Ψ x ∂μ = ∫ x, Ψ x * ψ (qq x) ∂μ := by simp_rw [mul_comm]
  rw [hlim]
  refine tendsto_integral_of_dominated_convergence (fun x => ‖Ψ x‖ * B) ?_ (hΨ.norm.mul_const _) ?_ ?_
  · intro k
    exact hΨ.aestronglyMeasurable.mul ((continuous_mM ψ B hB hψc (l k)).measurable.comp hqq).aestronglyMeasurable
  · intro k; refine Eventually.of_forall fun x => ?_
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_mM_le ψ B hB hψc _ _) (norm_nonneg _)
  · exact Eventually.of_forall fun x => tendsto_const_nhds.mul (tendsto_mM ψ B hB hψc l hl (qq x))

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `ha : ∀ β : E n, ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y * Complex.exp (-(Complex.I * t * ip β y)) = ∫ x, Ψ x * kr ε t (qq x - β) ∂μ` using `fun β => step_a Ψ qq hΨ hqq t ε hε β`. Repeatedly rewrite using `[ha]`. Rewrite using `[step_b Ψ qq hΨ hqq t ε hε ψ hψc hψi]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Rewrite using `[step_c ψ t ε ht hε (qq x)]`.
-/
theorem eq_A (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t : ℝ) (ht : t ≠ 0)
    (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ) (ε : ℝ) (hε : 0 < ε) :
    ∫ β, ψ β * ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) *
        ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
          Complex.exp (-(Complex.I * t * ip β y))) =
      ∫ x, Ψ x * mM ψ (|t| / (2 * Real.sqrt ε)) (qq x) ∂μ := by
  have ha : ∀ β : E n, ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
      Complex.exp (-(Complex.I * t * ip β y)) = ∫ x, Ψ x * kr ε t (qq x - β) ∂μ :=
    fun β => step_a Ψ qq hΨ hqq t ε hε β
  simp_rw [ha]
  rw [step_b Ψ qq hΨ hqq t ε hε ψ hψc hψi]
  congr 1
  funext x
  rw [step_c ψ t ε ht hε (qq x)]

/- English proof (translation)
Introduce `n X _ μ _ Ψ qq hΨ hqq t ht hρ ψ hψc hψs`. Take `⟨B, hB⟩` from `hψc.bounded_above_of_compact_support hψs`. Establish `hψi : Integrable ψ` using `hψc.integrable_of_hasCompactSupport hψs`. Establish `hε : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1)` using `fun k => by positivity`. Establish `hε0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0)` using `tendsto_one_div_add_atTop_nhds_zero_nat`.

Establish `hl : Tendsto (fun k : ℕ => (|t| / (2 * Real.sqrt (1 / ((k : ℝ) + 1))))⁻¹) atTop (𝓝 0)`. Establish `e : (fun k : ℕ => (|t| / (2 * Real.sqrt (1 / ((k : ℝ) + 1))))⁻¹) = fun k : ℕ => (2 / |t|) * Real.sqrt (1 / ((k : ℝ) + 1))`. Use function extensionality and compare the values at `k`. Rewrite using `[inv_div]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Establish `h` using `((Real.continuous_sqrt.tendsto 0).comp hε0).const_mul (2 / |t|)`. Simplify `h` using `[Real.sqrt_zero, Function.comp_def]`. Establish `h1` using `lim_one _ hρ t ψ hψc hψi ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ)) _ hε hε0`. Establish `h2` using `lim_two Ψ qq hΨ hqq ψ hψc B hB _ hl`.

Establish `e : (fun k : ℕ => ∫ β, ψ β * ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) * ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam (1 / ((k : ℝ) + 1)) y * Complex.exp (-(Complex.I * t * ip β y)))) = fun k : ℕ => ∫ x, Ψ x * mM ψ (|t| / (2 * Real.sqrt (1 / ((k : ℝ) + …`. Use function extensionality and compare the values at `k`. Conclude with `eq_A Ψ qq hΨ hqq t ht ψ hψc hψi _ (hε k)`. Rewrite `h1` using `[e]`. Conclude with `tendsto_nhds_unique h2 h1`.
-/
theorem _root_.PositivityTheory.Rg.Sw.WR.D.mollId : MollId := by
  intro n X _ μ _ Ψ qq hΨ hqq t ht hρ ψ hψc hψs
  obtain ⟨B, hB⟩ := hψc.bounded_above_of_compact_support hψs
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  have hε : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hε0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto (fun k : ℕ => (|t| / (2 * Real.sqrt (1 / ((k : ℝ) + 1))))⁻¹) atTop (𝓝 0) := by
    have e : (fun k : ℕ => (|t| / (2 * Real.sqrt (1 / ((k : ℝ) + 1))))⁻¹) =
        fun k : ℕ => (2 / |t|) * Real.sqrt (1 / ((k : ℝ) + 1)) := by
      funext k; rw [inv_div]; ring
    rw [e]
    have h := ((Real.continuous_sqrt.tendsto 0).comp hε0).const_mul (2 / |t|)
    simpa [Real.sqrt_zero, Function.comp_def] using h
  have h1 := lim_one _ hρ t ψ hψc hψi ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ)) _ hε hε0
  have h2 := lim_two Ψ qq hΨ hqq ψ hψc B hB _ hl
  have e : (fun k : ℕ => ∫ β, ψ β * ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) *
        ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam (1 / ((k : ℝ) + 1)) y *
          Complex.exp (-(Complex.I * t * ip β y)))) =
      fun k : ℕ => ∫ x, Ψ x * mM ψ (|t| / (2 * Real.sqrt (1 / ((k : ℝ) + 1)))) (qq x) ∂μ := by
    funext k
    exact eq_A Ψ qq hΨ hqq t ht ψ hψc hψi _ (hε k)
  rw [e] at h1
  exact tendsto_nhds_unique h2 h1

end PositivityTheory.Rg.Sw.WR.D.Moll
