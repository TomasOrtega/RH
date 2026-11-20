import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleCpowDetInverseTwist
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

/- English proof (translation)
Introduce `s₀`. Use `set σ : ℝ := max 2 (|s₀.re| + 3) with hσ`. Establish `hσ2 : 2 ≤ σ` using `le_max_left _ _`. Establish `hσ3 : |s₀.re| + 3 ≤ σ` using `le_max_right _ _`. Establish `hmD : Measurable fun x => ((D x : ℝ) : ℂ)` using `Complex.measurable_ofReal.comp hD`.

Establish `hmb : Measurable fun x => ‖w x‖ * D x ^ σ` using `hw.norm.mul (hD.pow_const σ)`. Establish `hbound : Integrable (fun x => ‖w x‖ * D x ^ σ) ν`. Use `⟨hmb.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Use `lt_of_le_of_lt (le_of_eq ?_) (hfin σ (by linarith))` and prove the remaining obligations. Use `lintegral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [h1] with x hx`. Establish `hp : 0 ≤ D x ^ σ` using `Real.rpow_nonneg (by linarith) σ`. Rewrite using `[enorm_mul, Real.enorm_of_nonneg hp, enorm_norm]`. Establish `hre : ∀ s ∈ Metric.ball s₀ 1, s.re + 1 ≤ σ`. Introduce `s hs`.

Establish `h : ‖s - s₀‖ < 1` using `by simpa [dist_eq_norm] using hs`. Establish `h2 : |(s - s₀).re| ≤ ‖s - s₀‖` using `Complex.abs_re_le_norm _`. Establish `h3` using `le_abs_self (s - s₀).re`. Establish `h4` using `le_abs_self s₀.re`. Simplify using `only [Complex.sub_re] at h2 h3`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnorm : ∀ x, 1 ≤ D x → ∀ s : ℂ, ‖((D x : ℝ) : ℂ) ^ s‖ = D x ^ s.re` using `fun x hx s => Complex.norm_cpow_eq_rpow_re_of_pos (by linarith) s`. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := s₀) (F := fun s x => w x * ((D x : ℝ) : ℂ) ^ s) (F' := fun s x => w x * (((D x : ℝ) : ℂ) ^ s * Complex.log ((D x : ℝ) : ℂ))) (bound := fun x => ‖w x‖ * D x ^ σ) (Metric.ball_mem_nhds s₀ one_pos) (Eventually.of_foral …`. Conclude with `key.2.differentiableAt`. Use `hbound.mono' (hw.mul (hmD.pow_const s₀)).aestronglyMeasurable ?_ filter_upwards [h1] with x hx` and prove the remaining obligations.

Rewrite using `[norm_mul, hnorm x hx]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Use `Real.rpow_le_rpow_of_exponent_le hx ?_` and prove the remaining obligations. Use `le_abs_self s₀.re` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `filter_upwards [h1] with x hx s hs`. Rewrite using `[norm_mul, norm_mul, hnorm x hx, ← Complex.ofReal_log (by linarith), Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hx)]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Establish `hpos : 0 < D x` using `by linarith`. Establish `hlog : Real.log (D x) ≤ D x` using `(Real.log_le_sub_one_of_pos hpos).trans (by linarith)`.

Combine the equalities or inequalities in the displayed calculation. Use `filter_upwards [h1] with x hx s _`. Establish `h0 : ((D x : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (by linarith)`. Use `((hasDerivAt_id s).const_cpow (c := ((D x : ℝ) : ℂ)) (Or.inl h0)).const_mul (w x)` as an intermediate fact. Simplify using `using this`.
-/
theorem differentiable_integral_cpow_of_one_le {X : Type*} [MeasurableSpace X] (ν : Measure X) (D : X → ℝ)
    (w : X → ℂ) (hD : Measurable D) (hw : Measurable w) (h1 : ∀ᵐ x ∂ν, 1 ≤ D x)
    (hfin : ∀ σ : ℝ, 1 < σ → ∫⁻ x, ‖w x‖ₑ * ENNReal.ofReal (D x ^ σ) ∂ν < ∞) :
    Differentiable ℂ (fun s : ℂ => ∫ x, w x * ((D x : ℝ) : ℂ) ^ s ∂ν) := by
  intro s₀
  set σ : ℝ := max 2 (|s₀.re| + 3) with hσ
  have hσ2 : 2 ≤ σ := le_max_left _ _
  have hσ3 : |s₀.re| + 3 ≤ σ := le_max_right _ _
  have hmD : Measurable fun x => ((D x : ℝ) : ℂ) := Complex.measurable_ofReal.comp hD
  have hmb : Measurable fun x => ‖w x‖ * D x ^ σ := hw.norm.mul (hD.pow_const σ)
  have hbound : Integrable (fun x => ‖w x‖ * D x ^ σ) ν := by
    refine ⟨hmb.aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (le_of_eq ?_) (hfin σ (by linarith))
    refine lintegral_congr_ae ?_
    filter_upwards [h1] with x hx
    have hp : 0 ≤ D x ^ σ := Real.rpow_nonneg (by linarith) σ
    rw [enorm_mul, Real.enorm_of_nonneg hp, enorm_norm]
  have hre : ∀ s ∈ Metric.ball s₀ 1, s.re + 1 ≤ σ := by
    intro s hs
    have h : ‖s - s₀‖ < 1 := by simpa [dist_eq_norm] using hs
    have h2 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
    have h3 := le_abs_self (s - s₀).re
    have h4 := le_abs_self s₀.re
    simp only [Complex.sub_re] at h2 h3
    linarith
  have hnorm : ∀ x, 1 ≤ D x → ∀ s : ℂ, ‖((D x : ℝ) : ℂ) ^ s‖ = D x ^ s.re := fun x hx s =>
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith) s
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := s₀)
    (F := fun s x => w x * ((D x : ℝ) : ℂ) ^ s)
    (F' := fun s x => w x * (((D x : ℝ) : ℂ) ^ s * Complex.log ((D x : ℝ) : ℂ)))
    (bound := fun x => ‖w x‖ * D x ^ σ) (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s => (hw.mul (hmD.pow_const s)).aestronglyMeasurable)
    ?_ ((hw.mul ((hmD.pow_const s₀).mul (Complex.measurable_log.comp hmD))).aestronglyMeasurable)
    ?_ hbound ?_
  · exact key.2.differentiableAt
  · refine hbound.mono' (hw.mul (hmD.pow_const s₀)).aestronglyMeasurable ?_
    filter_upwards [h1] with x hx
    rw [norm_mul, hnorm x hx]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine Real.rpow_le_rpow_of_exponent_le hx ?_
    have := le_abs_self s₀.re
    linarith
  · filter_upwards [h1] with x hx s hs
    rw [norm_mul, norm_mul, hnorm x hx, ← Complex.ofReal_log (by linarith), Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg hx)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hpos : 0 < D x := by linarith
    have hlog : Real.log (D x) ≤ D x := (Real.log_le_sub_one_of_pos hpos).trans (by linarith)
    calc D x ^ s.re * Real.log (D x) ≤ D x ^ s.re * D x :=
          mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hpos.le _)
      _ = D x ^ (s.re + 1) := by rw [Real.rpow_add_one hpos.ne']
      _ ≤ D x ^ σ := Real.rpow_le_rpow_of_exponent_le hx (hre s hs)
  · filter_upwards [h1] with x hx s _
    have h0 : ((D x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
    have := ((hasDerivAt_id s).const_cpow (c := ((D x : ℝ) : ℂ)) (Or.inl h0)).const_mul (w x)
    simpa using this

/- English proof (translation)
Establish `hth : Measurable (th Φ)` using `(h3 μ 𝓕 mK 𝓓 h0 H hH Φ hΦ 2 one_lt_two).1`. Establish `hmA : MeasurableSet (𝓕 ∩ {g | 1 ≤ Dt g})` using `h0.meas.inter (measurableSet_le measurable_const measurable_Dt)`. Establish `hw : Measurable fun g => H g * cdet c g * th Φ g` using `(hH.cont.measurable.mul (measurable_cdet c)).mul hth`. Establish `main` using `differentiable_integral_cpow_of_one_le (μ.restrict (𝓕 ∩ {g | 1 ≤ Dt g})) Dt (fun g => H g * cdet c g * th Φ g) measurable_Dt hw ((ae_restrict_mem hmA).mono fun g hg => hg.2) ?_`. Establish `e : GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c Φ = fun s : ℂ => ∫ g, (H g * cdet c g * th Φ g) * ((Dt g : ℝ) : ℂ) ^ s ∂(μ.restrict (𝓕 ∩ {g | 1 ≤ Dt g}))`.

Use function extensionality and compare the values at `s`. Simplify using `only [Zp]`. Use `integral_congr_ae (Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `only`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `main`. Introduce `σ hσ`. Use `lt_of_le_of_lt ?_ (h3 μ 𝓕 mK 𝓓 h0 H hH Φ hΦ σ hσ).2.2` and prove the remaining obligations. Use `le_trans ?_ (lintegral_mono_set (Set.inter_subset_left (t := {g | 1 ≤ Dt g})))` and prove the remaining obligations.

Use `lintegral_mono fun g => ?_` and prove the remaining obligations. Establish `hc : ‖cdet c g‖ₑ = 1`. Rewrite using `[← ofReal_norm, norm_cdet]`. Simplify using the standard rewrite rules. Rewrite using `[enorm_mul, enorm_mul, hc, mul_one]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem differentiable_Zp (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ)
    (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) (c : HeckeCharacter ℚ) (h3 : Ad3.R.G3) (h0 : Set0 μ 𝓕 mK 𝓓) (hH : Aut H)
    (hΦ : Φ ∈ Adele2.schwartzBruhat2 ℚ) : Differentiable ℂ (GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c Φ) := by
  have hth : Measurable (th Φ) := (h3 μ 𝓕 mK 𝓓 h0 H hH Φ hΦ 2 one_lt_two).1
  have hmA : MeasurableSet (𝓕 ∩ {g | 1 ≤ Dt g}) :=
    h0.meas.inter (measurableSet_le measurable_const measurable_Dt)
  have hw : Measurable fun g => H g * cdet c g * th Φ g :=
    (hH.cont.measurable.mul (measurable_cdet c)).mul hth
  have main := differentiable_integral_cpow_of_one_le (μ.restrict (𝓕 ∩ {g | 1 ≤ Dt g})) Dt
    (fun g => H g * cdet c g * th Φ g) measurable_Dt hw
    ((ae_restrict_mem hmA).mono fun g hg => hg.2) ?_
  · have e : GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c Φ =
        fun s : ℂ => ∫ g, (H g * cdet c g * th Φ g) * ((Dt g : ℝ) : ℂ) ^ s ∂(μ.restrict (𝓕 ∩ {g | 1 ≤ Dt g})) := by
      funext s
      simp only [Zp]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only
      ring
    rw [e]
    exact main
  · intro σ hσ
    refine lt_of_le_of_lt ?_ (h3 μ 𝓕 mK 𝓓 h0 H hH Φ hΦ σ hσ).2.2
    refine le_trans ?_ (lintegral_mono_set (Set.inter_subset_left (t := {g | 1 ≤ Dt g})))
    refine lintegral_mono fun g => ?_
    have hc : ‖cdet c g‖ₑ = 1 := by
      rw [← ofReal_norm, norm_cdet]; simp
    rw [enorm_mul, enorm_mul, hc, mul_one]
    calc ‖H g‖ₑ * ‖th Φ g‖ₑ * ENNReal.ofReal (Dt g ^ σ)
        = (‖H g‖ₑ * ENNReal.ofReal (Dt g ^ σ)) * ‖th Φ g‖ₑ := by ring
      _ ≤ _ := by gcongr; exact enorm_tsum_le_tsum_enorm

end GlobalTheory.CompanionTheory.RSZeta
