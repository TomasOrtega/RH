import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ContDiff Classical

namespace GlobalTheory.Chamber

/- English proof (translation)
Set `f : ℝ → ℂ` to `Set.indicator (Set.Ioc (0 : ℝ) 1) fun _ => (1 : ℂ)`. Establish `hf : Integrable f volume`. Use `IntegrableOn.integrable_indicator ?_ measurableSet_Ioc` and prove the remaining obligations. Use `first`. Consider the case `exact integrableOn_const (by simp)`.

Consider the case `exact integrableOn_const.2 (Or.inr (by simp))`. Consider the case `exact (continuous_const.integrableOn_Icc (a := (0:ℝ)) (b := 1)).mono_set Set.Ioc_subset_Icc_self`. Set `K : Set ℝ` to `Set.Icc 0 1`. Establish `hK : IsCompact K` using `isCompact_Icc`. Take `⟨R, hR0, hR⟩` from `hK.isBounded.subset_closedBall_lt 0 0`.

Set `χ : ContDiffBump (0 : ℝ)` to `⟨R, R + 1, hR0, by linarith⟩`. Establish `key` using `contDiffOn_convolution_right_with_param_comp (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (ContinuousLinearMap.mul ℝ ℂ) (s := (Set.univ : Set P)) (v := fun _ => (0 : ℝ)) contDiffOn_const (f := f) (μ := volume) (g := fun p z => (χ (-z) : ℂ) * Φ (p, -z)) (k := Metric.closedBall 0 (R + 1)) isOpen_univ …`. Rewrite `key` using `[contDiffOn_univ]`. Use `key using 2 with p` and compare the differences between its conclusion and the goal. Rewrite using `[convolution_def, intervalIntegral.integral_of_le zero_le_one, ← integral_indicator measurableSet_Ioc]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [ContinuousLinearMap.mul_apply', zero_sub, neg_neg, f]`. Distinguish the cases in `hx : x ∈ Set.Ioc (0 : ℝ) 1`. Establish `hxK : x ∈ K` using `Set.Ioc_subset_Icc_self hx`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem hx, χ.one_of_mem_closedBall (hR hxK)]`.

Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]`. Simplify using the standard rewrite rules. Introduce `p z _ hz`. Establish `: χ (-z) = 0`.

Apply `χ.zero_of_le_dist` to reduce the goal to its premises. Simplify using `only [Metric.mem_closedBall, dist_zero_right, not_le] at hz`. Simplify `hz.le` using `[χ]`. Simplify using `[this]`. Use `ContDiff.contDiffOn ?_` and prove the remaining obligations.

Establish `h1 : ContDiff ℝ ∞ fun q : P × ℝ => ((χ (-q.2) : ℝ) : ℂ)` using `Complex.ofRealCLM.contDiff.comp (χ.contDiff.comp contDiff_snd.neg)`. Conclude with `h1.mul (hΦ.comp (contDiff_fst.prodMk contDiff_snd.neg))`.
-/
theorem contDiff_intervalIntegral_unit {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ fun p => ∫ t in (0 : ℝ)..1, Φ (p, t) := by
  let f : ℝ → ℂ := Set.indicator (Set.Ioc (0 : ℝ) 1) fun _ => (1 : ℂ)
  have hf : Integrable f volume :=
    by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Ioc
    first
    | exact integrableOn_const (by simp)
    | exact integrableOn_const.2 (Or.inr (by simp))
    | exact (continuous_const.integrableOn_Icc (a := (0:ℝ)) (b := 1)).mono_set Set.Ioc_subset_Icc_self
  let K : Set ℝ := Set.Icc 0 1
  have hK : IsCompact K := isCompact_Icc
  obtain ⟨R, hR0, hR⟩ := hK.isBounded.subset_closedBall_lt 0 0
  let χ : ContDiffBump (0 : ℝ) := ⟨R, R + 1, hR0, by linarith⟩
  have key := contDiffOn_convolution_right_with_param_comp (𝕜 := ℝ) (n := (⊤ : ℕ∞))
    (ContinuousLinearMap.mul ℝ ℂ) (s := (Set.univ : Set P)) (v := fun _ => (0 : ℝ)) contDiffOn_const
    (f := f) (μ := volume) (g := fun p z => (χ (-z) : ℂ) * Φ (p, -z))
    (k := Metric.closedBall 0 (R + 1)) isOpen_univ (isCompact_closedBall _ _) ?_ hf.locallyIntegrable ?_
  · rw [contDiffOn_univ] at key
    convert key using 2 with p
    rw [convolution_def, intervalIntegral.integral_of_le zero_le_one, ← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearMap.mul_apply', zero_sub, neg_neg, f]
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
    · have hxK : x ∈ K := Set.Ioc_subset_Icc_self hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, χ.one_of_mem_closedBall (hR hxK)]; simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp
  · intro p z _ hz
    have : χ (-z) = 0 := by
      apply χ.zero_of_le_dist
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hz
      simpa [χ] using hz.le
    simp [this]
  · refine ContDiff.contDiffOn ?_
    have h1 : ContDiff ℝ ∞ fun q : P × ℝ => ((χ (-q.2) : ℝ) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp (χ.contDiff.comp contDiff_snd.neg)
    exact h1.mul (hΦ.comp (contDiff_fst.prodMk contDiff_snd.neg))

/- English proof (translation)
Use `set e : A0 k := (‖b‖ ^ 2)⁻¹ • b with he`. Establish `heb : ⟪e, b⟫_ℝ = 1`. Establish `hb2 : (‖b‖ ^ 2 : ℝ) ≠ 0` using `by positivity`. Rewrite using `[he, real_inner_smul_left, real_inner_self_eq_norm_sq, inv_mul_cancel₀ hb2]`. Establish `hdN : ContDiff ℝ ∞ (fderiv ℝ N)` using `hN.fderiv_right (by simp)`.

Establish `hD : Differentiable ℝ N` using `hN.differentiable (by simp)`. Set `γ : A0 k → ℝ → A0 k` to `fun x t => x - ⟪x, b⟫_ℝ • e + t • (⟪x, b⟫_ℝ • e)`. Use `⟨fun x => ∫ t in (0 : ℝ)..1, fderiv ℝ N (γ x t) e, ?_, ?_⟩` and prove the remaining obligations. Use `contDiff_intervalIntegral_unit (Φ := fun q : A0 k × ℝ => fderiv ℝ N (γ q.1 q.2) e) ?_` and prove the remaining obligations. Establish `hγ : ContDiff ℝ ∞ fun q : A0 k × ℝ => γ q.1 q.2`.

Establish `hi : ContDiff ℝ ∞ fun q : A0 k × ℝ => ⟪q.1, b⟫_ℝ` using `contDiff_fst.inner ℝ contDiff_const`. Conclude with `(contDiff_fst.sub (hi.smul contDiff_const)).add (contDiff_snd.smul (hi.smul contDiff_const))`. Conclude with `(hdN.comp hγ).clm_apply contDiff_const`. Introduce `x set s : ℝ := ⟪x, b⟫_ℝ with hs`. Establish `hy : ⟪x - s • e, b⟫_ℝ = 0`.

Rewrite using `[inner_sub_left, real_inner_smul_left, heb, hs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => N (x - s • e + t • (s • e))) (fderiv ℝ N (γ x t) (s • e)) t`. Introduce `t _`. Establish `h1 : HasDerivAt (fun t : ℝ => x - s • e + t • (s • e)) (s • e) t`.

Simplify using `using ((hasDerivAt_id t).smul_const (s • e)).const_add (x - s • e)`. Conclude with `(hD _).hasFDerivAt.comp_hasDerivAt t h1`. Establish `hcont : Continuous fun t : ℝ => fderiv ℝ N (γ x t) (s • e)`. Establish `: Continuous fun t : ℝ => γ x t` using `by fun_prop`. Conclude with `((hdN.continuous.comp this).clm_apply continuous_const)`.

Establish `hftc` using `intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)`. Simplify using `only [zero_smul, add_zero, one_smul, sub_add_cancel] at hftc`. Rewrite `hftc` using `[hz _ hy, sub_zero]`. Rewrite using `[← hftc]`. Repeatedly rewrite using `[ContinuousLinearMap.map_smul, Complex.real_smul]`.

Rewrite using `[intervalIntegral.integral_const_mul]`.
-/
theorem hadamard_div_linear {k : ℕ} (b : A0 k) (N : A0 k → ℂ) (hb : b ≠ 0) (hN : ContDiff ℝ ∞ N)
    (hz : ∀ x, ⟪x, b⟫_ℝ = 0 → N x = 0) :
    ∃ F : A0 k → ℂ, ContDiff ℝ ∞ F ∧ ∀ x, N x = (⟪x, b⟫_ℝ : ℂ) * F x := by
  set e : A0 k := (‖b‖ ^ 2)⁻¹ • b with he
  have heb : ⟪e, b⟫_ℝ = 1 := by
    have hb2 : (‖b‖ ^ 2 : ℝ) ≠ 0 := by positivity
    rw [he, real_inner_smul_left, real_inner_self_eq_norm_sq, inv_mul_cancel₀ hb2]
  have hdN : ContDiff ℝ ∞ (fderiv ℝ N) := hN.fderiv_right (by simp)
  have hD : Differentiable ℝ N := hN.differentiable (by simp)
  let γ : A0 k → ℝ → A0 k := fun x t => x - ⟪x, b⟫_ℝ • e + t • (⟪x, b⟫_ℝ • e)
  refine ⟨fun x => ∫ t in (0 : ℝ)..1, fderiv ℝ N (γ x t) e, ?_, ?_⟩
  · refine contDiff_intervalIntegral_unit (Φ := fun q : A0 k × ℝ => fderiv ℝ N (γ q.1 q.2) e) ?_
    have hγ : ContDiff ℝ ∞ fun q : A0 k × ℝ => γ q.1 q.2 := by
      have hi : ContDiff ℝ ∞ fun q : A0 k × ℝ => ⟪q.1, b⟫_ℝ := contDiff_fst.inner ℝ contDiff_const
      exact (contDiff_fst.sub (hi.smul contDiff_const)).add (contDiff_snd.smul (hi.smul contDiff_const))
    exact (hdN.comp hγ).clm_apply contDiff_const
  · intro x
    set s : ℝ := ⟪x, b⟫_ℝ with hs
    have hy : ⟪x - s • e, b⟫_ℝ = 0 := by
      rw [inner_sub_left, real_inner_smul_left, heb, hs]; ring
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => N (x - s • e + t • (s • e))) (fderiv ℝ N (γ x t) (s • e)) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => x - s • e + t • (s • e)) (s • e) t := by
        simpa using ((hasDerivAt_id t).smul_const (s • e)).const_add (x - s • e)
      exact (hD _).hasFDerivAt.comp_hasDerivAt t h1
    have hcont : Continuous fun t : ℝ => fderiv ℝ N (γ x t) (s • e) := by
      have : Continuous fun t : ℝ => γ x t := by fun_prop
      exact ((hdN.continuous.comp this).clm_apply continuous_const)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)
    simp only [zero_smul, add_zero, one_smul, sub_add_cancel] at hftc
    rw [hz _ hy, sub_zero] at hftc
    rw [← hftc]
    simp_rw [ContinuousLinearMap.map_smul, Complex.real_smul]
    rw [intervalIntegral.integral_const_mul]

end GlobalTheory.Chamber
