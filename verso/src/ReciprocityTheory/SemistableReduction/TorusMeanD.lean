import ReciprocityTheory.SemistableReduction.TorusMeanC

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Real Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `hu : ∀ t, tmLog f (update θ i t) = Real.log ‖(tmSlice i (torusPoint θ) f).eval (circPt t)‖` using `tmLog_update f θ i`. Establish `hL : 0 ≤ posLog (∑ s ∈ f.support, ‖f.coeff s‖)` using `posLog_nonneg`. Establish `hI : Integrable (fun t => tmLog f (update θ i t)) unitIntervalMeasure`. Repeatedly rewrite using `[hu]`. Conclude with `integrableOn_log_circ _`.

Establish `h1 : ∫ t, ‖tmLog f (update θ i t)‖ ∂unitIntervalMeasure ≤ ∫ t, (2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) - tmLog f (update θ i t)) ∂unitIntervalMeasure`. Use `integral_mono hI.norm ((integrable_const _).sub hI) fun t => ?_` and prove the remaining obligations. Use `tmLog_le f (update θ i t)` as an intermediate fact. Simplify using `only [Real.norm_eq_abs]`. Apply the tactic sequence `rcases abs_cases (tmLog f (update θ i t)) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith`.

Establish `h2 : ∫ t, (2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) - tmLog f (update θ i t)) ∂unitIntervalMeasure = 2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) - (tmSlice i (torusPoint θ) f).logMahlerMeasure`. Rewrite using `[integral_sub (integrable_const _) hI, integral_const]`. Repeatedly rewrite using `[hu]`. Rewrite using `[integral_log_circ]`. Simplify using the standard rewrite rules.

Establish `h3 : |Real.log ‖(tmSlice i (torusPoint θ) f).leadingCoeff‖| ≤ ∑ k ∈ Finset.range (f.support.sup (fun s => s i) + 1), |tmLog (coeffIn i k f) θ|`. Rewrite using `[Polynomial.leadingCoeff, tmSlice_coeff]`. Distinguish the cases in `hn : (tmSlice i (torusPoint θ) f).natDegree < f.support.sup (fun s => s i) + 1`. Conclude with `Finset.single_le_sum (f := fun k => |tmLog (coeffIn i k f) θ|) (fun k _ => abs_nonneg _) (Finset.mem_range.mpr hn)`. Rewrite using `[coeffIn_eq_zero_of_lt i f _ (by omega)]`.

Simplify using `only [map_zero, norm_zero, Real.log_zero, abs_zero]`. Conclude with `Finset.sum_nonneg fun k _ => abs_nonneg _`. Establish `h4` using `log_norm_leadingCoeff_le (tmSlice i (torusPoint θ) f)`. Establish `h5` using `neg_abs_le (Real.log ‖(tmSlice i (torusPoint θ) f).leadingCoeff‖)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma slice_abs_integral_le (f : MvPolynomial ι ℂ) (i : ι) (θ : ι → ℝ) :
    ∫ t, ‖tmLog f (update θ i t)‖ ∂unitIntervalMeasure ≤
      2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) +
        ∑ k ∈ Finset.range (f.support.sup (fun s => s i) + 1), |tmLog (coeffIn i k f) θ| := by
  have hu : ∀ t, tmLog f (update θ i t) =
      Real.log ‖(tmSlice i (torusPoint θ) f).eval (circPt t)‖ := tmLog_update f θ i
  have hL : 0 ≤ posLog (∑ s ∈ f.support, ‖f.coeff s‖) := posLog_nonneg
  have hI : Integrable (fun t => tmLog f (update θ i t)) unitIntervalMeasure := by
    simp_rw [hu]; exact integrableOn_log_circ _
  have h1 : ∫ t, ‖tmLog f (update θ i t)‖ ∂unitIntervalMeasure ≤
      ∫ t, (2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) - tmLog f (update θ i t)) ∂unitIntervalMeasure := by
    refine integral_mono hI.norm ((integrable_const _).sub hI) fun t => ?_
    have := tmLog_le f (update θ i t)
    simp only [Real.norm_eq_abs]
    rcases abs_cases (tmLog f (update θ i t)) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have h2 : ∫ t, (2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) - tmLog f (update θ i t)) ∂unitIntervalMeasure =
      2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) -
        (tmSlice i (torusPoint θ) f).logMahlerMeasure := by
    rw [integral_sub (integrable_const _) hI, integral_const]
    simp_rw [hu]
    rw [integral_log_circ]
    simp
  have h3 : |Real.log ‖(tmSlice i (torusPoint θ) f).leadingCoeff‖| ≤
      ∑ k ∈ Finset.range (f.support.sup (fun s => s i) + 1), |tmLog (coeffIn i k f) θ| := by
    rw [Polynomial.leadingCoeff, tmSlice_coeff]
    by_cases hn : (tmSlice i (torusPoint θ) f).natDegree < f.support.sup (fun s => s i) + 1
    · exact Finset.single_le_sum (f := fun k => |tmLog (coeffIn i k f) θ|)
        (fun k _ => abs_nonneg _) (Finset.mem_range.mpr hn)
    · rw [coeffIn_eq_zero_of_lt i f _ (by omega)]
      simp only [map_zero, norm_zero, Real.log_zero, abs_zero]
      exact Finset.sum_nonneg fun k _ => abs_nonneg _
  have h4 := log_norm_leadingCoeff_le (tmSlice i (torusPoint θ) f)
  have h5 := neg_abs_le (Real.log ‖(tmSlice i (torusPoint θ) f).leadingCoeff‖)
  linarith

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `f hS`. Establish `: tmLog f = fun _ => Real.log ‖MvPolynomial.constantCoeff f‖`. Use function extensionality and compare the values at `θ`.

Simplify using `[tmLog, eval_const_of_vars_empty f hS]`. Rewrite using `[this]`. Conclude with `integrable_const _`. Consider the case `insert i S' hi ih`. Introduce `f hS`.

Establish `hsub : ∀ k, (coeffIn i k f).vars ⊆ S'`. Introduce `k j hj`. Establish `h1` using `vars_coeffIn_subset i k f hj`. Rewrite `h1` using `[Finset.mem_erase]`. Establish `h2` using `hS h1.2`.

Rewrite `h2` using `[Finset.mem_insert]`. Conclude with `h2.resolve_left h1.1`. Establish `hmeas : AEStronglyMeasurable (tmLog f ∘ tmUpd i) ((torusProb ι).prod unitIntervalMeasure)` using `((measurable_tmLog f).comp (measurable_tmUpd i)).aestronglyMeasurable`. Rewrite using `[← tm_integrable_comp i (measurable_tmLog f).aestronglyMeasurable, integrable_prod_iff hmeas]`. Use `⟨Filter.Eventually.of_forall fun θ => ?_, ?_⟩` and prove the remaining obligations.

Use `show Integrable (fun t => tmLog f (update θ i t)) unitIntervalMeasure`. Repeatedly rewrite using `[tmLog_update]`. Conclude with `integrableOn_log_circ _`. Establish `hG : Integrable (fun θ => 2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) + ∑ k ∈ Finset.range (f.support.sup (fun s => s i) + 1), |tmLog (coeffIn i k f) θ|) (torusProb ι)` using `(integrable_const _).add (integrable_finsetSum _ fun k _ => (ih _ (hsub k)).abs)`. Use `hG.mono' hmeas.norm.integral_prod_right' (Filter.Eventually.of_forall fun θ => ?_)` and prove the remaining obligations.

Rewrite using `[Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]`. Conclude with `slice_abs_integral_le f i θ`.
-/
lemma integrable_log_abs_on_torus (S : Finset ι) :
    ∀ f : MvPolynomial ι ℂ, f.vars ⊆ S → Integrable (tmLog f) (torusProb ι) := by
  induction S using Finset.induction_on with
  | empty =>
    intro f hS
    have : tmLog f = fun _ => Real.log ‖MvPolynomial.constantCoeff f‖ := by
      funext θ; simp [tmLog, eval_const_of_vars_empty f hS]
    rw [this]; exact integrable_const _
  | insert i S' hi ih =>
    intro f hS
    have hsub : ∀ k, (coeffIn i k f).vars ⊆ S' := by
      intro k j hj
      have h1 := vars_coeffIn_subset i k f hj
      rw [Finset.mem_erase] at h1
      have h2 := hS h1.2
      rw [Finset.mem_insert] at h2
      exact h2.resolve_left h1.1
    have hmeas : AEStronglyMeasurable (tmLog f ∘ tmUpd i) ((torusProb ι).prod unitIntervalMeasure) :=
      ((measurable_tmLog f).comp (measurable_tmUpd i)).aestronglyMeasurable
    rw [← tm_integrable_comp i (measurable_tmLog f).aestronglyMeasurable,
      integrable_prod_iff hmeas]
    refine ⟨Filter.Eventually.of_forall fun θ => ?_, ?_⟩
    · show Integrable (fun t => tmLog f (update θ i t)) unitIntervalMeasure
      simp_rw [tmLog_update]
      exact integrableOn_log_circ _
    · have hG : Integrable (fun θ => 2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) +
          ∑ k ∈ Finset.range (f.support.sup (fun s => s i) + 1), |tmLog (coeffIn i k f) θ|)
          (torusProb ι) :=
        (integrable_const _).add (integrable_finsetSum _ fun k _ => (ih _ (hsub k)).abs)
      refine hG.mono' hmeas.norm.integral_prod_right' (Filter.Eventually.of_forall fun θ => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact slice_abs_integral_le f i θ

/- English proof (translation)
The claim follows from `integrable_log_abs_on_torus Finset.univ f (Finset.subset_univ _)`.
-/
lemma tm_int (f : MvPolynomial ι ℂ) : Integrable (tmLog f) (torusProb ι) :=
  integrable_log_abs_on_torus Finset.univ f (Finset.subset_univ _)

/- English proof (translation)
Rewrite using `[ae_iff]`. Simplify using `using tm_null f hf`.
-/
lemma tm_ae_ne (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    ∀ᵐ θ ∂(torusProb ι), MvPolynomial.eval (torusPoint θ) f ≠ 0 := by
  rw [ae_iff]; simpa using tm_null f hf

end ReciprocityTheory.MultiplicativeHeights
