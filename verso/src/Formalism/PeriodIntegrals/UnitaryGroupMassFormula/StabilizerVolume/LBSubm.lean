import Mathlib

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology Set Filter
open scoped ENNReal

def SubmLB : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f → ∀ x0,
      Function.Surjective (fderiv ℝ f x0) → ∀ W : Set (Fin n → ℝ), IsOpen W → x0 ∈ W →
      ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 (f x0), ∀ S ⊆ N, MeasurableSet S →
        c * ν S ≤ μ (f ⁻¹' S ∩ W)

/- English proof (translation)
Take `⟨g, hg⟩` from `LinearMap.exists_rightInverse_of_surjective (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (LinearMap.range_eq_top.mpr hA)`. Use `⟨LinearMap.toContinuousLinearMap g, fun y => ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun hg y` as an intermediate fact. Simplify using `using this`.
-/
private theorem exists_clm_rightInverse_of_surjective {n m : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) (hA : Function.Surjective A) :
    ∃ R : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ), ∀ y, A (R y) = y := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (LinearMap.range_eq_top.mpr hA)
  refine ⟨LinearMap.toContinuousLinearMap g, fun y => ?_⟩
  have := LinearMap.congr_fun hg y
  simpa using this

/- English proof (translation)
Establish `hZ : IsOpen {x : Fin n → ℝ | ‖x - R (A x) - (p - R (A p))‖ < r}`. Conclude with `isOpen_lt (by fun_prop) continuous_const`. Establish `hAm : Measurable A` using `A.continuous.measurable`. Establish `key : ∀ x t, x + R t - R (A (x + R t)) = x - R (A x)`. Introduce `x t`.

Rewrite using `[map_add, hAR, map_add]`. Normalize the expressions using the abelian group laws. Establish `happ : ∀ S, MeasurableSet S → Measure.map A (μ.restrict {x | ‖x - R (A x) - (p - R (A p))‖ < r}) S = μ (A ⁻¹' S ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r})`. Introduce `S hS`. Rewrite using `[Measure.map_apply hAm hS, Measure.restrict_apply (hAm hS)]`.

Use `{ lt_top_of_isCompact := ?_, map_add_left_eq_self := ?_, open_pos := ?_ }` and prove the remaining obligations. Introduce `K hK`. Rewrite using `[happ K hK.measurableSet]`. Take `⟨C, hC⟩` from `isBounded_iff_forall_norm_le.1 hK.isBounded`. Establish `hsub : A ⁻¹' K ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r} ⊆ Metric.closedBall (0 : Fin n → ℝ) (‖R‖ * C + (‖p - R (A p)‖ + r))`.

Introduce `x hx`. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Establish `h1 : ‖A x‖ ≤ C` using `hC _ hx.1`. Establish `h2 : ‖x - R (A x) - (p - R (A p))‖ < r` using `hx.2`. Establish `h3 : ‖R (A x)‖ ≤ ‖R‖ * C` using `(R.le_opNorm _).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))`.

Establish `h4 : ‖x - R (A x)‖ ≤ ‖x - R (A x) - (p - R (A p))‖ + ‖p - R (A p)‖`. Establish `e : x - R (A x) = (x - R (A x) - (p - R (A p))) + (p - R (A p))` using `by abel`. Combine the equalities or inequalities in the displayed calculation. Establish `e' : x = R (A x) + (x - R (A x))` using `by abel`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `(measure_mono hsub).trans_lt measure_closedBall_lt_top`. Introduce `t`. Use extensionality with `S hS`. Rewrite using `[Measure.map_apply (measurable_const_add t) hS, happ _ (measurable_const_add t hS), happ S hS]`. Establish `hset : A ⁻¹' ((fun y => t + y) ⁻¹' S) ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r} = (fun x => x + R t) ⁻¹' (A ⁻¹' S ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r})`.

Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq]`. Rewrite using `[key x t, map_add, hAR, add_comm t (A x)]`. Rewrite using `[hset, measure_preimage_add_right]`. Introduce `O hO hne`.

Rewrite using `[happ O hO.measurableSet]`. Take `⟨y, hy⟩` from `hne`. Establish `hopen : IsOpen (A ⁻¹' O ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r})` using `(hO.preimage A.continuous).inter hZ`. Establish `hA1 : A (R y + (p - R (A p))) = y`. Rewrite using `[map_add, map_sub, hAR, hAR, sub_self, add_zero]`.

Establish `hmem : R y + (p - R (A p)) ∈ A ⁻¹' O ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r}`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show A (R y + (p - R (A p))) ∈ O`. Rewrite using `[hA1]`. Conclude with `hy`.

Use `show ‖R y + (p - R (A p)) - R (A (R y + (p - R (A p)))) - (p - R (A p))‖ < r`. Rewrite using `[hA1]`. Establish `e : R y + (p - R (A p)) - R y - (p - R (A p)) = 0` using `by abel`. Rewrite using `[e, norm_zero]`. Conclude with `hr`.

Conclude with `hopen.measure_ne_zero μ ⟨_, hmem⟩`.
-/
private theorem isAddHaarMeasure_map_restrict_slab {n m : ℕ} (μ : Measure (Fin n → ℝ))
    [μ.IsAddHaarMeasure] (A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ))
    (R : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (hAR : ∀ y, A (R y) = y) (p : Fin n → ℝ)
    {r : ℝ} (hr : 0 < r) :
    (Measure.map A (μ.restrict {x | ‖x - R (A x) - (p - R (A p))‖ < r})).IsAddHaarMeasure := by
  have hZ : IsOpen {x : Fin n → ℝ | ‖x - R (A x) - (p - R (A p))‖ < r} := by
    exact isOpen_lt (by fun_prop) continuous_const
  have hAm : Measurable A := A.continuous.measurable
  have key : ∀ x t, x + R t - R (A (x + R t)) = x - R (A x) := by
    intro x t; rw [map_add, hAR, map_add]; abel
  have happ : ∀ S, MeasurableSet S →
      Measure.map A (μ.restrict {x | ‖x - R (A x) - (p - R (A p))‖ < r}) S
        = μ (A ⁻¹' S ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r}) := by
    intro S hS
    rw [Measure.map_apply hAm hS, Measure.restrict_apply (hAm hS)]
  refine { lt_top_of_isCompact := ?_, map_add_left_eq_self := ?_, open_pos := ?_ }
  · intro K hK
    rw [happ K hK.measurableSet]
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hK.isBounded
    have hsub : A ⁻¹' K ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r} ⊆
        Metric.closedBall (0 : Fin n → ℝ) (‖R‖ * C + (‖p - R (A p)‖ + r)) := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖A x‖ ≤ C := hC _ hx.1
      have h2 : ‖x - R (A x) - (p - R (A p))‖ < r := hx.2
      have h3 : ‖R (A x)‖ ≤ ‖R‖ * C :=
        (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
      have h4 : ‖x - R (A x)‖ ≤ ‖x - R (A x) - (p - R (A p))‖ + ‖p - R (A p)‖ := by
        have e : x - R (A x) = (x - R (A x) - (p - R (A p))) + (p - R (A p)) := by abel
        calc ‖x - R (A x)‖ = ‖(x - R (A x) - (p - R (A p))) + (p - R (A p))‖ := by rw [← e]
          _ ≤ _ := norm_add_le _ _
      have e' : x = R (A x) + (x - R (A x)) := by abel
      calc ‖x‖ = ‖R (A x) + (x - R (A x))‖ := by rw [← e']
        _ ≤ ‖R (A x)‖ + ‖x - R (A x)‖ := norm_add_le _ _
        _ ≤ ‖R‖ * C + (‖p - R (A p)‖ + r) := by linarith
    exact (measure_mono hsub).trans_lt measure_closedBall_lt_top
  · intro t
    ext S hS
    rw [Measure.map_apply (measurable_const_add t) hS, happ _ (measurable_const_add t hS),
      happ S hS]
    have hset : A ⁻¹' ((fun y => t + y) ⁻¹' S) ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r}
        = (fun x => x + R t) ⁻¹' (A ⁻¹' S ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r}) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [key x t, map_add, hAR, add_comm t (A x)]
    rw [hset, measure_preimage_add_right]
  · intro O hO hne
    rw [happ O hO.measurableSet]
    obtain ⟨y, hy⟩ := hne
    have hopen : IsOpen (A ⁻¹' O ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r}) :=
      (hO.preimage A.continuous).inter hZ
    have hA1 : A (R y + (p - R (A p))) = y := by
      rw [map_add, map_sub, hAR, hAR, sub_self, add_zero]
    have hmem : R y + (p - R (A p)) ∈ A ⁻¹' O ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r} := by
      refine ⟨?_, ?_⟩
      · show A (R y + (p - R (A p))) ∈ O
        rw [hA1]; exact hy
      · show ‖R y + (p - R (A p)) - R (A (R y + (p - R (A p)))) - (p - R (A p))‖ < r
        rw [hA1]
        have e : R y + (p - R (A p)) - R y - (p - R (A p)) = 0 := by abel
        rw [e, norm_zero]; exact hr
    exact hopen.measure_ne_zero μ ⟨_, hmem⟩

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `n m μ ν hμ hν f hf x0 hsurj W hW hx0W`. Use `hμ` as an intermediate fact. Use `hν` as an intermediate fact. Take `⟨A, hAdef⟩ : ∃ A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ), A = fderiv ℝ f x0` from `⟨_, rfl⟩`. Rewrite `hsurj` using `[← hAdef]`.

Take `⟨R, hAR⟩` from `exists_clm_rightInverse_of_surjective A hsurj`. Establish `hfd : HasStrictFDerivAt f A x0`. Rewrite using `[hAdef]; exact hf.contDiffAt.hasStrictFDerivAt (by norm_num)`. Take `⟨h, hhdef⟩ : ∃ h : (Fin n → ℝ) → (Fin n → ℝ), h = fun x => x + R (f x - A x) + (R (A x0) - R (f x0))` from `⟨_, rfl⟩`. Establish `hfh : ∀ x, f x = A (h x) + (f x0 - A x0)`.

Introduce `x`. Rewrite using `[hhdef]`. Simplify using `only [map_add, map_sub, hAR]`. Normalize the expressions using the abelian group laws. Establish `hhx0 : h x0 = x0`.

Rewrite using `[hhdef]`. Simplify using `only [map_sub]`. Normalize the expressions using the abelian group laws. Establish `hC : ContDiff ℝ 1 h`. Rewrite using `[hhdef]`.

Conclude with `(contDiff_id.add (R.contDiff.comp (hf.sub A.contDiff))).add contDiff_const`. Establish `hh : HasStrictFDerivAt h ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x0`. Establish `h1 : HasStrictFDerivAt (fun x => f x - A x) (A - A) x0` using `hfd.sub A.hasStrictFDerivAt`. Establish `h2` using `((hasStrictFDerivAt_id x0).add (R.hasStrictFDerivAt.comp x0 h1)).add_const (R (A x0) - R (f x0))`. Rewrite using `[hhdef]`.

Apply the tactic sequence `convert h2 using 1 <;> first | rfl | (funext x; simp) | (ext v; simp) | (ext v i; simp)`. Establish `hdiff : Differentiable ℝ h` using `hC.differentiable (by norm_num)`. Establish `hdet : Continuous fun x => (fderiv ℝ h x).det` using `ContinuousLinearMap.continuous_det.comp (hC.continuous_fderiv (by norm_num))`. Establish `hdet0 : (fderiv ℝ h x0).det = 1`. Rewrite using `[hh.hasFDerivAt.fderiv]`.

Use `first`. Consider the case `simp [ContinuousLinearMap.det]`. Consider the case `simp`. Consider the case `norm_num [ContinuousLinearMap.det, LinearMap.det_id]`. Take `⟨U0, hU0⟩ : ∃ U0 : Set (Fin n → ℝ), U0 = W ∩ {x | |(fderiv ℝ h x).det| < 2}` from `⟨_, rfl⟩`.

Establish `hU0open : IsOpen U0`. Rewrite using `[hU0]`. Conclude with `hW.inter (isOpen_lt (continuous_abs.comp hdet) continuous_const)`. Establish `hx0U0 : x0 ∈ U0`. Rewrite using `[hU0]`.

Use `⟨hx0W, ?_⟩` and prove the remaining obligations. Use `show |(fderiv ℝ h x0).det| < 2`. Rewrite using `[hdet0]`. Evaluate the numerical expressions. Establish `hU0W : U0 ⊆ W` using `by rw [hU0]; exact Set.inter_subset_left`.

Establish `hU0det : ∀ x ∈ U0, |(fderiv ℝ h x).det| < 2`. Rewrite using `[hU0]`. Conclude with `fun x hx => hx.2`. Establish `himg : h '' U0 ∈ 𝓝 x0`. Establish `hmap : Filter.map h (𝓝 x0) = 𝓝 (h x0)` using `hh.map_nhds_eq_of_equiv`.

Establish `: h '' U0 ∈ Filter.map h (𝓝 x0)` using `Filter.image_mem_map (hU0open.mem_nhds hx0U0)`. Rewrite `this` using `[hmap, hhx0]`. Then use the resulting hypothesis. Take `⟨δ, hδ, hball⟩` from `Metric.mem_nhds_iff.1 himg`. Take `⟨r, hr, hrδ⟩ : ∃ r : ℝ, 0 < r ∧ r + r = δ` from `⟨δ / 2, by linarith, by ring⟩`. Take `⟨ρ, hρdef⟩ : ∃ ρ : Measure (Fin m → ℝ), ρ = Measure.map A (μ.restrict {x | ‖x - R (A x) - (x0 - R (A x0))‖ < r})` from `⟨_, rfl⟩`.

Establish `hρ : ρ.IsAddHaarMeasure`. Rewrite using `[hρdef]`. Conclude with `isAddHaarMeasure_map_restrict_slab μ A R hAR x0 hr`. Choose the witnesses or unpack the hypotheses as in `⟨c0, hc0pos, hρeq⟩ : ∃ c0 : NNReal, 0 < c0 ∧ ρ = c0 • ν := by`. Use `⟨ρ.addHaarScalarFactor ν, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ρ ν, ?_⟩` and prove the remaining obligations.

Use `first`. Consider the case `exact Measure.isAddLeftInvariant_eq_smul ρ ν`. Consider the case `exact Measure.isAddHaarMeasure_eq_smul_of_isAddHaarMeasure ρ ν`. Consider the case `exact Measure.isAddLeftInvariant_eq_smul_of_innerRegular ρ ν`. Consider the case `exact Measure.isAddLeftInvariant_eq_smul_of_regular ρ ν`.

Establish `hK0 : ENNReal.ofReal 2 ≠ 0` using `(ENNReal.ofReal_pos.2 two_pos).ne'`. Establish `hpos : (0 : ℝ) < ‖R‖ + 1` using `by positivity`. Use `⟨(ENNReal.ofReal 2)⁻¹ * c0, ?_, ?_, Metric.ball (f x0) (r / (‖R‖ + 1)), Metric.ball_mem_nhds _ (div_pos hr hpos), ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top) (ENNReal.coe_ne_zero.2 hc0pos.ne')`.

Consider the case `(apply ENNReal.mul_pos <;> simp [hc0pos.ne'])`. Conclude with `ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hK0) ENNReal.coe_ne_top`. Introduce `S hSN hS`. Establish `hAm : Measurable A` using `A.continuous.measurable`. Establish `hS'' : MeasurableSet ((fun y => y + (f x0 - A x0)) ⁻¹' S)` using `measurable_add_const _ hS`.

Establish `hM : MeasurableSet (f ⁻¹' S ∩ U0)` using `(hf.continuous.measurable hS).inter hU0open.measurableSet`. Establish `hsub : A ⁻¹' ((fun y => y + (f x0 - A x0)) ⁻¹' S) ∩ {x | ‖x - R (A x) - (x0 - R (A x0))‖ < r} ⊆ h '' (f ⁻¹' S ∩ U0)`. Introduce and unpack `u ⟨huS, huZ⟩`. Establish `huS' : A u + (f x0 - A x0) ∈ S` using `huS`. Establish `huZ' : ‖u - R (A u) - (x0 - R (A x0))‖ < r` using `huZ`.

Establish `hN` using `hSN huS'`. Rewrite `hN` using `[Metric.mem_ball, dist_eq_norm]`. Establish `e1 : A u + (f x0 - A x0) - f x0 = A (u - x0)` using `by rw [map_sub]; abel`. Rewrite `hN` using `[e1]`. Establish `e2 : u - x0 = R (A (u - x0)) + (u - R (A u) - (x0 - R (A x0)))`.

Rewrite using `[map_sub, map_sub]`. Normalize the expressions using the abelian group laws. Establish `hne : ‖R‖ + 1 ≠ 0` using `hpos.ne'`. Establish `hR1 : ‖R (A (u - x0))‖ ≤ r`. Establish `ht` using `norm_nonneg (A (u - x0))`.

Combine the equalities or inequalities in the displayed calculation. Establish `hu : u ∈ Metric.ball x0 δ`. Rewrite using `[Metric.mem_ball, dist_eq_norm, e2]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨x, hxU0, rfl⟩` from `hball hu`.

Use `⟨x, ⟨?_, hxU0⟩, rfl⟩` and prove the remaining obligations. Use `show f x ∈ S`. Rewrite using `[hfh x]`. Conclude with `huS'`. Establish `h1 : ν S = ν ((fun y => y + (f x0 - A x0)) ⁻¹' S)` using `(measure_preimage_add_right ν _ S).symm`.

Establish `h2 : ρ ((fun y => y + (f x0 - A x0)) ⁻¹' S) = (c0 : ℝ≥0∞) * ν ((fun y => y + (f x0 - A x0)) ⁻¹' S)`. Rewrite using `[hρeq]`. Use `first`. Consider the case `exact Measure.nnreal_smul_coe_apply _ _ _`. Consider the case `simp`.

Consider the case `rfl`. Establish `h3 : ρ ((fun y => y + (f x0 - A x0)) ⁻¹' S) = μ (A ⁻¹' ((fun y => y + (f x0 - A x0)) ⁻¹' S) ∩ {x | ‖x - R (A x) - (x0 - R (A x0))‖ < r})`. Rewrite using `[hρdef, Measure.map_apply hAm hS'', Measure.restrict_apply (hAm hS'')]`. Establish `h5 : μ (h '' (f ⁻¹' S ∩ U0)) ≤ ∫⁻ x in f ⁻¹' S ∩ U0, ENNReal.ofReal |(fderiv ℝ h x).det| ∂μ` using `by first`. Consider the case `exact addHaar_image_le_lintegral_abs_det_fderiv μ hM (fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt)`.

Consider the case `exact addHaar_image_le_lintegral_abs_det_fderiv hM (fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt)`. Establish `h6 : ∫⁻ x in f ⁻¹' S ∩ U0, ENNReal.ofReal |(fderiv ℝ h x).det| ∂μ ≤ ∫⁻ _ in f ⁻¹' S ∩ U0, ENNReal.ofReal 2 ∂μ`. Establish `hle : ∀ x ∈ f ⁻¹' S ∩ U0, ENNReal.ofReal |(fderiv ℝ h x).det| ≤ ENNReal.ofReal 2` using `fun x hx => ENNReal.ofReal_le_ofReal (hU0det x hx.2).le`. Use `first`. Consider the case `exact setLIntegral_mono' hM hle`.

Consider the case `exact setLIntegral_mono measurable_const hle`. Consider the case `exact lintegral_mono_ae ((ae_restrict_iff' hM).2 (Filter.Eventually.of_forall hle))`. Establish `h7 : ∫⁻ _ in f ⁻¹' S ∩ U0, ENNReal.ofReal 2 ∂μ = ENNReal.ofReal 2 * μ (f ⁻¹' S ∩ U0)` using `by first`. Consider the case `exact setLIntegral_const _ _`. Consider the case `rw [lintegral_const, Measure.restrict_apply_univ]`.

Establish `h8 : μ (f ⁻¹' S ∩ U0) ≤ μ (f ⁻¹' S ∩ W)` using `measure_mono (fun x hx => ⟨hx.1, hU0W hx.2⟩)`. Establish `key : (c0 : ℝ≥0∞) * ν S ≤ ENNReal.ofReal 2 * μ (f ⁻¹' S ∩ W)`. Rewrite using `[h1, ← h2, h3]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, ENNReal.inv_mul_cancel hK0 ENNReal.ofReal_ne_top, one_mul]`.
-/
theorem submLB_holds : SubmLB := by
  intro n m μ ν hμ hν f hf x0 hsurj W hW hx0W
  have := hμ
  have := hν
  obtain ⟨A, hAdef⟩ : ∃ A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ), A = fderiv ℝ f x0 := ⟨_, rfl⟩
  rw [← hAdef] at hsurj
  obtain ⟨R, hAR⟩ := exists_clm_rightInverse_of_surjective A hsurj
  have hfd : HasStrictFDerivAt f A x0 := by
    rw [hAdef]; exact hf.contDiffAt.hasStrictFDerivAt (by norm_num)
  obtain ⟨h, hhdef⟩ : ∃ h : (Fin n → ℝ) → (Fin n → ℝ),
      h = fun x => x + R (f x - A x) + (R (A x0) - R (f x0)) := ⟨_, rfl⟩
  have hfh : ∀ x, f x = A (h x) + (f x0 - A x0) := by
    intro x; rw [hhdef]; simp only [map_add, map_sub, hAR]; abel
  have hhx0 : h x0 = x0 := by
    rw [hhdef]; simp only [map_sub]; abel
  have hC : ContDiff ℝ 1 h := by
    rw [hhdef]
    exact (contDiff_id.add (R.contDiff.comp (hf.sub A.contDiff))).add contDiff_const
  have hh : HasStrictFDerivAt h
      ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x0 := by
    have h1 : HasStrictFDerivAt (fun x => f x - A x) (A - A) x0 := hfd.sub A.hasStrictFDerivAt
    have h2 := ((hasStrictFDerivAt_id x0).add (R.hasStrictFDerivAt.comp x0 h1)).add_const
      (R (A x0) - R (f x0))
    rw [hhdef]
    convert h2 using 1 <;> first | rfl | (funext x; simp) | (ext v; simp) | (ext v i; simp)
  have hdiff : Differentiable ℝ h := hC.differentiable (by norm_num)
  have hdet : Continuous fun x => (fderiv ℝ h x).det :=
    ContinuousLinearMap.continuous_det.comp (hC.continuous_fderiv (by norm_num))
  have hdet0 : (fderiv ℝ h x0).det = 1 := by
    rw [hh.hasFDerivAt.fderiv]
    first
    | simp [ContinuousLinearMap.det]
    | simp
    | norm_num [ContinuousLinearMap.det, LinearMap.det_id]
  obtain ⟨U0, hU0⟩ : ∃ U0 : Set (Fin n → ℝ), U0 = W ∩ {x | |(fderiv ℝ h x).det| < 2} :=
    ⟨_, rfl⟩
  have hU0open : IsOpen U0 := by
    rw [hU0]; exact hW.inter (isOpen_lt (continuous_abs.comp hdet) continuous_const)
  have hx0U0 : x0 ∈ U0 := by
    rw [hU0]
    refine ⟨hx0W, ?_⟩
    show |(fderiv ℝ h x0).det| < 2
    rw [hdet0]; norm_num
  have hU0W : U0 ⊆ W := by rw [hU0]; exact Set.inter_subset_left
  have hU0det : ∀ x ∈ U0, |(fderiv ℝ h x).det| < 2 := by
    rw [hU0]; exact fun x hx => hx.2
  have himg : h '' U0 ∈ 𝓝 x0 := by
    have hmap : Filter.map h (𝓝 x0) = 𝓝 (h x0) := hh.map_nhds_eq_of_equiv
    have : h '' U0 ∈ Filter.map h (𝓝 x0) := Filter.image_mem_map (hU0open.mem_nhds hx0U0)
    rwa [hmap, hhx0] at this
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 himg
  obtain ⟨r, hr, hrδ⟩ : ∃ r : ℝ, 0 < r ∧ r + r = δ := ⟨δ / 2, by linarith, by ring⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : Measure (Fin m → ℝ),
      ρ = Measure.map A (μ.restrict {x | ‖x - R (A x) - (x0 - R (A x0))‖ < r}) := ⟨_, rfl⟩
  have hρ : ρ.IsAddHaarMeasure := by
    rw [hρdef]; exact isAddHaarMeasure_map_restrict_slab μ A R hAR x0 hr
  obtain ⟨c0, hc0pos, hρeq⟩ : ∃ c0 : NNReal, 0 < c0 ∧ ρ = c0 • ν := by
    refine ⟨ρ.addHaarScalarFactor ν, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ρ ν, ?_⟩
    first
    | exact Measure.isAddLeftInvariant_eq_smul ρ ν
    | exact Measure.isAddHaarMeasure_eq_smul_of_isAddHaarMeasure ρ ν
    | exact Measure.isAddLeftInvariant_eq_smul_of_innerRegular ρ ν
    | exact Measure.isAddLeftInvariant_eq_smul_of_regular ρ ν
  have hK0 : ENNReal.ofReal 2 ≠ 0 := (ENNReal.ofReal_pos.2 two_pos).ne'
  have hpos : (0 : ℝ) < ‖R‖ + 1 := by positivity
  refine ⟨(ENNReal.ofReal 2)⁻¹ * c0, ?_, ?_, Metric.ball (f x0) (r / (‖R‖ + 1)),
    Metric.ball_mem_nhds _ (div_pos hr hpos), ?_⟩
  · first
    | exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
        (ENNReal.coe_ne_zero.2 hc0pos.ne')
    | (apply ENNReal.mul_pos <;> simp [hc0pos.ne'])
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hK0) ENNReal.coe_ne_top
  · intro S hSN hS
    have hAm : Measurable A := A.continuous.measurable
    have hS'' : MeasurableSet ((fun y => y + (f x0 - A x0)) ⁻¹' S) := measurable_add_const _ hS
    have hM : MeasurableSet (f ⁻¹' S ∩ U0) :=
      (hf.continuous.measurable hS).inter hU0open.measurableSet
    have hsub : A ⁻¹' ((fun y => y + (f x0 - A x0)) ⁻¹' S) ∩
        {x | ‖x - R (A x) - (x0 - R (A x0))‖ < r} ⊆ h '' (f ⁻¹' S ∩ U0) := by
      rintro u ⟨huS, huZ⟩
      have huS' : A u + (f x0 - A x0) ∈ S := huS
      have huZ' : ‖u - R (A u) - (x0 - R (A x0))‖ < r := huZ
      have hN := hSN huS'
      rw [Metric.mem_ball, dist_eq_norm] at hN
      have e1 : A u + (f x0 - A x0) - f x0 = A (u - x0) := by rw [map_sub]; abel
      rw [e1] at hN
      have e2 : u - x0 = R (A (u - x0)) + (u - R (A u) - (x0 - R (A x0))) := by
        rw [map_sub, map_sub]; abel
      have hne : ‖R‖ + 1 ≠ 0 := hpos.ne'
      have hR1 : ‖R (A (u - x0))‖ ≤ r := by
        have ht := norm_nonneg (A (u - x0))
        calc ‖R (A (u - x0))‖ ≤ ‖R‖ * ‖A (u - x0)‖ := R.le_opNorm _
          _ ≤ (‖R‖ + 1) * ‖A (u - x0)‖ := by nlinarith
          _ ≤ (‖R‖ + 1) * (r / (‖R‖ + 1)) := mul_le_mul_of_nonneg_left hN.le hpos.le
          _ = r := by field_simp
      have hu : u ∈ Metric.ball x0 δ := by
        rw [Metric.mem_ball, dist_eq_norm, e2]
        calc ‖R (A (u - x0)) + (u - R (A u) - (x0 - R (A x0)))‖
            ≤ ‖R (A (u - x0))‖ + ‖u - R (A u) - (x0 - R (A x0))‖ := norm_add_le _ _
          _ < δ := by linarith
      obtain ⟨x, hxU0, rfl⟩ := hball hu
      refine ⟨x, ⟨?_, hxU0⟩, rfl⟩
      show f x ∈ S
      rw [hfh x]; exact huS'
    have h1 : ν S = ν ((fun y => y + (f x0 - A x0)) ⁻¹' S) :=
      (measure_preimage_add_right ν _ S).symm
    have h2 : ρ ((fun y => y + (f x0 - A x0)) ⁻¹' S)
        = (c0 : ℝ≥0∞) * ν ((fun y => y + (f x0 - A x0)) ⁻¹' S) := by
      rw [hρeq]
      first
      | exact Measure.nnreal_smul_coe_apply _ _ _
      | simp
      | rfl
    have h3 : ρ ((fun y => y + (f x0 - A x0)) ⁻¹' S) = μ (A ⁻¹' ((fun y => y + (f x0 - A x0)) ⁻¹' S) ∩
        {x | ‖x - R (A x) - (x0 - R (A x0))‖ < r}) := by
      rw [hρdef, Measure.map_apply hAm hS'', Measure.restrict_apply (hAm hS'')]
    have h5 : μ (h '' (f ⁻¹' S ∩ U0)) ≤
        ∫⁻ x in f ⁻¹' S ∩ U0, ENNReal.ofReal |(fderiv ℝ h x).det| ∂μ := by
      first
      | exact addHaar_image_le_lintegral_abs_det_fderiv μ hM
          (fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt)
      | exact addHaar_image_le_lintegral_abs_det_fderiv hM
          (fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt)
    have h6 : ∫⁻ x in f ⁻¹' S ∩ U0, ENNReal.ofReal |(fderiv ℝ h x).det| ∂μ ≤
        ∫⁻ _ in f ⁻¹' S ∩ U0, ENNReal.ofReal 2 ∂μ := by
      have hle : ∀ x ∈ f ⁻¹' S ∩ U0, ENNReal.ofReal |(fderiv ℝ h x).det| ≤ ENNReal.ofReal 2 :=
        fun x hx => ENNReal.ofReal_le_ofReal (hU0det x hx.2).le
      first
      | exact setLIntegral_mono' hM hle
      | exact setLIntegral_mono measurable_const hle
      | exact lintegral_mono_ae ((ae_restrict_iff' hM).2 (Filter.Eventually.of_forall hle))
    have h7 : ∫⁻ _ in f ⁻¹' S ∩ U0, ENNReal.ofReal 2 ∂μ = ENNReal.ofReal 2 * μ (f ⁻¹' S ∩ U0) := by
      first
      | exact setLIntegral_const _ _
      | rw [lintegral_const, Measure.restrict_apply_univ]
    have h8 : μ (f ⁻¹' S ∩ U0) ≤ μ (f ⁻¹' S ∩ W) :=
      measure_mono (fun x hx => ⟨hx.1, hU0W hx.2⟩)
    have key : (c0 : ℝ≥0∞) * ν S ≤ ENNReal.ofReal 2 * μ (f ⁻¹' S ∩ W) := by
      rw [h1, ← h2, h3]
      calc _ ≤ μ (h '' (f ⁻¹' S ∩ U0)) := measure_mono hsub
        _ ≤ _ := h5
        _ ≤ _ := h6
        _ = _ := h7
        _ ≤ _ := by gcongr
    calc (ENNReal.ofReal 2)⁻¹ * c0 * ν S = (ENNReal.ofReal 2)⁻¹ * (c0 * ν S) := mul_assoc _ _ _
      _ ≤ (ENNReal.ofReal 2)⁻¹ * (ENNReal.ofReal 2 * μ (f ⁻¹' S ∩ W)) := by gcongr
      _ = μ (f ⁻¹' S ∩ W) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hK0 ENNReal.ofReal_ne_top, one_mul]

end PI.VolStabS
