import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
open scoped InnerProductSpace ComplexOrder

section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

private noncomputable def box (r : ℝ) (e : V) : L V :=
  indicatorConstLp 2 (measurableSet_Ioc (a := (0 : ℝ)) (b := r)) (by simp) e

/- English proof (translation)
The claim follows from `indicatorConstLp_coeFn`.
-/
private theorem box_ae (r : ℝ) (e : V) : ∀ᵐ x : ℝ, box r e x = (Set.Ioc (0 : ℝ) r).indicator (fun _ => e) x :=
  indicatorConstLp_coeFn

private noncomputable def ov (r t : ℝ) : ℝ := max (min r (r - t) - max 0 (-t)) 0

/- English proof (translation)
Rewrite using `[L2.inner_def]`. Establish `h : ∀ᵐ x : ℝ, ⟪box r e' x, c.compLpL 2 volume (sh V t (box r e)) x⟫_ℂ = (Set.Ioc (max 0 (-t)) (min r (r - t))).indicator (fun _ => ⟪e', c e⟫_ℂ) x` using `by filter_upwards [box_ae r e', c.coeFn_compLpL (sh V t (box r e)), sh_ae V t (box r e), (measurePreserving_add_right volume t).quasiMeasurePreserving.ae (box_ae r e)] with x h1 h2 h3 h4`. Rewrite using `[h1, h2, h3, h4]`. Distinguish the cases in `a : x ∈ Set.Ioc (0 : ℝ) r`. Distinguish the cases in `b : x + t ∈ Set.Ioc (0 : ℝ) r`.

Rewrite using `[Set.indicator_of_mem a, Set.indicator_of_mem b, Set.indicator_of_mem]`. Conclude with `⟨max_lt a.1 (by linarith [b.1]), le_min a.2 (by linarith [b.2])⟩`. Rewrite using `[Set.indicator_of_notMem b, map_zero, inner_zero_right, Set.indicator_of_notMem]`. Introduce `h`. Conclude with `b ⟨by linarith [(max_lt_iff.1 h.1).2], by linarith [(le_min_iff.1 h.2).2]⟩`.

Rewrite using `[Set.indicator_of_notMem a, inner_zero_left, Set.indicator_of_notMem]`. Introduce `h`. Conclude with `a ⟨(max_lt_iff.1 h.1).1, (le_min_iff.1 h.2).1⟩`. Rewrite using `[integral_congr_ae h, integral_indicator_const _ measurableSet_Ioc, Real.volume_real_Ioc, Complex.real_smul, ov]`.
-/
private theorem box_inner (r t : ℝ) (c : V →L[ℂ] V) (e' e : V) :
    ⟪box r e', c.compLpL 2 volume (sh V t (box r e))⟫_ℂ = (ov r t : ℂ) * ⟪e', c e⟫_ℂ := by
  rw [L2.inner_def]
  have h : ∀ᵐ x : ℝ, ⟪box r e' x, c.compLpL 2 volume (sh V t (box r e)) x⟫_ℂ =
      (Set.Ioc (max 0 (-t)) (min r (r - t))).indicator (fun _ => ⟪e', c e⟫_ℂ) x := by
    filter_upwards [box_ae r e', c.coeFn_compLpL (sh V t (box r e)), sh_ae V t (box r e),
      (measurePreserving_add_right volume t).quasiMeasurePreserving.ae (box_ae r e)] with x h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    by_cases a : x ∈ Set.Ioc (0 : ℝ) r
    · by_cases b : x + t ∈ Set.Ioc (0 : ℝ) r
      · rw [Set.indicator_of_mem a, Set.indicator_of_mem b, Set.indicator_of_mem]
        exact ⟨max_lt a.1 (by linarith [b.1]), le_min a.2 (by linarith [b.2])⟩
      · rw [Set.indicator_of_notMem b, map_zero, inner_zero_right, Set.indicator_of_notMem]
        intro h
        exact b ⟨by linarith [(max_lt_iff.1 h.1).2], by linarith [(le_min_iff.1 h.2).2]⟩
    · rw [Set.indicator_of_notMem a, inner_zero_left, Set.indicator_of_notMem]
      intro h
      exact a ⟨(max_lt_iff.1 h.1).1, (le_min_iff.1 h.2).1⟩
  rw [integral_congr_ae h, integral_indicator_const _ measurableSet_Ioc, Real.volume_real_Ioc, Complex.real_smul, ov]

/- English proof (translation)
Rewrite using `[box, norm_indicatorConstLp (by simp) (by simp), Real.volume_real_Ioc, sub_zero, max_eq_left hr, Real.sqrt_eq_rpow]`. Simplify using the standard rewrite rules.
-/
private theorem box_norm (r : ℝ) (hr : 0 ≤ r) (e : V) : ‖box r e‖ = ‖e‖ * Real.sqrt r := by
  rw [box, norm_indicatorConstLp (by simp) (by simp), Real.volume_real_Ioc, sub_zero, max_eq_left hr, Real.sqrt_eq_rpow]
  simp

/- English proof (translation)
Establish `h0 : 0 ≤ ov r t` using `le_max_right _ _`. Establish `h1 : ov r t ≤ r` using `max_le (by linarith [min_le_left r (r - t), le_max_left 0 (-t)]) hr.le`. Rewrite using `[abs_of_nonneg (by positivity), inv_mul_le_iff₀ hr]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem ov_le (r t : ℝ) (hr : 0 < r) : |r⁻¹ * ov r t| ≤ 1 := by
  have h0 : 0 ≤ ov r t := le_max_right _ _
  have h1 : ov r t ≤ r := max_le (by linarith [min_le_left r (r - t), le_max_left 0 (-t)]) hr.le
  rw [abs_of_nonneg (by positivity), inv_mul_le_iff₀ hr]
  linarith

/- English proof (translation)
Establish `h : Tendsto (fun r : ℝ => 1 - |t| * r⁻¹) atTop (𝓝 (1 - |t| * 0))` using `tendsto_const_nhds.sub (tendsto_inv_atTop_zero.const_mul _)`. Rewrite `h` using `[mul_zero, sub_zero]`. Use `h.congr' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_gt_atTop |t|] with r hr`. Establish `hr0 : 0 < r` using `(abs_nonneg t).trans_lt hr`.

Establish `: ov r t = r - |t|`. Unfold `ov`. Break down `le_total 0 t with h | h` into its components or cases. Rewrite `hr`, the goal using `[abs_of_nonneg h]`. Rewrite using `[min_eq_right (by linarith), max_eq_left (by linarith : -t ≤ 0), max_eq_left (by linarith), sub_zero]`.

Rewrite `hr`, the goal using `[abs_of_nonpos h]`. Rewrite using `[min_eq_left (by linarith), max_eq_right (by linarith : 0 ≤ -t), max_eq_left (by linarith)]`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem ov_lim (t : ℝ) : Tendsto (fun r : ℝ => r⁻¹ * ov r t) atTop (𝓝 1) := by
  have h : Tendsto (fun r : ℝ => 1 - |t| * r⁻¹) atTop (𝓝 (1 - |t| * 0)) :=
    tendsto_const_nhds.sub (tendsto_inv_atTop_zero.const_mul _)
  rw [mul_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop |t|] with r hr
  have hr0 : 0 < r := (abs_nonneg t).trans_lt hr
  have : ov r t = r - |t| := by
    unfold ov
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h] at hr ⊢
      rw [min_eq_right (by linarith), max_eq_left (by linarith : -t ≤ 0), max_eq_left (by linarith), sub_zero]
    · rw [abs_of_nonpos h] at hr ⊢
      rw [min_eq_left (by linarith), max_eq_right (by linarith : 0 ≤ -t), max_eq_left (by linarith)]
  rw [this]
  field_simp

/- English proof (translation)
Establish `hk1 : Integrable β` using `hk.1.integrable_of_hasCompactSupport hk.2`. Establish `hk2 : Integrable fun t => β t e` using `hk1.apply_continuousLinearMap e`. Establish `hk3 : Integrable fun t => ⟪e', β t e⟫_ℂ` using `hk2.const_inner e'`. Establish `hs : ⟪e', symb β 0 e⟫_ℂ = ∫ t, ((1 : ℝ) : ℂ) * ⟪e', β t e⟫_ℂ`. Simplify using `only [symb, zero_mul, Complex.exp_zero, one_smul, Complex.ofReal_one, one_mul]`.

Rewrite using `[ContinuousLinearMap.integral_apply hk1, integral_inner hk2]`. Establish `he : ∀ r : ℝ, ((r⁻¹ : ℝ) : ℂ) * ⟪box r e', conv β (box r e)⟫_ℂ = ∫ t, ((r⁻¹ * ov r t : ℝ) : ℂ) * ⟪e', β t e⟫_ℂ` using `fun r => by`. Take `⟨-, h2, h3⟩` from `convSpec β hk (box r e)`. Rewrite using `[h3, ← integral_inner h2, ← integral_const_mul]`. Simplify using `only [box_inner, Complex.ofReal_mul, mul_assoc]`.

Rewrite using `[hs]`. Simplify using `only [he]`. Use `tendsto_integral_filter_of_dominated_convergence (fun t => ‖⟪e', β t e⟫_ℂ‖) ?_ ?_ hk3.norm ?_` and prove the remaining obligations. Use `Eventually.of_forall fun r => AEStronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_) hk3.1` and prove the remaining obligations. Unfold `ov`.

Use `fun_prop`. Use `filter_upwards [eventually_gt_atTop 0] with r hr`. Use `Eventually.of_forall fun t => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (ov_le r t hr)`.

Conclude with `Eventually.of_forall fun t => ((Complex.continuous_ofReal.tendsto 1).comp (ov_lim t)).mul_const _`.
-/
private theorem conv_lim [FiniteDimensional ℂ V] [CompleteSpace V] (β : ℝ → V →L[ℂ] V) (hk : Ker β) (e' e : V) :
    Tendsto (fun r : ℝ => ((r⁻¹ : ℝ) : ℂ) * ⟪box r e', conv β (box r e)⟫_ℂ) atTop (𝓝 ⟪e', symb β 0 e⟫_ℂ) := by
  have hk1 : Integrable β := hk.1.integrable_of_hasCompactSupport hk.2
  have hk2 : Integrable fun t => β t e := hk1.apply_continuousLinearMap e
  have hk3 : Integrable fun t => ⟪e', β t e⟫_ℂ := hk2.const_inner e'
  have hs : ⟪e', symb β 0 e⟫_ℂ = ∫ t, ((1 : ℝ) : ℂ) * ⟪e', β t e⟫_ℂ := by
    simp only [symb, zero_mul, Complex.exp_zero, one_smul, Complex.ofReal_one, one_mul]
    rw [ContinuousLinearMap.integral_apply hk1, integral_inner hk2]
  have he : ∀ r : ℝ, ((r⁻¹ : ℝ) : ℂ) * ⟪box r e', conv β (box r e)⟫_ℂ =
      ∫ t, ((r⁻¹ * ov r t : ℝ) : ℂ) * ⟪e', β t e⟫_ℂ := fun r => by
    obtain ⟨-, h2, h3⟩ := convSpec β hk (box r e)
    rw [h3, ← integral_inner h2, ← integral_const_mul]
    simp only [box_inner, Complex.ofReal_mul, mul_assoc]
  rw [hs]
  simp only [he]
  refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖⟪e', β t e⟫_ℂ‖) ?_ ?_ hk3.norm ?_
  · refine Eventually.of_forall fun r => AEStronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_) hk3.1
    unfold ov
    fun_prop
  · filter_upwards [eventually_gt_atTop 0] with r hr
    refine Eventually.of_forall fun t => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (ov_le r t hr)
  · exact Eventually.of_forall fun t => ((Complex.continuous_ofReal.tendsto 1).comp (ov_lim t)).mul_const _

end

/- English proof (translation)
Introduce `H V _ _ _ _ _ _ _ J Y β hk hc h0 h1`. Establish `hY : ∀ u' u : L V, ⟪u', conv β u⟫_ℂ = ⟪J u', Y (J u)⟫_ℂ` using `fun u' u => by`. Rewrite using `[hc u _ (convSpec β hk u).1, J.inner_map_map]`. Establish `hp` using `(ContinuousLinearMap.nonneg_iff_isPositive Y).1 h0`. Prove the components needed by the constructor for the conclusion.

Establish `key : ∀ e, 0 ≤ ⟪e, symb β 0 e⟫_ℂ` using `fun e => by`. Use `ge_of_tendsto (conv_lim β hk e e) ?_` and prove the remaining obligations. Use `filter_upwards [eventually_gt_atTop 0] with r hr`. Rewrite using `[hY]`. Conclude with `mul_nonneg (Complex.zero_le_real.2 (by positivity)) (hp.inner_nonneg_right _)`.

Rewrite using `[ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]`. Introduce `e`. Establish `h : 0 ≤ ⟪symb β 0 e, e⟫_ℂ`. Rewrite using `[← inner_conj_symm]`. Conclude with `star_nonneg_iff.2 (key e)`.

Take `⟨a, b⟩` from `Complex.nonneg_iff.1 h`. Conclude with `⟨Complex.ext (by simp) (by simp [← b]), a⟩`. Establish `key : ∀ e' e, ‖⟪e', symb β 0 e⟫_ℂ‖ ≤ ‖e'‖ * ‖e‖` using `fun e' e => by`. Use `le_of_tendsto (conv_lim β hk e' e).norm ?_` and prove the remaining obligations. Use `filter_upwards [eventually_gt_atTop 0] with r hr`.

Rewrite using `[hY, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_le_iff₀ hr]`. Use `(norm_inner_le_norm _ _).trans ?_` and prove the remaining obligations. Establish `h2 : ‖Y (J (box r e))‖ ≤ ‖box r e‖`. Use `(Y.le_opNorm _).trans ?_` and prove the remaining obligations. Rewrite using `[J.norm_map]`.

Conclude with `mul_le_of_le_one_left (norm_nonneg _) h1`. Rewrite using `[J.norm_map]`. Use `(mul_le_mul_of_nonneg_left h2 (norm_nonneg _)).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[box_norm r hr.le, box_norm r hr.le, mul_mul_mul_comm, Real.mul_self_sqrt hr.le, mul_comm]`. Use `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun e => ?_` and prove the remaining obligations.

Establish `h` using `key (symb β 0 e) e`. Rewrite `h` using `[inner_self_eq_norm_sq_to_K]`. Simplify using `only [norm_pow, Complex.coe_algebraMap, Complex.norm_real, norm_norm] at h`. Rewrite using `[one_mul]`. Assume the negation of the conclusion as `hh`.

Use `push Not at hh`. Use polynomial arithmetic with `[norm_nonneg e]`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.posSymb :
    ∀ {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (J : L V →ₗᵢ[ℂ] H) (Y : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V), Ker β → Conv J J Y β → 0 ≤ Y → ‖Y‖ ≤ 1 → 0 ≤ symb β 0 ∧ ‖symb β 0‖ ≤ 1 := by
  intro H V _ _ _ _ _ _ _ J Y β hk hc h0 h1
  have hY : ∀ u' u : L V, ⟪u', conv β u⟫_ℂ = ⟪J u', Y (J u)⟫_ℂ := fun u' u => by
    rw [hc u _ (convSpec β hk u).1, J.inner_map_map]
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive Y).1 h0
  constructor
  · have key : ∀ e, 0 ≤ ⟪e, symb β 0 e⟫_ℂ := fun e => by
      refine ge_of_tendsto (conv_lim β hk e e) ?_
      filter_upwards [eventually_gt_atTop 0] with r hr
      rw [hY]
      exact mul_nonneg (Complex.zero_le_real.2 (by positivity)) (hp.inner_nonneg_right _)
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
    intro e
    have h : 0 ≤ ⟪symb β 0 e, e⟫_ℂ := by
      rw [← inner_conj_symm]
      exact star_nonneg_iff.2 (key e)
    obtain ⟨a, b⟩ := Complex.nonneg_iff.1 h
    exact ⟨Complex.ext (by simp) (by simp [← b]), a⟩
  · have key : ∀ e' e, ‖⟪e', symb β 0 e⟫_ℂ‖ ≤ ‖e'‖ * ‖e‖ := fun e' e => by
      refine le_of_tendsto (conv_lim β hk e' e).norm ?_
      filter_upwards [eventually_gt_atTop 0] with r hr
      rw [hY, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_le_iff₀ hr]
      refine (norm_inner_le_norm _ _).trans ?_
      have h2 : ‖Y (J (box r e))‖ ≤ ‖box r e‖ := by
        refine (Y.le_opNorm _).trans ?_
        rw [J.norm_map]
        exact mul_le_of_le_one_left (norm_nonneg _) h1
      rw [J.norm_map]
      refine (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)).trans (le_of_eq ?_)
      rw [box_norm r hr.le, box_norm r hr.le, mul_mul_mul_comm, Real.mul_self_sqrt hr.le, mul_comm]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun e => ?_
    have h := key (symb β 0 e) e
    rw [inner_self_eq_norm_sq_to_K] at h
    simp only [norm_pow, Complex.coe_algebraMap, Complex.norm_real, norm_norm] at h
    rw [one_mul]
    by_contra hh
    push Not at hh
    nlinarith [norm_nonneg e]
