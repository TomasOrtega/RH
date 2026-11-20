import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntMulOfCpt

open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

section LogBump

def bumpR : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

def psiL (n : ℕ) (c : ℂ) : ℝ := if c = 0 then 0 else bumpR (Real.log ‖c‖ / ((n : ℝ) + 1))

/- English proof (translation)
Unfold `psiL`. Use `split_ifs`. Simplify using the standard rewrite rules. Rewrite using `[abs_of_nonneg bumpR.nonneg]`. Conclude with `bumpR.le_one`.
-/
theorem psiL_le_one (n : ℕ) (c : ℂ) : |psiL n c| ≤ 1 := by
  unfold psiL
  split_ifs
  · simp
  · rw [abs_of_nonneg bumpR.nonneg]
    exact bumpR.le_one

/- English proof (translation)
Use `filter_upwards [isOpen_ne.mem_nhds hc] with w hw`. Simplify using `[psiL, hw]`.
-/
theorem psiL_eq_near (n : ℕ) (c : ℂ) (hc : c ≠ 0) :
    psiL n =ᶠ[𝓝 c] fun w => bumpR (Real.log ‖w‖ / ((n : ℝ) + 1)) := by
  filter_upwards [isOpen_ne.mem_nhds hc] with w hw
  simp [psiL, hw]

/- English proof (translation)
Unfold `psiL`. Use `split_ifs with h`. Both sides reduce to the same expression. Apply `bumpR.zero_of_le_dist` to reduce the goal to its premises. Establish `hpos : (0:ℝ) < (n:ℝ) + 1` using `by positivity`.

Rewrite using `[Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos, le_div_iff₀ hpos]`. Conclude with `hw`.
-/
theorem psiL_zero_of (n : ℕ) (w : ℂ) (hw : 2 * ((n : ℝ) + 1) ≤ |Real.log ‖w‖|) : psiL n w = 0 := by
  unfold psiL
  split_ifs with h
  · rfl
  · apply bumpR.zero_of_le_dist
    have hpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos, le_div_iff₀ hpos]
    exact hw

/- English proof (translation)
Establish `hcont : ContinuousAt (fun w : ℂ => |Real.log ‖w‖|) c` using `((Real.continuousAt_log (norm_ne_zero_iff.2 hc)).comp continuous_norm.continuousAt).abs`. Establish `h1 : ∀ᶠ w in 𝓝 c, |Real.log ‖w‖| < (n:ℝ) + 1` using `hcont.eventually_lt continuousAt_const h`. Use `filter_upwards [isOpen_ne.mem_nhds hc, h1] with w hw hw1`. Simplify using `only [psiL, if_neg hw]`. Apply `bumpR.one_of_mem_closedBall` to reduce the goal to its premises.

Establish `hpos : (0:ℝ) < (n:ℝ) + 1` using `by positivity`. Rewrite using `[Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]`. Use `show |Real.log ‖w‖| ≤ 1 * ((n:ℝ) + 1)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem psiL_one_near (n : ℕ) (c : ℂ) (hc : c ≠ 0) (h : |Real.log ‖c‖| < (n : ℝ) + 1) :
    psiL n =ᶠ[𝓝 c] fun _ => 1 := by
  have hcont : ContinuousAt (fun w : ℂ => |Real.log ‖w‖|) c :=
    ((Real.continuousAt_log (norm_ne_zero_iff.2 hc)).comp continuous_norm.continuousAt).abs
  have h1 : ∀ᶠ w in 𝓝 c, |Real.log ‖w‖| < (n:ℝ) + 1 := hcont.eventually_lt continuousAt_const h
  filter_upwards [isOpen_ne.mem_nhds hc, h1] with w hw hw1
  simp only [psiL, if_neg hw]
  apply bumpR.one_of_mem_closedBall
  have hpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  show |Real.log ‖w‖| ≤ 1 * ((n:ℝ) + 1)
  linarith

/- English proof (translation)
Establish `hε : (0:ℝ) < Real.exp (-(2 * ((n:ℝ) + 1)))` using `Real.exp_pos _`. Use `filter_upwards [Metric.ball_mem_nhds (0:ℂ) hε] with w hw`. Distinguish the cases in `h0 : w = 0`. Simplify using `[psiL, h0]`. Apply `psiL_zero_of` to reduce the goal to its premises.

Rewrite `hw` using `[Metric.mem_ball, dist_zero_right]`. Establish `hlog : Real.log ‖w‖ < -(2 * ((n:ℝ) + 1))`. Rewrite using `[Real.log_lt_iff_lt_exp (norm_pos_iff.2 h0)]`. Conclude with `hw`. Establish `h2 : (0:ℝ) < 2 * ((n:ℝ) + 1)` using `by positivity`.

Rewrite using `[abs_of_neg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem psiL_zero_near0 (n : ℕ) : psiL n =ᶠ[𝓝 0] fun _ => 0 := by
  have hε : (0:ℝ) < Real.exp (-(2 * ((n:ℝ) + 1))) := Real.exp_pos _
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) hε] with w hw
  by_cases h0 : w = 0
  · simp [psiL, h0]
  · apply psiL_zero_of
    rw [Metric.mem_ball, dist_zero_right] at hw
    have hlog : Real.log ‖w‖ < -(2 * ((n:ℝ) + 1)) := by
      rw [Real.log_lt_iff_lt_exp (norm_pos_iff.2 h0)]
      exact hw
    have h2 : (0:ℝ) < 2 * ((n:ℝ) + 1) := by positivity
    rw [abs_of_neg (by linarith)]
    linarith

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Conclude with `(contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq (psiL_zero_near0 n)`. Use `ContDiffAt.congr_of_eventuallyEq ?_ (psiL_eq_near n c hc)` and prove the remaining obligations. Establish `h1 : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) c` using `contDiffAt_norm ℝ hc`.

Establish `h2 : ContDiffAt ℝ ∞ (fun w : ℂ => Real.log ‖w‖) c` using `(Real.contDiffAt_log.2 (norm_ne_zero_iff.2 hc)).comp c h1`. Establish `h3 : ContDiffAt ℝ ∞ (fun w : ℂ => Real.log ‖w‖ / ((n:ℝ) + 1)) c` using `h2.div_const _`. Conclude with `bumpR.contDiff.contDiffAt.comp c h3`.
-/
theorem psiL_contDiffAt (n : ℕ) (c : ℂ) : ContDiffAt ℝ ∞ (psiL n) c := by
  by_cases hc : c = 0
  · subst hc
    exact (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq (psiL_zero_near0 n)
  · refine ContDiffAt.congr_of_eventuallyEq ?_ (psiL_eq_near n c hc)
    have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) c := contDiffAt_norm ℝ hc
    have h2 : ContDiffAt ℝ ∞ (fun w : ℂ => Real.log ‖w‖) c :=
      (Real.contDiffAt_log.2 (norm_ne_zero_iff.2 hc)).comp c h1
    have h3 : ContDiffAt ℝ ∞ (fun w : ℂ => Real.log ‖w‖ / ((n:ℝ) + 1)) c := h2.div_const _
    exact bumpR.contDiff.contDiffAt.comp c h3

/- English proof (translation)
The claim follows from `contDiff_iff_contDiffAt.2 (psiL_contDiffAt n)`.
-/
theorem psiL_contDiff (n : ℕ) : ContDiff ℝ ∞ (psiL n) := contDiff_iff_contDiffAt.2 (psiL_contDiffAt n)

/- English proof (translation)
Use `closure_minimal (fun c hc => ?_) ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))` and prove the remaining obligations. Establish `hc' : psiL n c ≠ 0` using `hc`. Establish `h0 : c ≠ 0`. Introduce and unpack `rfl`. Conclude with `hc' (by simp [psiL])`.

Establish `hlog : |Real.log ‖c‖| < 2 * ((n:ℝ) + 1)`. Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Conclude with `hc' (psiL_zero_of n c hle)`. Establish `hpos` using `norm_pos_iff.2 h0`.

Rewrite `hlog` using `[abs_lt]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← Real.exp_log hpos]`. Conclude with `Real.exp_le_exp.2 (by linarith [hlog.1])`. Rewrite using `[← Real.exp_log hpos]`.

Conclude with `Real.exp_le_exp.2 (by linarith [hlog.2])`.
-/
theorem tsupport_psiL (n : ℕ) : tsupport (psiL n) ⊆
    {c : ℂ | Real.exp (-(2 * ((n : ℝ) + 1))) ≤ ‖c‖ ∧ ‖c‖ ≤ Real.exp (2 * ((n : ℝ) + 1))} := by
  refine closure_minimal (fun c hc => ?_)
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
  have hc' : psiL n c ≠ 0 := hc
  have h0 : c ≠ 0 := by
    rintro rfl
    exact hc' (by simp [psiL])
  have hlog : |Real.log ‖c‖| < 2 * ((n:ℝ) + 1) := by
    by_contra hle
    push_neg at hle
    exact hc' (psiL_zero_of n c hle)
  have hpos := norm_pos_iff.2 h0
  rw [abs_lt] at hlog
  constructor
  · rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 (by linarith [hlog.1])
  · rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 (by linarith [hlog.2])

/- English proof (translation)
Use `(isCompact_closedBall (0:ℂ) (Real.exp (2 * ((n:ℝ) + 1)))).of_isClosed_subset (isClosed_tsupport _) ?_` and prove the remaining obligations. Introduce `c hc`. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Conclude with `(tsupport_psiL n hc).2`.
-/
theorem psiL_hasCompactSupport (n : ℕ) : HasCompactSupport (psiL n) := by
  refine (isCompact_closedBall (0:ℂ) (Real.exp (2 * ((n:ℝ) + 1)))).of_isClosed_subset (isClosed_tsupport _) ?_
  intro c hc
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (tsupport_psiL n hc).2

/- English proof (translation)
Introduce `h`. Establish `h1` using `(tsupport_psiL n h).1`. Rewrite `h1` using `[norm_zero]`. Conclude with `absurd h1 (not_le.2 (Real.exp_pos _))`.
-/
theorem zero_notMem_tsupport_psiL (n : ℕ) : (0 : ℂ) ∉ tsupport (psiL n) := by
  intro h
  have h1 := (tsupport_psiL n h).1
  rw [norm_zero] at h1
  exact absurd h1 (not_le.2 (Real.exp_pos _))

/- English proof (translation)
Establish `hc : Continuous (deriv bumpR)` using `(bumpR.contDiff (n := 1)).continuous_deriv le_rfl`. Conclude with `hc.bounded_above_of_compact_support bumpR.hasCompactSupport.deriv`.
-/
theorem exists_deriv_bump_bound : ∃ C : ℝ, ∀ t, ‖deriv bumpR t‖ ≤ C := by
  have hc : Continuous (deriv bumpR) := (bumpR.contDiff (n := 1)).continuous_deriv le_rfl
  exact hc.bounded_above_of_compact_support bumpR.hasCompactSupport.deriv

/- English proof (translation)
Establish `hpos : 0 < ‖c‖` using `norm_pos_iff.2 hc`. Establish `hn1 : (0:ℝ) < (n:ℝ) + 1` using `by positivity`. Establish `hnd : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) c` using `(contDiffAt_norm ℝ hc (n := 1)).differentiableAt one_ne_zero`. Establish `hN : ‖fderiv ℝ (fun w : ℂ => ‖w‖) c‖ ≤ 1`. Simplify using `using norm_fderiv_le_of_lipschitz ℝ (x₀ := c) lipschitzWith_one_norm`.

Establish `hl : HasFDerivAt (fun w : ℂ => Real.log ‖w‖) ((‖c‖)⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) c) c` using `(Real.hasDerivAt_log hpos.ne').comp_hasFDerivAt c hnd.hasFDerivAt`. Establish `hφ : HasFDerivAt (fun w : ℂ => Real.log ‖w‖ / ((n:ℝ) + 1)) ((((n:ℝ) + 1)⁻¹) • ((‖c‖)⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) c)) c`. Establish `h2` using `hl.mul_const (((n:ℝ) + 1)⁻¹)`. Simplify `h2` using `only [div_eq_mul_inv]`. Establish `hb : HasDerivAt (⇑bumpR) (deriv bumpR (Real.log ‖c‖ / ((n:ℝ) + 1))) (Real.log ‖c‖ / ((n:ℝ) + 1))` using `((bumpR.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt`.

Establish `hcomp` using `hb.comp_hasFDerivAt c hφ`. Establish `hf : fderiv ℝ (psiL n) c = deriv bumpR (Real.log ‖c‖ / ((n:ℝ) + 1)) • ((((n:ℝ) + 1)⁻¹) • ((‖c‖)⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) c))` using `(psiL_eq_near n c hc).fderiv_eq.trans hcomp.fderiv`. Establish `e1 : ‖(((n:ℝ) + 1)⁻¹)‖ = ((n:ℝ) + 1)⁻¹` using `by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn1)]`. Establish `e2 : ‖(‖c‖)⁻¹‖ = (‖c‖)⁻¹` using `by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]`. Rewrite using `[hf, norm_smul, norm_smul, norm_smul, e1, e2]`.

Establish `hinv : ((n:ℝ) + 1)⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])`. Establish `key : ∀ (t a b N : ℝ), 0 < t → a ≤ C → 0 ≤ a → 0 ≤ b → b ≤ 1 → 0 ≤ N → N ≤ 1 → t * (a * (b * (t⁻¹ * N))) ≤ C`. Introduce `t a b N ht ha ha0 hb0 hb1 hN0 hN1`. Rewrite using `[show t * (a * (b * (t⁻¹ * N))) = a * (b * N) * (t * t⁻¹) by ring, mul_inv_cancel₀ ht.ne', mul_one]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `key _ _ _ _ hpos (hC _) (norm_nonneg _) (inv_nonneg.2 hn1.le) hinv (norm_nonneg _) hN`.
-/
theorem norm_mul_fderiv_psiL_le {C : ℝ} (hC : ∀ t, ‖deriv bumpR t‖ ≤ C) (n : ℕ) (c : ℂ) (hc : c ≠ 0) :
    ‖c‖ * ‖fderiv ℝ (psiL n) c‖ ≤ C := by
  have hpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hnd : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) c := (contDiffAt_norm ℝ hc (n := 1)).differentiableAt one_ne_zero
  have hN : ‖fderiv ℝ (fun w : ℂ => ‖w‖) c‖ ≤ 1 := by
    simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := c) lipschitzWith_one_norm
  have hl : HasFDerivAt (fun w : ℂ => Real.log ‖w‖) ((‖c‖)⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) c) c :=
    (Real.hasDerivAt_log hpos.ne').comp_hasFDerivAt c hnd.hasFDerivAt
  have hφ : HasFDerivAt (fun w : ℂ => Real.log ‖w‖ / ((n:ℝ) + 1))
      ((((n:ℝ) + 1)⁻¹) • ((‖c‖)⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) c)) c := by
    have h2 := hl.mul_const (((n:ℝ) + 1)⁻¹)
    simpa only [div_eq_mul_inv] using h2
  have hb : HasDerivAt (⇑bumpR) (deriv bumpR (Real.log ‖c‖ / ((n:ℝ) + 1))) (Real.log ‖c‖ / ((n:ℝ) + 1)) :=
    ((bumpR.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  have hcomp := hb.comp_hasFDerivAt c hφ
  have hf : fderiv ℝ (psiL n) c = deriv bumpR (Real.log ‖c‖ / ((n:ℝ) + 1)) •
      ((((n:ℝ) + 1)⁻¹) • ((‖c‖)⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) c)) :=
    (psiL_eq_near n c hc).fderiv_eq.trans hcomp.fderiv
  have e1 : ‖(((n:ℝ) + 1)⁻¹)‖ = ((n:ℝ) + 1)⁻¹ := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn1)]
  have e2 : ‖(‖c‖)⁻¹‖ = (‖c‖)⁻¹ := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
  rw [hf, norm_smul, norm_smul, norm_smul, e1, e2]
  have hinv : ((n:ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
  have key : ∀ (t a b N : ℝ), 0 < t → a ≤ C → 0 ≤ a → 0 ≤ b → b ≤ 1 → 0 ≤ N → N ≤ 1 →
      t * (a * (b * (t⁻¹ * N))) ≤ C := by
    intro t a b N ht ha ha0 hb0 hb1 hN0 hN1
    rw [show t * (a * (b * (t⁻¹ * N))) = a * (b * N) * (t * t⁻¹) by ring, mul_inv_cancel₀ ht.ne', mul_one]
    calc a * (b * N) ≤ C * (1 * 1) :=
          mul_le_mul ha (mul_le_mul hb1 hN1 hN0 zero_le_one) (mul_nonneg hb0 hN0) (le_trans ha0 ha)
      _ = C := by ring
  exact key _ _ _ _ hpos (hC _) (norm_nonneg _) (inv_nonneg.2 hn1.le) hinv (norm_nonneg _) hN

end LogBump

end Formalism.FourierDecayAlt.P5.HerB
