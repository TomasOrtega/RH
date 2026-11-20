import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Legendre

noncomputable section
open scoped BigOperators ComplexConjugate
open Filter

namespace Formalism.L2.Th1.F

namespace SigmaConv

/- English proof (translation)
Use `set f : ℂ → ℂ := fun x => (1 - x) * Complex.exp (x + x ^ 2 / 2) with hf`. Establish `hder : ∀ x : ℂ, HasDerivAt f (-(x ^ 2) * Complex.exp (x + x ^ 2 / 2)) x`. Introduce `x`. Establish `h1 : HasDerivAt (fun x : ℂ => x + x ^ 2 / 2) (1 + x) x`. Establish `h0` using `(hasDerivAt_id x).add ((hasDerivAt_pow 2 x).div_const 2)`.

Apply the tactic sequence `exact h0.congr_deriv (by first | (norm_num; done) | (norm_num; ring) | ring)`. Establish `h2` using `((hasDerivAt_id x).const_sub (1 : ℂ)).mul h1.cexp`. Conclude with `h2.congr_deriv (by simp only [id]; ring)`. Establish `hbound : ∀ x ∈ Metric.closedBall (0 : ℂ) ‖w‖, ‖-(x ^ 2) * Complex.exp (x + x ^ 2 / 2)‖ ≤ 2 * ‖w‖ ^ 2`. Introduce `x hx`.

Rewrite `hx` using `[Metric.mem_closedBall, dist_zero_right]`. Establish `hx2 : ‖x‖ ≤ 1 / 2` using `hx.trans hw`. Rewrite using `[norm_mul, norm_neg, norm_pow, Complex.norm_exp]`. Establish `h3 : ‖x + x ^ 2 / 2‖ ≤ ‖x‖ + ‖x‖ ^ 2 / 2`. Combine the equalities or inequalities in the displayed calculation.

Establish `hre : (x + x ^ 2 / 2).re ≤ 5 / 8`. Use `Complex.re_le_norm (x + x ^ 2 / 2)` as an intermediate fact. Use polynomial arithmetic with `[norm_nonneg x]`. Establish `he : Real.exp ((x + x ^ 2 / 2).re) ≤ 2`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Real.exp_log (by norm_num : (0 : ℝ) < 2)]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use `Real.log_two_gt_d9` as an intermediate fact. Evaluate the numerical expressions using `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hx2' : ‖x‖ ^ 2 ≤ ‖w‖ ^ 2` using `by gcongr`. Combine the equalities or inequalities in the displayed calculation. Establish `hw0 : w ∈ Metric.closedBall (0 : ℂ) ‖w‖`. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Establish `key` using `(convex_closedBall (0 : ℂ) ‖w‖).norm_image_sub_le_of_norm_hasDerivWithin_le (fun x _ => (hder x).hasDerivWithinAt) hbound (Metric.mem_closedBall_self (norm_nonneg w)) hw0`.

Establish `f0 : f 0 = 1` using `by simp [f]`. Rewrite `key` using `[f0, sub_zero]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma norm_factor_sub_one_le (w : ℂ) (hw : ‖w‖ ≤ 1 / 2) :
    ‖(1 - w) * Complex.exp (w + w ^ 2 / 2) - 1‖ ≤ 2 * ‖w‖ ^ 3 := by
  set f : ℂ → ℂ := fun x => (1 - x) * Complex.exp (x + x ^ 2 / 2) with hf
  have hder : ∀ x : ℂ, HasDerivAt f (-(x ^ 2) * Complex.exp (x + x ^ 2 / 2)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℂ => x + x ^ 2 / 2) (1 + x) x := by
      have h0 := (hasDerivAt_id x).add ((hasDerivAt_pow 2 x).div_const 2)
      exact h0.congr_deriv (by first | (norm_num; done) | (norm_num; ring) | ring)
    have h2 := ((hasDerivAt_id x).const_sub (1 : ℂ)).mul h1.cexp
    exact h2.congr_deriv (by simp only [id]; ring)
  have hbound : ∀ x ∈ Metric.closedBall (0 : ℂ) ‖w‖,
      ‖-(x ^ 2) * Complex.exp (x + x ^ 2 / 2)‖ ≤ 2 * ‖w‖ ^ 2 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    have hx2 : ‖x‖ ≤ 1 / 2 := hx.trans hw
    rw [norm_mul, norm_neg, norm_pow, Complex.norm_exp]
    have h3 : ‖x + x ^ 2 / 2‖ ≤ ‖x‖ + ‖x‖ ^ 2 / 2 := by
      calc ‖x + x ^ 2 / 2‖ ≤ ‖x‖ + ‖x ^ 2 / 2‖ := norm_add_le _ _
        _ = ‖x‖ + ‖x‖ ^ 2 / 2 := by rw [norm_div, norm_pow]; norm_num
    have hre : (x + x ^ 2 / 2).re ≤ 5 / 8 := by
      have := Complex.re_le_norm (x + x ^ 2 / 2)
      nlinarith [norm_nonneg x]
    have he : Real.exp ((x + x ^ 2 / 2).re) ≤ 2 := by
      calc Real.exp ((x + x ^ 2 / 2).re) ≤ Real.exp (5 / 8) := Real.exp_le_exp.mpr hre
        _ ≤ 2 := by
          rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          apply Real.exp_le_exp.mpr
          have := Real.log_two_gt_d9
          norm_num at this ⊢
          linarith
    have hx2' : ‖x‖ ^ 2 ≤ ‖w‖ ^ 2 := by gcongr
    calc ‖x‖ ^ 2 * Real.exp ((x + x ^ 2 / 2).re) ≤ ‖w‖ ^ 2 * 2 :=
          mul_le_mul hx2' he (Real.exp_pos _).le (sq_nonneg _)
      _ = 2 * ‖w‖ ^ 2 := by ring
  have hw0 : w ∈ Metric.closedBall (0 : ℂ) ‖w‖ := by
    rw [Metric.mem_closedBall, dist_zero_right]
  have key := (convex_closedBall (0 : ℂ) ‖w‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hder x).hasDerivWithinAt) hbound (Metric.mem_closedBall_self (norm_nonneg w)) hw0
  have f0 : f 0 = 1 := by simp [f]
  rw [f0, sub_zero] at key
  calc ‖f w - 1‖ ≤ 2 * ‖w‖ ^ 2 * ‖w‖ := key
    _ = 2 * ‖w‖ ^ 3 := by ring

/- English proof (translation)
Unfold `wFactor`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma wFactor_eq (l z : ℂ) :
    wFactor l z = (1 - z / l) * Complex.exp (z / l + (z / l) ^ 2 / 2) := by
  unfold wFactor
  congr 2
  ring

/- English proof (translation)
Establish `hr : 0 ≤ r` using `(norm_nonneg z).trans hz`. Establish `hrp : ‖l‖ ^ (-3 : ℝ) = (‖l‖ ^ 3)⁻¹`. Rewrite using `[Real.rpow_neg (norm_nonneg _)]`. Use `norm_cast`. Break down `eq_or_ne l 0 with rfl | hl0` into its components or cases.

Establish `h1 : wFactor 0 z = 1` using `by simp [wFactor]`. Rewrite using `[h1, sub_self, norm_zero]`. Conclude with `mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hr 3)) (Real.rpow_nonneg le_rfl _)`. Establish `hlpos : 0 < ‖l‖` using `norm_pos_iff.mpr hl0`. Establish `hw : ‖z / l‖ ≤ 1 / 2`.

Rewrite using `[norm_div, div_le_iff₀ hlpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[wFactor_eq]`. Conclude with `norm_factor_sub_one_le _ hw`.

Use `_ = 2 * ‖z‖ ^ 3 * (‖l‖ ^ 3)⁻¹ := by rw [norm_div, div_pow]; ring`. Use `_ ≤ 2 * r ^ 3 * (‖l‖ ^ 3)⁻¹ := by gcongr`. Use `_ = 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by rw [hrp]`.
-/
lemma norm_wFactor_sub_one_le (r : ℝ) (l z : ℂ) (hz : ‖z‖ ≤ r) (hl : 2 * r ≤ ‖l‖) :
    ‖wFactor l z - 1‖ ≤ 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
  have hr : 0 ≤ r := (norm_nonneg z).trans hz
  have hrp : ‖l‖ ^ (-3 : ℝ) = (‖l‖ ^ 3)⁻¹ := by
    rw [Real.rpow_neg (norm_nonneg _)]
    norm_cast
  rcases eq_or_ne l 0 with rfl | hl0
  · have h1 : wFactor 0 z = 1 := by simp [wFactor]
    rw [h1, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hr 3)) (Real.rpow_nonneg le_rfl _)
  have hlpos : 0 < ‖l‖ := norm_pos_iff.mpr hl0
  have hw : ‖z / l‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hlpos]
    linarith
  calc ‖wFactor l z - 1‖ ≤ 2 * ‖z / l‖ ^ 3 := by
        rw [wFactor_eq]
        exact norm_factor_sub_one_le _ hw
    _ = 2 * ‖z‖ ^ 3 * (‖l‖ ^ 3)⁻¹ := by rw [norm_div, div_pow]; ring
    _ ≤ 2 * r ^ 3 * (‖l‖ ^ 3)⁻¹ := by gcongr
    _ = 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by rw [hrp]

/- English proof (translation)
Establish `hfin : Module.finrank ℤ L.lattice = 2`. Rewrite using `[ZLattice.rank ℝ L.lattice, Complex.finrank_real_complex]`. Conclude with `ZLattice.summable_norm_rpow L.lattice (-3) (by rw [hfin]; norm_num)`.
-/
private lemma summable_norm_lattice_rpow_neg_three (L : PeriodPair) :
    Summable (fun l : L.lattice => ‖(l : ℂ)‖ ^ (-3 : ℝ)) := by
  have hfin : Module.finrank ℤ L.lattice = 2 := by
    rw [ZLattice.rank ℝ L.lattice, Complex.finrank_real_complex]
  exact ZLattice.summable_norm_rpow L.lattice (-3) (by rw [hfin]; norm_num)

/- English proof (translation)
The claim follows from `(summable_norm_lattice_rpow_neg_three L).mul_left _`.
-/
lemma summable_majorant (L : PeriodPair) (r : ℝ) :
    Summable (fun l : L.lattice => 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ)) :=
  (summable_norm_lattice_rpow_neg_three L).mul_left _

/- English proof (translation)
Break down `le_or_gt R 0 with hR | hR` into its components or cases. Conclude with `Eventually.of_forall fun l => hR.trans (norm_nonneg _)`. Establish `ht` using `(summable_norm_lattice_rpow_neg_three L).tendsto_cofinite_zero`. Establish `hε : (0 : ℝ) < R ^ (-3 : ℝ)` using `Real.rpow_pos_of_pos hR _`. Use `filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_cofinite_ne 0] with l hl hl0`.

Establish `hpos : 0 < ‖(l : ℂ)‖`. Rewrite using `[norm_pos_iff]`. Conclude with `fun h => hl0 (Subtype.ext h)`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Use `Real.rpow_le_rpow_of_nonpos hpos hlt.le (by norm_num : (-3 : ℝ) ≤ 0)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma eventually_large (L : PeriodPair) (R : ℝ) :
    ∀ᶠ l : L.lattice in cofinite, R ≤ ‖(l : ℂ)‖ := by
  rcases le_or_gt R 0 with hR | hR
  · exact Eventually.of_forall fun l => hR.trans (norm_nonneg _)
  have ht := (summable_norm_lattice_rpow_neg_three L).tendsto_cofinite_zero
  have hε : (0 : ℝ) < R ^ (-3 : ℝ) := Real.rpow_pos_of_pos hR _
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_cofinite_ne 0] with l hl hl0
  have hpos : 0 < ‖(l : ℂ)‖ := by
    rw [norm_pos_iff]
    exact fun h => hl0 (Subtype.ext h)
  by_contra hlt
  push_neg at hlt
  have := Real.rpow_le_rpow_of_nonpos hpos hlt.le (by norm_num : (-3 : ℝ) ≤ 0)
  linarith

/- English proof (translation)
Unfold `wFactor`. Use `fun_prop`.
-/
lemma continuous_wFactor (l : ℂ) : Continuous (wFactor l) := by
  unfold wFactor
  fun_prop

end SigmaConv

open SigmaConv

/- English proof (translation)
Introduce `L z`. Use `Summable.of_norm_bounded_eventually (summable_majorant L ‖z‖) ?_` and prove the remaining obligations. Use `filter_upwards [eventually_large L (2 * ‖z‖)] with l hl`. Rewrite using `[norm_norm]`. Conclude with `norm_wFactor_sub_one_le ‖z‖ l z le_rfl hl`.
-/
theorem sigma_summable : SigmaSummable := by
  intro L z
  refine Summable.of_norm_bounded_eventually (summable_majorant L ‖z‖) ?_
  filter_upwards [eventually_large L (2 * ‖z‖)] with l hl
  rw [norm_norm]
  exact norm_wFactor_sub_one_le ‖z‖ l z le_rfl hl

/- English proof (translation)
Introduce `L`. Establish `key : HasProdLocallyUniformlyOn (fun (l : L.lattice) (z : ℂ) => 1 + (wFactor (l : ℂ) z - 1)) (fun z => ∏' l : L.lattice, (1 + (wFactor (l : ℂ) z - 1))) Set.univ`. Rewrite using `[HasProdLocallyUniformlyOn, tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]`. Introduce `K _ hK`. Take `⟨r, hr⟩` from `hK.isBounded.subset_closedBall 0`.

Use `HasProdUniformlyOn.tendstoUniformlyOn <| Summable.hasProdUniformlyOn_one_add (f := fun (l : L.lattice) (z : ℂ) => wFactor (l : ℂ) z - 1) hK (summable_majorant L r) ?_ ?_` and prove the remaining obligations. Use `filter_upwards [eventually_large L (2 * r)] with l hl x hx`. Conclude with `norm_wFactor_sub_one_le r l x (by simpa using hr hx) hl`. Introduce `l`. Conclude with `((continuous_wFactor _).sub continuous_const).continuousOn`.

Simplify `key` using `only [add_sub_cancel]`.
-/
theorem sigma_product_locally_uniform : SigmaProdLU := by
  intro L
  have key : HasProdLocallyUniformlyOn (fun (l : L.lattice) (z : ℂ) => 1 + (wFactor (l : ℂ) z - 1))
      (fun z => ∏' l : L.lattice, (1 + (wFactor (l : ℂ) z - 1))) Set.univ := by
    rw [HasProdLocallyUniformlyOn, tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    refine HasProdUniformlyOn.tendstoUniformlyOn <| Summable.hasProdUniformlyOn_one_add (f := fun (l : L.lattice) (z : ℂ) => wFactor (l : ℂ) z - 1)
      hK (summable_majorant L r) ?_ ?_
    · filter_upwards [eventually_large L (2 * r)] with l hl x hx
      exact norm_wFactor_sub_one_le r l x (by simpa using hr hx) hl
    · intro l
      exact ((continuous_wFactor _).sub continuous_const).continuousOn
  simpa only [add_sub_cancel] using key

end Formalism.L2.Th1.F
