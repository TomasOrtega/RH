import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Metric

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
Introduce `r X la P z0 x0 w hP hz0 ho hb0 hmax hpos hw hw1 hr Z hZ`. Take `⟨b, hb, rfl⟩` from `hb0`. Establish `hx0 : rmul z0 b ∈ X.dom` using `OrthogonalFrameDomain.rmul_mem_dom X hz0 hb`. Establish `hpn : X.pnorm la P (rmul z0 b) = X.pnorm la P z0` using `FrameDegreeData.pnorm_rmul X la P hP.2.1 z0 hz0 b hb`. Establish `hpe : ∀ y, X.pnorm la P y = ‖P y‖ * X.nfac la y` using `fun y => rfl`.

Use `set x0 := rmul z0 b with hx0def`. Use `set ρ := frameRadius w r with hρdef`. Establish `hr1 : (1 : ℝ) ≤ r` using `Nat.one_le_cast.2 hr`. Establish `hwr : 1 ≤ w * r` using `by nlinarith`. Establish `hsq : 1 ≤ Real.sqrt (w * r)` using `Real.one_le_sqrt.2 hwr`.

Establish `hs0 : 0 < Real.sqrt (w * r)` using `by linarith`. Establish `hρ0 : 0 < ρ`. Rewrite using `[hρdef]`. Unfold `frameRadius`. Conclude with `one_div_pos.2 (mul_pos (by norm_num) hs0)`.

Establish `hρ10 : ρ ≤ 1 / 10`. Rewrite using `[hρdef]`. Unfold `frameRadius`. Rewrite using `[div_le_div_iff₀ (mul_pos (by norm_num) hs0) (by norm_num)]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hρsq : 4 * w * r * ρ ^ 2 = 1 / 25`. Rewrite using `[hρdef]`. Unfold `frameRadius`. Rewrite using `[div_pow, mul_pow, Real.sq_sqrt (by linarith)]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hw0 : 0 ≤ 4 * w * r` using `by nlinarith`. Establish `hnx` using `BoundedSectionAlgebra.nfac_pos X hx0 la`. Establish `hS : 0 < ‖P x0‖`. Break down `(norm_nonneg (P x0)).lt_or_eq with h | h` into its components or cases.

Conclude with `h`. It suffices to derive a contradiction. Rewrite `hpos` using `[← hpn, hpe, ← h, zero_mul]`. Conclude with `lt_irrefl _ hpos`. Establish `hbd : ∀ Z' : X.Coord, X.zN Z' < ρ → ‖P (X.xZ x0 Z')‖ ≤ Real.exp (1 / 25) * ‖P x0‖`.

Introduce `Z' hZ'`. Establish `hy` using `OrthonormalChartBounds.xZ_mem_dom X hx0 ho (by linarith : X.zN Z' < 1)`. Establish `hlog` using `OrthonormalChartBounds.nfac_xZ X hx0 ho hρ0 hρ10 hZ'.le la w hw`. Establish `hzn` using `OrthogonalFrameDomain.zN_nonneg X Z'`. Establish `hz2 : 4 * w * r * X.zN Z' ^ 2 ≤ 1 / 25`.

Rewrite using `[← hρsq]`. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hzn hZ'.le 2) hw0`. Establish `hny` using `BoundedSectionAlgebra.nfac_pos X hy la`. Establish `h1 : Real.log (X.nfac la x0) - Real.log (X.nfac la (X.xZ x0 Z')) ≤ 1 / 25`. Use `(abs_le.1 (hlog.trans hz2)).1` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : X.nfac la x0 ≤ Real.exp (1 / 25) * X.nfac la (X.xZ x0 Z')`. Use `Real.exp_le_exp.2 h1` as an intermediate fact. Rewrite `this` using `[Real.exp_sub, Real.exp_log hnx, Real.exp_log hny, div_le_iff₀ hny]`. Conclude with `this`.

Establish `h3` using `hmax _ hy`. Rewrite `h3` using `[← hpn, hpe, hpe]`. Establish `h4 : ‖P (X.xZ x0 Z')‖ * X.nfac la (X.xZ x0 Z') ≤ (Real.exp (1 / 25) * ‖P x0‖) * X.nfac la (X.xZ x0 Z')`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_of_mul_le_mul_right h4 hny`.

Use `set f : ℂ → ℂ := fun t => P (X.xZ x0 (t • Z)) with hf`. Establish `hmapsdom : ∀ t ∈ ball (0 : ℂ) 3, X.zN (t • Z) < ρ`. Introduce `t ht`. Rewrite `ht` using `[mem_ball, dist_zero_right]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hd : DifferentiableOn ℂ f (ball 0 3)`. Use `hP.1.comp ((OrthogonalFrameDomain.xZ_diff X x0).comp (differentiable_id.smul_const Z)).differentiableOn ?_` and prove the remaining obligations. Introduce `t ht`. Conclude with `OrthonormalChartBounds.xZ_mem_dom X hx0 ho (by linarith [hmapsdom t ht])`. Establish `hf0 : f 0 = P x0`.

Simplify using `only [hf, zero_smul, OrthogonalFrameDomain.xZ_zero]`. Establish `hmaps : Set.MapsTo f (ball 0 3) (closedBall (f 0) (5 / 2 * ‖P x0‖))`. Introduce `t ht`. Rewrite using `[mem_closedBall, dist_eq_norm, hf0]`. Establish `h1 : ‖f t‖ ≤ Real.exp (1 / 25) * ‖P x0‖` using `hbd _ (hmapsdom t ht)`.

Establish `he` using `OrthogonalFrameDomain.exp_small`. Combine the equalities or inequalities in the displayed calculation. Establish `h1mem : (1 : ℂ) ∈ ball (0 : ℂ) 3`. Rewrite using `[mem_ball, dist_zero_right]`. Evaluate the numerical expressions.

Establish `hS2` using `Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps h1mem`. Introduce `h0`. Establish `hf1 : f 1 = 0`. Simplify using `only [hf, one_smul]`. Conclude with `h0`.

Rewrite `hS2` using `[hf1, hf0, dist_zero_left, dist_zero_right, norm_one, mul_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nonvanishingNearMaximum_holds : NonvanishingNearMaximum (E := E) := by
  intro r X la P z0 x0 w hP hz0 ho hb0 hmax hpos hw hw1 hr Z hZ
  obtain ⟨b, hb, rfl⟩ := hb0
  have hx0 : rmul z0 b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom X hz0 hb
  have hpn : X.pnorm la P (rmul z0 b) = X.pnorm la P z0 := FrameDegreeData.pnorm_rmul X la P hP.2.1 z0 hz0 b hb
  have hpe : ∀ y, X.pnorm la P y = ‖P y‖ * X.nfac la y := fun y => rfl
  set x0 := rmul z0 b with hx0def
  set ρ := frameRadius w r with hρdef
  have hr1 : (1 : ℝ) ≤ r := Nat.one_le_cast.2 hr
  have hwr : 1 ≤ w * r := by nlinarith
  have hsq : 1 ≤ Real.sqrt (w * r) := Real.one_le_sqrt.2 hwr
  have hs0 : 0 < Real.sqrt (w * r) := by linarith
  have hρ0 : 0 < ρ := by
    rw [hρdef]
    unfold frameRadius
    exact one_div_pos.2 (mul_pos (by norm_num) hs0)
  have hρ10 : ρ ≤ 1 / 10 := by
    rw [hρdef]
    unfold frameRadius
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hs0) (by norm_num)]
    nlinarith
  have hρsq : 4 * w * r * ρ ^ 2 = 1 / 25 := by
    rw [hρdef]
    unfold frameRadius
    rw [div_pow, mul_pow, Real.sq_sqrt (by linarith)]
    field_simp
    ring
  have hw0 : 0 ≤ 4 * w * r := by nlinarith
  have hnx := BoundedSectionAlgebra.nfac_pos X hx0 la
  have hS : 0 < ‖P x0‖ := by
    rcases (norm_nonneg (P x0)).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← hpn, hpe, ← h, zero_mul] at hpos
      exact lt_irrefl _ hpos
  have hbd : ∀ Z' : X.Coord, X.zN Z' < ρ → ‖P (X.xZ x0 Z')‖ ≤ Real.exp (1 / 25) * ‖P x0‖ := by
    intro Z' hZ'
    have hy := OrthonormalChartBounds.xZ_mem_dom X hx0 ho (by linarith : X.zN Z' < 1)
    have hlog := OrthonormalChartBounds.nfac_xZ X hx0 ho hρ0 hρ10 hZ'.le la w hw
    have hzn := OrthogonalFrameDomain.zN_nonneg X Z'
    have hz2 : 4 * w * r * X.zN Z' ^ 2 ≤ 1 / 25 := by
      rw [← hρsq]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hzn hZ'.le 2) hw0
    have hny := BoundedSectionAlgebra.nfac_pos X hy la
    have h1 : Real.log (X.nfac la x0) - Real.log (X.nfac la (X.xZ x0 Z')) ≤ 1 / 25 := by
      have := (abs_le.1 (hlog.trans hz2)).1
      linarith
    have h2 : X.nfac la x0 ≤ Real.exp (1 / 25) * X.nfac la (X.xZ x0 Z') := by
      have := Real.exp_le_exp.2 h1
      rw [Real.exp_sub, Real.exp_log hnx, Real.exp_log hny, div_le_iff₀ hny] at this
      exact this
    have h3 := hmax _ hy
    rw [← hpn, hpe, hpe] at h3
    have h4 : ‖P (X.xZ x0 Z')‖ * X.nfac la (X.xZ x0 Z') ≤
        (Real.exp (1 / 25) * ‖P x0‖) * X.nfac la (X.xZ x0 Z') :=
      calc _ ≤ ‖P x0‖ * X.nfac la x0 := h3
        _ ≤ ‖P x0‖ * (Real.exp (1 / 25) * X.nfac la (X.xZ x0 Z')) :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = _ := by ring
    exact le_of_mul_le_mul_right h4 hny
  set f : ℂ → ℂ := fun t => P (X.xZ x0 (t • Z)) with hf
  have hmapsdom : ∀ t ∈ ball (0 : ℂ) 3, X.zN (t • Z) < ρ := by
    intro t ht
    rw [mem_ball, dist_zero_right] at ht
    calc X.zN (t • Z) ≤ ‖t‖ * X.zN Z := OrthogonalFrameDomain.zN_smul_le X t Z
      _ ≤ ‖t‖ * (ρ / 3) := mul_le_mul_of_nonneg_left hZ (norm_nonneg t)
      _ < 3 * (ρ / 3) := mul_lt_mul_of_pos_right ht (by positivity)
      _ = ρ := by ring
  have hd : DifferentiableOn ℂ f (ball 0 3) := by
    refine hP.1.comp ((OrthogonalFrameDomain.xZ_diff X x0).comp (differentiable_id.smul_const Z)).differentiableOn ?_
    intro t ht
    exact OrthonormalChartBounds.xZ_mem_dom X hx0 ho (by linarith [hmapsdom t ht])
  have hf0 : f 0 = P x0 := by
    simp only [hf, zero_smul, OrthogonalFrameDomain.xZ_zero]
  have hmaps : Set.MapsTo f (ball 0 3) (closedBall (f 0) (5 / 2 * ‖P x0‖)) := by
    intro t ht
    rw [mem_closedBall, dist_eq_norm, hf0]
    have h1 : ‖f t‖ ≤ Real.exp (1 / 25) * ‖P x0‖ := hbd _ (hmapsdom t ht)
    have he := OrthogonalFrameDomain.exp_small
    calc ‖f t - P x0‖ ≤ ‖f t‖ + ‖P x0‖ := norm_sub_le _ _
      _ ≤ Real.exp (1 / 25) * ‖P x0‖ + ‖P x0‖ := by linarith
      _ ≤ 5 / 2 * ‖P x0‖ := by nlinarith
  have h1mem : (1 : ℂ) ∈ ball (0 : ℂ) 3 := by
    rw [mem_ball, dist_zero_right]
    norm_num
  have hS2 := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps h1mem
  intro h0
  have hf1 : f 1 = 0 := by
    simp only [hf, one_smul]
    exact h0
  rw [hf1, hf0, dist_zero_left, dist_zero_right, norm_one, mul_one] at hS2
  linarith

end ReciprocityTheory.ChartRestriction.G.FD
