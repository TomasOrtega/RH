import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearHalfMax
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Metric

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
Unfold `NonvanishingNearHalfMax`. Introduce `r X la P z0 x0 w hSec hz0 hx0o ⟨b, hb, hx0⟩ hmax hpos hw hw1 hr Z hZ hPZ`. Establish `hx0d : x0 ∈ X.dom` using `by rw [hx0]; exact OrthogonalFrameDomain.rmul_mem_dom (X := X) hz0 hb`. Establish `hpx : X.pnorm la P x0 = X.pnorm la P z0`. Rewrite using `[hx0]`.

Conclude with `FrameDegreeData.pnorm_rmul (X := X) la P hSec.2.1 z0 hz0 b hb`. Establish `hpn : ∀ y, X.pnorm la P y = ‖P y‖ * X.nfac la y` using `fun y => rfl`. Establish `hr1 : (1 : ℝ) ≤ r` using `Nat.one_le_cast.mpr hr`. Establish `hw0 : w ≠ 0` using `by positivity`. Establish `hr0 : (r : ℝ) ≠ 0` using `by positivity`.

Establish `hwr : 0 < w * r` using `by nlinarith`. Establish `hwr1 : 1 ≤ w * r` using `by nlinarith`. Establish `hsq : Real.sqrt (w * r) ^ 2 = w * r` using `Real.sq_sqrt hwr.le`. Establish `hs1 : 1 ≤ Real.sqrt (w * r)` using `by nlinarith [Real.sqrt_nonneg (w * r)]`. Use `set ρ := frameRadius w r with hρdef`.

Establish `hρpos : 0 < ρ` using `by rw [hρdef, frameRadius]; positivity`. Establish `hρle : ρ ≤ 1 / 10`. Rewrite using `[hρdef, frameRadius]`. Conclude with `div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)`. Establish `hρsq : 4 * w * r * ρ ^ 2 = 1 / 25`.

Rewrite using `[hρdef, frameRadius, div_pow, mul_pow, hsq]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hM0 : 0 < ‖P x0‖`. Establish `h1 : 0 < X.pnorm la P x0` using `hpx ▸ hpos`.

Rewrite `h1` using `[hpn]`. Break down `(norm_nonneg (P x0)).lt_or_eq with h | h` into its components or cases. Conclude with `h`. Rewrite `h1` using `[← h, zero_mul]`. Conclude with `absurd h1 (lt_irrefl 0)`.

Establish `hzt : ∀ t : ℂ, ‖t‖ < 5 → X.zN (t • Z) ≤ ρ` using `fun t ht => (OrthogonalFrameDomain.zN_smul_le (X := X) t Z).trans (by nlinarith [OrthogonalFrameDomain.zN_nonneg (X := X) Z, norm_nonneg t])`. Establish `hdom : ∀ t : ℂ, ‖t‖ < 5 → X.xZ x0 (t • Z) ∈ X.dom` using `fun t ht => OrthonormalChartBounds.xZ_mem_dom (X := X) hx0d hx0o (lt_of_le_of_lt (hzt t ht) (by linarith))`. Establish `hbound : ∀ t : ℂ, ‖t‖ < 5 → ‖P (X.xZ x0 (t • Z))‖ < 3 * ‖P x0‖`. Introduce `t ht`. Establish `hyd` using `hdom t ht`.

Establish `hny` using `BoundedSectionAlgebra.nfac_pos (X := X) hyd la`. Establish `hnx` using `BoundedSectionAlgebra.nfac_pos (X := X) hx0d la`. Establish `hlog` using `OrthonormalChartBounds.nfac_xZ (X := X) hx0d hx0o hρpos hρle (hzt t ht) la w hw`. Establish `hz2 : 4 * w * r * X.zN (t • Z) ^ 2 ≤ 1 / 25`. Rewrite using `[← hρsq]`.

Establish `hwr4 : 0 ≤ 4 * w * r` using `by nlinarith`. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (OrthogonalFrameDomain.zN_nonneg (X := X) _) (hzt t ht) 2) hwr4`. Establish `hlow : Real.log (X.nfac la x0) - 1 / 25 ≤ Real.log (X.nfac la (X.xZ x0 (t • Z)))`. Use `(abs_le.mp (hlog.trans hz2)).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hexp : X.nfac la x0 * Real.exp (-(1 / 25)) ≤ X.nfac la (X.xZ x0 (t • Z))`. Rewrite using `[← Real.exp_log hnx, ← Real.exp_log hny, ← Real.exp_add]`. Conclude with `Real.exp_le_exp.mpr (by linarith)`. Establish `hpy : X.pnorm la P (X.xZ x0 (t • Z)) ≤ 2 * X.pnorm la P x0`. Rewrite using `[hpx]`.

Conclude with `hmax _ hyd`. Rewrite `hpy` using `[hpn, hpn]`. Establish `h1 : ‖P (X.xZ x0 (t • Z))‖ * (X.nfac la x0 * Real.exp (-(1 / 25))) ≤ 2 * (‖P x0‖ * X.nfac la x0)` using `(mul_le_mul_of_nonneg_left hexp (norm_nonneg _)).trans hpy`. Establish `h2 : ‖P (X.xZ x0 (t • Z))‖ * Real.exp (-(1 / 25)) ≤ 2 * ‖P x0‖`. Establish `h3 : (‖P (X.xZ x0 (t • Z))‖ * Real.exp (-(1 / 25))) * X.nfac la x0 ≤ (2 * ‖P x0‖) * X.nfac la x0` using `by nlinarith`.

Conclude with `le_of_mul_le_mul_right h3 hnx`. Establish `hE : Real.exp (-(1 / 25)) * Real.exp (1 / 25) = 1`. Rewrite using `[← Real.exp_add]`. Simplify using the standard rewrite rules. Establish `h4 : ‖P (X.xZ x0 (t • Z))‖ ≤ 2 * ‖P x0‖ * Real.exp (1 / 25)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, hE, mul_one]`. Use `_ ≤ 2 * ‖P x0‖ * Real.exp (1 / 25) := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le`. Establish `he` using `OrthogonalFrameDomain.exp_small`. Use polynomial arithmetic with `[mul_lt_mul_of_pos_left he hM0]`.

Establish `h5 : ∀ s ∈ Metric.ball (1 : ℂ) 4, ‖s‖ < 5`. Introduce `s hs`. Rewrite `hs` using `[Metric.mem_ball, dist_eq_norm]`. Combine the equalities or inequalities in the displayed calculation. Use `set g : ℂ → ℂ := fun t => P (X.xZ x0 (t • Z)) with hg`.

Establish `hg1 : g 1 = 0` using `by simp only [hg, one_smul]; exact hPZ`. Establish `hg0 : g 0 = P x0` using `by simp only [hg, zero_smul, (OrthogonalFrameDomain.xZ_zero (X := X))]`. Establish `hgd : DifferentiableOn ℂ g (Metric.ball 1 4)`. Introduce `t ht`. Establish `hin : DifferentiableAt ℂ (fun s : ℂ => X.xZ x0 (s • Z)) t` using `(OrthogonalFrameDomain.xZ_diff (X := X) x0).differentiableAt.comp t (differentiableAt_id.smul_const Z)`.

Conclude with `(hSec.1 _ (hdom t (h5 t ht))).comp t hin.differentiableWithinAt (fun s hs => hdom s (h5 s hs))`. Establish `hmaps : Set.MapsTo g (Metric.ball 1 4) (Metric.closedBall (g 1) (3 * ‖P x0‖))`. Introduce `s hs`. Rewrite using `[Metric.mem_closedBall, dist_eq_norm, hg1, sub_zero]`. Conclude with `(hbound s (h5 s hs)).le`.

Establish `hd : dist (0 : ℂ) 1 = 1` using `by simp [dist_eq_norm]`. Establish `h0 : (0 : ℂ) ∈ Metric.ball (1 : ℂ) 4` using `by rw [Metric.mem_ball, hd]; norm_num`. Establish `hS` using `Complex.dist_le_div_mul_dist_of_mapsTo_ball hgd hmaps h0`. Rewrite `hS` using `[hg0, hg1, dist_zero_right, hd, mul_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nonvanishingNearHalfMax_holds : NonvanishingNearHalfMax (E := E) := by
  unfold NonvanishingNearHalfMax
  intro r X la P z0 x0 w hSec hz0 hx0o ⟨b, hb, hx0⟩ hmax hpos hw hw1 hr Z hZ hPZ
  have hx0d : x0 ∈ X.dom := by rw [hx0]; exact OrthogonalFrameDomain.rmul_mem_dom (X := X) hz0 hb
  have hpx : X.pnorm la P x0 = X.pnorm la P z0 := by
    rw [hx0]; exact FrameDegreeData.pnorm_rmul (X := X) la P hSec.2.1 z0 hz0 b hb
  have hpn : ∀ y, X.pnorm la P y = ‖P y‖ * X.nfac la y := fun y => rfl
  have hr1 : (1 : ℝ) ≤ r := Nat.one_le_cast.mpr hr
  have hw0 : w ≠ 0 := by positivity
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  have hwr : 0 < w * r := by nlinarith
  have hwr1 : 1 ≤ w * r := by nlinarith
  have hsq : Real.sqrt (w * r) ^ 2 = w * r := Real.sq_sqrt hwr.le
  have hs1 : 1 ≤ Real.sqrt (w * r) := by nlinarith [Real.sqrt_nonneg (w * r)]
  set ρ := frameRadius w r with hρdef
  have hρpos : 0 < ρ := by rw [hρdef, frameRadius]; positivity
  have hρle : ρ ≤ 1 / 10 := by
    rw [hρdef, frameRadius]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hρsq : 4 * w * r * ρ ^ 2 = 1 / 25 := by
    rw [hρdef, frameRadius, div_pow, mul_pow, hsq]
    field_simp
    ring
  have hM0 : 0 < ‖P x0‖ := by
    have h1 : 0 < X.pnorm la P x0 := hpx ▸ hpos
    rw [hpn] at h1
    rcases (norm_nonneg (P x0)).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at h1
      exact absurd h1 (lt_irrefl 0)
  have hzt : ∀ t : ℂ, ‖t‖ < 5 → X.zN (t • Z) ≤ ρ := fun t ht =>
    (OrthogonalFrameDomain.zN_smul_le (X := X) t Z).trans (by nlinarith [OrthogonalFrameDomain.zN_nonneg (X := X) Z, norm_nonneg t])
  have hdom : ∀ t : ℂ, ‖t‖ < 5 → X.xZ x0 (t • Z) ∈ X.dom := fun t ht =>
    OrthonormalChartBounds.xZ_mem_dom (X := X) hx0d hx0o (lt_of_le_of_lt (hzt t ht) (by linarith))
  have hbound : ∀ t : ℂ, ‖t‖ < 5 → ‖P (X.xZ x0 (t • Z))‖ < 3 * ‖P x0‖ := by
    intro t ht
    have hyd := hdom t ht
    have hny := BoundedSectionAlgebra.nfac_pos (X := X) hyd la
    have hnx := BoundedSectionAlgebra.nfac_pos (X := X) hx0d la
    have hlog := OrthonormalChartBounds.nfac_xZ (X := X) hx0d hx0o hρpos hρle (hzt t ht) la w hw
    have hz2 : 4 * w * r * X.zN (t • Z) ^ 2 ≤ 1 / 25 := by
      rw [← hρsq]
      have hwr4 : 0 ≤ 4 * w * r := by nlinarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (OrthogonalFrameDomain.zN_nonneg (X := X) _) (hzt t ht) 2) hwr4
    have hlow : Real.log (X.nfac la x0) - 1 / 25 ≤ Real.log (X.nfac la (X.xZ x0 (t • Z))) := by
      have := (abs_le.mp (hlog.trans hz2)).1
      linarith
    have hexp : X.nfac la x0 * Real.exp (-(1 / 25)) ≤ X.nfac la (X.xZ x0 (t • Z)) := by
      rw [← Real.exp_log hnx, ← Real.exp_log hny, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hpy : X.pnorm la P (X.xZ x0 (t • Z)) ≤ 2 * X.pnorm la P x0 := by
      rw [hpx]; exact hmax _ hyd
    rw [hpn, hpn] at hpy
    have h1 : ‖P (X.xZ x0 (t • Z))‖ * (X.nfac la x0 * Real.exp (-(1 / 25))) ≤
        2 * (‖P x0‖ * X.nfac la x0) :=
      (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)).trans hpy
    have h2 : ‖P (X.xZ x0 (t • Z))‖ * Real.exp (-(1 / 25)) ≤ 2 * ‖P x0‖ := by
      have h3 : (‖P (X.xZ x0 (t • Z))‖ * Real.exp (-(1 / 25))) * X.nfac la x0 ≤
          (2 * ‖P x0‖) * X.nfac la x0 := by nlinarith
      exact le_of_mul_le_mul_right h3 hnx
    have hE : Real.exp (-(1 / 25)) * Real.exp (1 / 25) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 : ‖P (X.xZ x0 (t • Z))‖ ≤ 2 * ‖P x0‖ * Real.exp (1 / 25) := by
      calc ‖P (X.xZ x0 (t • Z))‖
          = ‖P (X.xZ x0 (t • Z))‖ * Real.exp (-(1 / 25)) * Real.exp (1 / 25) := by
            rw [mul_assoc, hE, mul_one]
        _ ≤ 2 * ‖P x0‖ * Real.exp (1 / 25) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    have he := OrthogonalFrameDomain.exp_small
    nlinarith [mul_lt_mul_of_pos_left he hM0]
  have h5 : ∀ s ∈ Metric.ball (1 : ℂ) 4, ‖s‖ < 5 := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm] at hs
    calc ‖s‖ = ‖(s - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ < 5 := by rw [norm_one]; linarith
  set g : ℂ → ℂ := fun t => P (X.xZ x0 (t • Z)) with hg
  have hg1 : g 1 = 0 := by simp only [hg, one_smul]; exact hPZ
  have hg0 : g 0 = P x0 := by simp only [hg, zero_smul, (OrthogonalFrameDomain.xZ_zero (X := X))]
  have hgd : DifferentiableOn ℂ g (Metric.ball 1 4) := by
    intro t ht
    have hin : DifferentiableAt ℂ (fun s : ℂ => X.xZ x0 (s • Z)) t :=
      (OrthogonalFrameDomain.xZ_diff (X := X) x0).differentiableAt.comp t (differentiableAt_id.smul_const Z)
    exact (hSec.1 _ (hdom t (h5 t ht))).comp t hin.differentiableWithinAt
      (fun s hs => hdom s (h5 s hs))
  have hmaps : Set.MapsTo g (Metric.ball 1 4) (Metric.closedBall (g 1) (3 * ‖P x0‖)) := by
    intro s hs
    rw [Metric.mem_closedBall, dist_eq_norm, hg1, sub_zero]
    exact (hbound s (h5 s hs)).le
  have hd : dist (0 : ℂ) 1 = 1 := by simp [dist_eq_norm]
  have h0 : (0 : ℂ) ∈ Metric.ball (1 : ℂ) 4 := by rw [Metric.mem_ball, hd]; norm_num
  have hS := Complex.dist_le_div_mul_dist_of_mapsTo_ball hgd hmaps h0
  rw [hg0, hg1, dist_zero_right, hd, mul_one] at hS
  linarith

end ReciprocityTheory.ChartRestriction.G.FD
