import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville

open Complex Metric

noncomputable section

namespace Formalism.ZF

/- English proof (translation)
Establish `hopen : IsOpen (ball z₀ R)` using `isOpen_ball`. Establish `hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball z₀ R)` using `(hf.deriv hopen).div hf hne`. Take `⟨G, hG⟩` from `hd.isExactOn_ball`. Use `⟨fun z => G z - G z₀, by simp, fun z hz => (hG z hz).sub_const _, ?_⟩` and prove the remaining obligations. Establish `hk : ∀ z ∈ ball z₀ R, HasDerivAt (fun w => f w * Complex.exp (-(G w - G z₀))) 0 z`.

Introduce `z hz`. Establish `hfz : HasDerivAt f (deriv f z) z` using `(hf.differentiableAt (hopen.mem_nhds hz)).hasDerivAt`. Establish `hgz : HasDerivAt (fun w => -(G w - G z₀)) (-(deriv f z / f z)) z` using `((hG z hz).sub_const _).neg`. Establish `h : HasDerivAt (fun w => f w * Complex.exp (-(G w - G z₀))) (deriv f z * Complex.exp (-(G z - G z₀)) + f z * (Complex.exp (-(G z - G z₀)) * -(deriv f z / f z))) z` using `hfz.mul hgz.cexp`. Establish `h0 : deriv f z * Complex.exp (-(G z - G z₀)) + f z * (Complex.exp (-(G z - G z₀)) * -(deriv f z / f z)) = 0`.

Establish `h1` using `hne z hz`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `all_goals ring`. Conclude with `h0 ▸ h`. Introduce `z hz`.

Establish `hz₀ : z₀ ∈ ball z₀ R` using `mem_ball_self (pos_of_mem_ball hz)`. Establish `hconst` using `hopen.is_const_of_deriv_eq_zero (convex_ball z₀ R).isPreconnected (fun w hw => (hk w hw).differentiableAt.differentiableWithinAt) (fun w hw => (hk w hw).deriv) hz hz₀`. Simplify using `only [sub_self, neg_zero, Complex.exp_zero, mul_one] at hconst`. Rewrite using `[← hconst, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]`.
-/
lemma zflb_exists_log {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hne : ∀ z ∈ ball z₀ R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, g z₀ = 0 ∧ (∀ z ∈ ball z₀ R, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ ball z₀ R, f z = f z₀ * Complex.exp (g z) := by
  have hopen : IsOpen (ball z₀ R) := isOpen_ball
  have hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball z₀ R) :=
    (hf.deriv hopen).div hf hne
  obtain ⟨G, hG⟩ := hd.isExactOn_ball
  refine ⟨fun z => G z - G z₀, by simp, fun z hz => (hG z hz).sub_const _, ?_⟩
  have hk : ∀ z ∈ ball z₀ R, HasDerivAt (fun w => f w * Complex.exp (-(G w - G z₀))) 0 z := by
    intro z hz
    have hfz : HasDerivAt f (deriv f z) z := (hf.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
    have hgz : HasDerivAt (fun w => -(G w - G z₀)) (-(deriv f z / f z)) z := ((hG z hz).sub_const _).neg
    have h : HasDerivAt (fun w => f w * Complex.exp (-(G w - G z₀)))
        (deriv f z * Complex.exp (-(G z - G z₀)) +
          f z * (Complex.exp (-(G z - G z₀)) * -(deriv f z / f z))) z :=
      hfz.mul hgz.cexp
    have h0 : deriv f z * Complex.exp (-(G z - G z₀)) +
        f z * (Complex.exp (-(G z - G z₀)) * -(deriv f z / f z)) = 0 := by
      have h1 := hne z hz
      field_simp
      all_goals ring
    exact h0 ▸ h
  intro z hz
  have hz₀ : z₀ ∈ ball z₀ R := mem_ball_self (pos_of_mem_ball hz)
  have hconst := hopen.is_const_of_deriv_eq_zero (convex_ball z₀ R).isPreconnected
    (fun w hw => (hk w hw).differentiableAt.differentiableWithinAt) (fun w hw => (hk w hw).deriv) hz hz₀
  simp only [sub_self, neg_zero, Complex.exp_zero, mul_one] at hconst
  rw [← hconst, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/- English proof (translation)
Introduce `f z₀ R M hR hM hf hne hbd z hz`. Establish `hR0 : R ≠ 0` using `hR.ne'`. Establish `hfb : DifferentiableOn ℂ f (ball z₀ R)` using `hf.mono ball_subset_closedBall`. Establish `hneb : ∀ w ∈ ball z₀ R, f w ≠ 0` using `fun w hw => hne w (ball_subset_closedBall hw)`. Take `⟨g, hg0, hgd, hgf⟩` from `zflb_exists_log hfb hneb`.

Establish `hf0 : 0 < ‖f z₀‖` using `norm_pos_iff.2 (hne z₀ (mem_closedBall_self hR.le))`. Establish `hre : ∀ w ∈ ball z₀ R, (g w).re ≤ Real.log M`. Introduce `w hw`. Establish `h1` using `hbd w (ball_subset_closedBall hw)`. Rewrite `h1` using `[hgf w hw, norm_mul, Complex.norm_exp]`.

Establish `h2 : Real.exp (g w).re ≤ M`. Assume the negation of the conclusion as `h`. Establish `h3` using `mul_lt_mul_of_pos_left (lt_of_not_ge h) hf0`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Establish `hzb : dist z z₀ ≤ R / 2` using `hz`. Establish `hshift : ∀ v ∈ ball (0 : ℂ) R, z₀ + v ∈ ball z₀ R`. Introduce `v hv`. Rewrite using `[mem_ball, dist_eq_norm, add_sub_cancel_left]`. Conclude with `mem_ball_zero_iff.1 hv`.

Establish `hmain : ∀ A : ℝ, Real.log M < A → ‖deriv f z / f z‖ ≤ 24 * A / R`. Introduce `A hA`. Establish `hA0 : 0 < A` using `lt_of_le_of_lt (Real.log_nonneg hM) hA`. Establish `hhd : DifferentiableOn ℂ (fun v => g (z₀ + v)) (ball 0 R)`. Introduce `v hv`.

Conclude with `((hgd _ (hshift v hv)).differentiableAt.comp v (differentiableAt_id.const_add z₀)).differentiableWithinAt`. Establish `hhm : Set.MapsTo (fun v => g (z₀ + v)) (ball 0 R) {w | w.re ≤ A}`. Introduce `v hv`. Conclude with `le_trans (hre _ (hshift v hv)) hA.le`. Establish `hbc : ∀ w ∈ closedBall z₀ (3 * R / 4), ‖g w‖ ≤ 6 * A`.

Introduce `w hw`. Take `⟨u, rfl⟩ : ∃ u, w = z₀ + u` from `⟨w - z₀, by ring⟩`. Rewrite `hw` using `[mem_closedBall, dist_eq_norm, add_sub_cancel_left]`. Establish `huR : u ∈ ball (0 : ℂ) R`. Rewrite using `[mem_ball_zero_iff]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB : ‖g (z₀ + u)‖ ≤ 2 * A * ‖u‖ / (R - ‖u‖)` using `Complex.borelCaratheodory_zero hA0 hhd hhm hR huR (by simpa using hg0)`. Establish `hpos : 0 < R - ‖u‖` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_le_iff₀ hpos]`.

Use polynomial arithmetic with `[norm_nonneg u]`. Establish `hR4 : 0 < R / 4` using `by linarith`. Establish `hsub : closedBall z (R / 4) ⊆ ball z₀ R`. Introduce `w hw`. Rewrite `hw` using `[mem_closedBall]`.

Rewrite using `[mem_ball]`. Combine the equalities or inequalities in the displayed calculation. Establish `hdiff : DiffContOnCl ℂ g (ball z (R / 4))`. Apply `DifferentiableOn.diffContOnCl` to reduce the goal to its premises. Rewrite using `[closure_ball z hR4.ne']`.

Introduce `w hw`. Conclude with `(hgd w (hsub hw)).differentiableAt.differentiableWithinAt`. Establish `hC : ∀ w ∈ sphere z (R / 4), ‖g w‖ ≤ 6 * A`. Introduce `w hw`. Apply `hbc` to reduce the goal to its premises.

Rewrite `hw` using `[mem_sphere]`. Rewrite using `[mem_closedBall]`. Combine the equalities or inequalities in the displayed calculation. Establish `hzb' : z ∈ ball z₀ R` using `hsub (mem_closedBall_self hR4.le)`. Establish `hder` using `norm_deriv_le_of_forall_mem_sphere_norm_le hR4 hdiff hC`.

Rewrite `hder` using `[(hgd z hzb').deriv]`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `all_goals ring`. Apply `le_of_forall_pos_le_add` to reduce the goal to its premises.

Introduce `ε hε`. Establish `hεR : 0 < ε * R / 24` using `by positivity`. Establish `h` using `hmain (Real.log M + ε * R / 24) (by linarith)`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts.
-/
theorem logDerivBoundOnBall : LogDerivBound := by
  intro f z₀ R M hR hM hf hne hbd z hz
  have hR0 : R ≠ 0 := hR.ne'
  have hfb : DifferentiableOn ℂ f (ball z₀ R) := hf.mono ball_subset_closedBall
  have hneb : ∀ w ∈ ball z₀ R, f w ≠ 0 := fun w hw => hne w (ball_subset_closedBall hw)
  obtain ⟨g, hg0, hgd, hgf⟩ := zflb_exists_log hfb hneb
  have hf0 : 0 < ‖f z₀‖ := norm_pos_iff.2 (hne z₀ (mem_closedBall_self hR.le))
  have hre : ∀ w ∈ ball z₀ R, (g w).re ≤ Real.log M := by
    intro w hw
    have h1 := hbd w (ball_subset_closedBall hw)
    rw [hgf w hw, norm_mul, Complex.norm_exp] at h1
    have h2 : Real.exp (g w).re ≤ M := by
      by_contra h
      have h3 := mul_lt_mul_of_pos_left (lt_of_not_ge h) hf0
      linarith
    calc (g w).re = Real.log (Real.exp (g w).re) := (Real.log_exp _).symm
      _ ≤ Real.log M := Real.log_le_log (Real.exp_pos _) h2
  have hzb : dist z z₀ ≤ R / 2 := hz
  have hshift : ∀ v ∈ ball (0 : ℂ) R, z₀ + v ∈ ball z₀ R := by
    intro v hv
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact mem_ball_zero_iff.1 hv
  have hmain : ∀ A : ℝ, Real.log M < A → ‖deriv f z / f z‖ ≤ 24 * A / R := by
    intro A hA
    have hA0 : 0 < A := lt_of_le_of_lt (Real.log_nonneg hM) hA
    have hhd : DifferentiableOn ℂ (fun v => g (z₀ + v)) (ball 0 R) := by
      intro v hv
      exact ((hgd _ (hshift v hv)).differentiableAt.comp v
        (differentiableAt_id.const_add z₀)).differentiableWithinAt
    have hhm : Set.MapsTo (fun v => g (z₀ + v)) (ball 0 R) {w | w.re ≤ A} := by
      intro v hv
      exact le_trans (hre _ (hshift v hv)) hA.le
    have hbc : ∀ w ∈ closedBall z₀ (3 * R / 4), ‖g w‖ ≤ 6 * A := by
      intro w hw
      obtain ⟨u, rfl⟩ : ∃ u, w = z₀ + u := ⟨w - z₀, by ring⟩
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left] at hw
      have huR : u ∈ ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff]
        linarith
      have hB : ‖g (z₀ + u)‖ ≤ 2 * A * ‖u‖ / (R - ‖u‖) :=
        Complex.borelCaratheodory_zero hA0 hhd hhm hR huR (by simpa using hg0)
      have hpos : 0 < R - ‖u‖ := by linarith
      calc ‖g (z₀ + u)‖ ≤ 2 * A * ‖u‖ / (R - ‖u‖) := hB
        _ ≤ 6 * A := by
          rw [div_le_iff₀ hpos]
          nlinarith [norm_nonneg u]
    have hR4 : 0 < R / 4 := by linarith
    have hsub : closedBall z (R / 4) ⊆ ball z₀ R := by
      intro w hw
      rw [mem_closedBall] at hw
      rw [mem_ball]
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < R := by linarith
    have hdiff : DiffContOnCl ℂ g (ball z (R / 4)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball z hR4.ne']
      intro w hw
      exact (hgd w (hsub hw)).differentiableAt.differentiableWithinAt
    have hC : ∀ w ∈ sphere z (R / 4), ‖g w‖ ≤ 6 * A := by
      intro w hw
      apply hbc
      rw [mem_sphere] at hw
      rw [mem_closedBall]
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ ≤ 3 * R / 4 := by linarith
    have hzb' : z ∈ ball z₀ R := hsub (mem_closedBall_self hR4.le)
    have hder := norm_deriv_le_of_forall_mem_sphere_norm_le hR4 hdiff hC
    rw [(hgd z hzb').deriv] at hder
    calc ‖deriv f z / f z‖ ≤ 6 * A / (R / 4) := hder
      _ = 24 * A / R := by
        field_simp
        all_goals ring
  apply le_of_forall_pos_le_add
  intro ε hε
  have hεR : 0 < ε * R / 24 := by positivity
  have h := hmain (Real.log M + ε * R / 24) (by linarith)
  calc ‖deriv f z / f z‖ ≤ 24 * (Real.log M + ε * R / 24) / R := h
    _ = 24 * Real.log M / R + ε := by
      field_simp

end Formalism.ZF
