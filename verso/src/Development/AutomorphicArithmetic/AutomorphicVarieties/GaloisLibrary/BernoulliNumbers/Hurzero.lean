import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Termdiff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Termsum

open Finset UpperTheory.V.Bern

/- English proof (translation)
Introduce `x hx0 hx1`. Use `set U : Set ℂ := {s | -1 / 2 < s.re} ∩ Metric.ball 0 3 with hU`. Establish `hUo : IsOpen U` using `(isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball`. Establish `hUc : IsPreconnected U` using `((convex_halfSpace_re_gt _).inter (convex_ball _ _)).isPreconnected`. Establish `hG : DifferentiableOn ℂ (fun s => HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s - HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s - (1 - (x : ℂ))) U`.

Introduce `s _`. Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Apply `DifferentiableAt.sub_const` to reduce the goal to its premises. Break down `eq_or_ne s 1 with rfl | hs` into its components or cases. Use `(HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div (x : UnitAddCircle)).sub (HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div ((1 : ℝ) : UnitAddCircle))` as an intermediate fact.

Conclude with `this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by`. Simplify using `only [Pi.sub_apply]`. Use the proof step `ring)`. Conclude with `(HurwitzZeta.differentiableAt_hurwitzZeta _ hs).sub (HurwitzZeta.differentiableAt_hurwitzZeta _ hs)`. Establish `hev : ∀ᶠ s in nhds (2 : ℂ), 1 < s.re` using `(Complex.continuous_re.tendsto 2).eventually (lt_mem_nhds (by norm_num))`.

Establish `h2 : (2 : ℂ) ∈ U` using `⟨by simp; norm_num, by simp; norm_num⟩`. Establish `heq` using `((b_termdiff x hx0 hx1).analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hUo) hUc h2 (hev.mono fun s hs => b_termsum x hx0 hx1 s hs)`. Establish `h0` using `heq (show (0 : ℂ) ∈ U from ⟨by simp; norm_num, by simp⟩)`. Establish `h1 : HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) 0 = -1 / 2`. Rewrite using `[AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero, riemannZeta_zero]`.

Simplify using `only [neg_zero, Complex.cpow_zero, sub_self, mul_zero, tsum_zero] at h0`. Rewrite `h0` using `[h1]`. Take the linear combination `-h0`.
-/
theorem UpperTheory.V.Bern.b_hurzero :
    ∀ (x : ℝ), 0 < x → x ≤ 1 → HurwitzZeta.hurwitzZeta (x : UnitAddCircle) 0 = 1 / 2 - (x : ℂ) := by
  intro x hx0 hx1
  set U : Set ℂ := {s | -1 / 2 < s.re} ∩ Metric.ball 0 3 with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hUc : IsPreconnected U := ((convex_halfSpace_re_gt _).inter (convex_ball _ _)).isPreconnected
  have hG : DifferentiableOn ℂ (fun s => HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s
      - HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s - (1 - (x : ℂ))) U := by
    intro s _
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.sub_const
    rcases eq_or_ne s 1 with rfl | hs
    · have := (HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div (x : UnitAddCircle)).sub
        (HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div ((1 : ℝ) : UnitAddCircle))
      exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
        simp only [Pi.sub_apply]; ring)
    · exact (HurwitzZeta.differentiableAt_hurwitzZeta _ hs).sub
        (HurwitzZeta.differentiableAt_hurwitzZeta _ hs)
  have hev : ∀ᶠ s in nhds (2 : ℂ), 1 < s.re :=
    (Complex.continuous_re.tendsto 2).eventually (lt_mem_nhds (by norm_num))
  have h2 : (2 : ℂ) ∈ U := ⟨by simp; norm_num, by simp; norm_num⟩
  have heq := ((b_termdiff x hx0 hx1).analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hG.analyticOnNhd hUo) hUc h2 (hev.mono fun s hs => b_termsum x hx0 hx1 s hs)
  have h0 := heq (show (0 : ℂ) ∈ U from ⟨by simp; norm_num, by simp⟩)
  have h1 : HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) 0 = -1 / 2 := by
    rw [AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero, riemannZeta_zero]
  simp only [neg_zero, Complex.cpow_zero, sub_self, mul_zero, tsum_zero] at h0
  rw [h1] at h0
  linear_combination -h0
