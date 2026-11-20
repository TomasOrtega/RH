import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

/- English proof (translation)
Establish `h` using `integral_comp_abs (f := fun x => Real.exp (-ε * x))`. Rewrite using `[h, integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero]`. Clear the denominators using the available nonvanishing facts.
-/
theorem integral_exp_neg_mul_abs {ε : ℝ} (hε : 0 < ε) :
    ∫ u : ℝ, Real.exp (-ε * |u|) = 2 / ε := by
  have h := integral_comp_abs (f := fun x => Real.exp (-ε * x))
  rw [h, integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero]
  field_simp

/- English proof (translation)
Use `Integrable.of_integral_ne_zero ?_` and prove the remaining obligations. Rewrite using `[integral_exp_neg_mul_abs hε]`. Check the signs of the components of the expression.
-/
theorem integrable_exp_neg_mul_abs {ε : ℝ} (hε : 0 < ε) :
    Integrable fun u : ℝ => Real.exp (-ε * |u|) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_exp_neg_mul_abs hε]
  positivity

/- English proof (translation)
Establish `hg1` using `integrable_exp_neg_mul_abs hε`. Establish `hgi : Integrable (fun t : ℝ × ℝ => M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|)))` using `(hg1.mul_prod hg1).const_mul M`. Establish `hbound : ∀ t : ℝ × ℝ, ‖Complex.exp (dot l t) • φ t‖ ≤ M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|))`. Introduce `t`. Rewrite using `[norm_smul, Complex.norm_exp]`.

Establish `hre : (dot l t).re = rdot (l.1.re, l.2.re) t` using `by simp [dot, rdot]`. Rewrite using `[hre]`. Establish `h1 : Real.exp (rdot (l.1.re, l.2.re) t) * Real.exp (-rdot (l.1.re, l.2.re) t) = 1`. Rewrite using `[← Real.exp_add, add_neg_cancel, Real.exp_zero]`. Establish `h2 : Real.exp (-ε * (|t.1| + |t.2|)) = Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|)`.

Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2]`. Take the linear combination `(M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|))) * h1`.

Establish `hc : Continuous (fun t : ℝ × ℝ => Complex.exp (dot l t) • φ t)`. Establish `hd : Continuous (fun t : ℝ × ℝ => dot l t)` using `by simp only [dot]; fun_prop`. Conclude with `(Complex.continuous_exp.comp hd).smul hφ`. Use `⟨hgi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hbound), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[integral_const_mul, Measure.volume_eq_prod, integral_prod_mul (fun u : ℝ => Real.exp (-ε * |u|)) (fun u : ℝ => Real.exp (-ε * |u|)), integral_exp_neg_mul_abs hε]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integrable_and_norm_integral_le (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X]
    (φ : ℝ × ℝ → X) (l : ℂ × ℂ) (ε M : ℝ) (hε : 0 < ε) (hφ : Continuous φ)
    (hb : ∀ t : ℝ × ℝ, ‖φ t‖ ≤ M * Real.exp (-rdot (l.1.re, l.2.re) t) *
      Real.exp (-ε * (|t.1| + |t.2|))) :
    Integrable (fun t : ℝ × ℝ => Complex.exp (dot l t) • φ t) ∧
      ‖∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t‖ ≤ M * (2 / ε) ^ 2 := by
  have hg1 := integrable_exp_neg_mul_abs hε
  have hgi : Integrable (fun t : ℝ × ℝ => M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|))) :=
    (hg1.mul_prod hg1).const_mul M
  have hbound : ∀ t : ℝ × ℝ, ‖Complex.exp (dot l t) • φ t‖ ≤
      M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|)) := by
    intro t
    rw [norm_smul, Complex.norm_exp]
    have hre : (dot l t).re = rdot (l.1.re, l.2.re) t := by simp [dot, rdot]
    rw [hre]
    have h1 : Real.exp (rdot (l.1.re, l.2.re) t) * Real.exp (-rdot (l.1.re, l.2.re) t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h2 : Real.exp (-ε * (|t.1| + |t.2|)) = Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|) := by
      rw [← Real.exp_add]; ring_nf
    calc Real.exp (rdot (l.1.re, l.2.re) t) * ‖φ t‖
        ≤ Real.exp (rdot (l.1.re, l.2.re) t) * (M * Real.exp (-rdot (l.1.re, l.2.re) t) *
          Real.exp (-ε * (|t.1| + |t.2|))) := mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos _).le
      _ = M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|)) := by
        rw [h2]
        linear_combination (M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|))) * h1
  have hc : Continuous (fun t : ℝ × ℝ => Complex.exp (dot l t) • φ t) := by
    have hd : Continuous (fun t : ℝ × ℝ => dot l t) := by simp only [dot]; fun_prop
    exact (Complex.continuous_exp.comp hd).smul hφ
  refine ⟨hgi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hbound), ?_⟩
  calc ‖∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t‖
      ≤ ∫ t : ℝ × ℝ, M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|)) :=
        norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall hbound)
    _ = M * (2 / ε) ^ 2 := by
        rw [integral_const_mul, Measure.volume_eq_prod,
          integral_prod_mul (fun u : ℝ => Real.exp (-ε * |u|)) (fun u : ℝ => Real.exp (-ε * |u|)),
          integral_exp_neg_mul_abs hε]
        ring

end GlobalTheory.CompanionTheory.TubeFourier
