import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

/- English proof (translation)
Simplify using `using integrable_exp_neg_mul_sq (b := 1) one_pos`.
-/
theorem integrable_gauss_one : Integrable (fun s : ℝ => Real.exp (-s ^ 2)) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

/- English proof (translation)
Simplify using `using integral_gaussian 1`.
-/
theorem integral_gauss_one : ∫ s : ℝ, Real.exp (-s ^ 2) = Real.sqrt Real.pi := by
  simpa using integral_gaussian 1

/- English proof (translation)
The claim follows from `Integrable.mul_prod integrable_gauss_one integrable_gauss_one`.
-/
theorem integrable_gauss_prod :
    Integrable (fun y : ℝ × ℝ => Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) :=
  Integrable.mul_prod integrable_gauss_one integrable_gauss_one

/- English proof (translation)
Rewrite using `[Measure.volume_eq_prod, integral_prod_mul (fun s : ℝ => Real.exp (-s ^ 2)) (fun s : ℝ => Real.exp (-s ^ 2)), integral_gauss_one, Real.mul_self_sqrt Real.pi_pos.le]`.
-/
theorem integral_gauss_prod :
    ∫ y : ℝ × ℝ, Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2) = Real.pi := by
  rw [Measure.volume_eq_prod, integral_prod_mul (fun s : ℝ => Real.exp (-s ^ 2)) (fun s : ℝ => Real.exp (-s ^ 2)),
    integral_gauss_one, Real.mul_self_sqrt Real.pi_pos.le]

/- English proof (translation)
Simplify using `[dot, pt, rdot, Complex.mul_re]`.
-/
theorem re_dot_pt (x y t : ℝ × ℝ) : (dot (pt x y) t).re = rdot x t := by
  simp [dot, pt, rdot, Complex.mul_re]

/- English proof (translation)
Introduce `X _ _ G x M hG t`. Establish `hb : ∀ y : ℝ × ℝ, ‖Complex.exp (-dot (pt x y) t) • G (pt x y)‖ ≤ M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2))`. Introduce `y`. Rewrite using `[norm_smul, Complex.norm_exp, Complex.neg_re, re_dot_pt]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[neg_add, Real.exp_add]`. Expand and normalize the polynomial expressions, which then agree. Unfold `phi`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[integral_const_mul, integral_gauss_prod]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_phi_le : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (G : ℂ × ℂ → X) (x : ℝ × ℝ) (M : ℝ),
    (∀ y : ℝ × ℝ, ‖G (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) →
    ∀ t : ℝ × ℝ, ‖phi G x t‖ ≤ M * Real.pi * Real.exp (-rdot x t) := by
  intro X _ _ G x M hG t
  have hb : ∀ y : ℝ × ℝ, ‖Complex.exp (-dot (pt x y) t) • G (pt x y)‖ ≤
      M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
    intro y
    rw [norm_smul, Complex.norm_exp, Complex.neg_re, re_dot_pt]
    calc Real.exp (-rdot x t) * ‖G (pt x y)‖
        ≤ Real.exp (-rdot x t) * (M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) :=
          mul_le_mul_of_nonneg_left (hG y) (Real.exp_pos _).le
      _ = M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
          rw [neg_add, Real.exp_add]; ring
  unfold phi
  calc ‖∫ y : ℝ × ℝ, Complex.exp (-dot (pt x y) t) • G (pt x y)‖
      ≤ ∫ y : ℝ × ℝ, M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) :=
        norm_integral_le_of_norm_le (Integrable.const_mul integrable_gauss_prod _) (Eventually.of_forall hb)
    _ = M * Real.pi * Real.exp (-rdot x t) := by
        rw [integral_const_mul, integral_gauss_prod]; ring

end GlobalTheory.CompanionTheory.TubeFourier
