import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Establish `hg0 : g 0 ≠ 0`. Introduce `h0`. Apply `hg` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[hform x, h0]`.

Simplify using the standard rewrite rules. Assume the negation of the conclusion as `hre`. Use `push_neg at hre`. Take `⟨C, hC, hdec⟩` from `g.decay 1 0`. Establish `hgn : 0 < ‖g 0‖` using `norm_pos_iff.mpr hg0`.

Establish `hvn : 0 < ‖v‖` using `norm_pos_iff.mpr hv`. Use `set s : ℝ := (C + 1) / (‖v‖ * ‖g 0‖) with hs`. Establish `hspos : 0 < s` using `by positivity`. Establish `key` using `hdec (s • v)`. Rewrite `key` using `[norm_iteratedFDeriv_zero, pow_one, hform (s • v)]`.

Establish `hM : M (s • v) (s • v) = ((s ^ 2 : ℝ) : ℂ) * M v v`. Simplify using `only [map_smul, LinearMap.smul_apply, smul_smul]`. Rewrite using `[Complex.real_smul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `key` using `[hM, norm_mul, Complex.norm_exp]`. Establish `hexp : 1 ≤ Real.exp ((((s ^ 2 : ℝ) : ℂ) * M v v).re)`. Apply `Real.one_le_exp` to reduce the goal to its premises. Rewrite using `[Complex.re_ofReal_mul]`. Check the signs of the components of the expression.

Establish `hnorm : ‖s • v‖ = s * ‖v‖`. Rewrite using `[norm_smul, Real.norm_eq_abs, abs_of_pos hspos]`. Rewrite `key` using `[hnorm]`. Establish `h1 : s * ‖v‖ * ‖g 0‖ = C + 1`. Rewrite using `[hs]`.

Clear the denominators using the available nonvanishing facts. Establish `h2 : s * ‖v‖ * ‖g 0‖ ≤ s * ‖v‖ * (‖g 0‖ * Real.exp ((((s ^ 2 : ℝ) : ℂ) * M v v).re))`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem schwartz_gaussian_form_re_neg {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (M : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (g : SchwartzMap V ℂ) (hg : g ≠ 0)
    (hform : ∀ x, g x = g 0 * Complex.exp (M x x)) (v : V) (hv : v ≠ 0) : (M v v).re < 0 := by
  have hg0 : g 0 ≠ 0 := by
    intro h0
    apply hg
    ext x
    rw [hform x, h0]; simp
  by_contra hre
  push_neg at hre
  obtain ⟨C, hC, hdec⟩ := g.decay 1 0
  have hgn : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set s : ℝ := (C + 1) / (‖v‖ * ‖g 0‖) with hs
  have hspos : 0 < s := by positivity
  have key := hdec (s • v)
  rw [norm_iteratedFDeriv_zero, pow_one, hform (s • v)] at key
  have hM : M (s • v) (s • v) = ((s ^ 2 : ℝ) : ℂ) * M v v := by
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rw [Complex.real_smul]; push_cast; ring
  rw [hM, norm_mul, Complex.norm_exp] at key
  have hexp : 1 ≤ Real.exp ((((s ^ 2 : ℝ) : ℂ) * M v v).re) := by
    apply Real.one_le_exp
    rw [Complex.re_ofReal_mul]
    positivity
  have hnorm : ‖s • v‖ = s * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
  rw [hnorm] at key
  have h1 : s * ‖v‖ * ‖g 0‖ = C + 1 := by
    rw [hs]; field_simp
  have h2 : s * ‖v‖ * ‖g 0‖ ≤ s * ‖v‖ * (‖g 0‖ * Real.exp ((((s ^ 2 : ℝ) : ℂ) * M v v).re)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  linarith

end GlobalTheory
