import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open scoped InnerProductSpace ComplexConjugate Matrix

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;>`. Simplify using `[blochVector, pauli, Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma blochVector_apply (e : EuclideanSpace ℂ (Fin 2)) :
    blochVector e 0 = 2 * ((e 0).re * (e 1).re + (e 0).im * (e 1).im) ∧
    blochVector e 1 = 2 * ((e 0).re * (e 1).im - (e 0).im * (e 1).re) ∧
    blochVector e 2 = (e 0).re ^ 2 + (e 0).im ^ 2 - (e 1).re ^ 2 - (e 1).im ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp [blochVector, pauli, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma norm_sq_complex_two_re_im (e : EuclideanSpace ℂ (Fin 2)) :
    ‖e‖ ^ 2 = (e 0).re ^ 2 + (e 0).im ^ 2 + (e 1).re ^ 2 + (e 1).im ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  ring

/- English proof (translation)
Use `⟨fun e he => ?_, fun e₁ e₂ h₁ h₂ => ?_⟩` and prove the remaining obligations. Establish `hs` using `norm_sq_complex_two_re_im e`. Rewrite `hs` using `[he]`. Take `⟨h0, h1, h2⟩` from `blochVector_apply e`. Establish `hn : ‖blochVector e‖ ^ 2 = 1`.

Rewrite using `[EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, sq_abs, h0, h1, h2]`. Take the linear combination `(-(1 : ℝ) - ((e 0).re ^ 2 + (e 0).im ^ 2 + (e 1).re ^ 2 + (e 1).im ^ 2)) * hs`. Establish `h0' : 0 ≤ ‖blochVector e‖` using `norm_nonneg _`. Use polynomial arithmetic with `[hn]`. Establish `hs₁` using `norm_sq_complex_two_re_im e₁`.

Establish `hs₂` using `norm_sq_complex_two_re_im e₂`. Rewrite `hs₁` using `[h₁]`. Rewrite `hs₂` using `[h₂]`. Take `⟨a0, a1, a2⟩` from `blochVector_apply e₁`. Take `⟨b0, b1, b2⟩` from `blochVector_apply e₂`.

Rewrite using `[PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]`. Simplify using `only [RCLike.inner_apply, conj_trivial, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, a0, a1, a2, b0, b1, b2]`. Take the linear combination `(-(1 : ℝ) / 2) * (((e₂ 0).re ^ 2 + (e₂ 0).im ^ 2 + (e₂ 1).re ^ 2 + (e₂ 1).im ^ 2) * hs₁ + hs₂)`.
-/
theorem BlochOverlap.proof : BlochOverlap.Statement := by
  refine ⟨fun e he => ?_, fun e₁ e₂ h₁ h₂ => ?_⟩
  · have hs := norm_sq_complex_two_re_im e
    rw [he] at hs
    obtain ⟨h0, h1, h2⟩ := blochVector_apply e
    have hn : ‖blochVector e‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, sq_abs, sq_abs, sq_abs, h0, h1, h2]
      linear_combination (-(1 : ℝ) - ((e 0).re ^ 2 + (e 0).im ^ 2 + (e 1).re ^ 2 + (e 1).im ^ 2)) * hs
    have h0' : 0 ≤ ‖blochVector e‖ := norm_nonneg _
    nlinarith [hn]
  · have hs₁ := norm_sq_complex_two_re_im e₁
    have hs₂ := norm_sq_complex_two_re_im e₂
    rw [h₁] at hs₁
    rw [h₂] at hs₂
    obtain ⟨a0, a1, a2⟩ := blochVector_apply e₁
    obtain ⟨b0, b1, b2⟩ := blochVector_apply e₂
    rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two,
      Complex.sq_norm, Complex.normSq_apply]
    simp only [RCLike.inner_apply, conj_trivial, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, a0, a1, a2, b0, b1, b2]
    linear_combination (-(1 : ℝ) / 2) * (((e₂ 0).re ^ 2 + (e₂ 0).im ^ 2 + (e₂ 1).re ^ 2 + (e₂ 1).im ^ 2) * hs₁ + hs₂)

end GroundTheory.Heights₂.Heights.FlagBundles
