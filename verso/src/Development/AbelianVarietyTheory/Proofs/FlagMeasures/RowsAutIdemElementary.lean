import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory

/- English proof (translation)
Introduce `B`. Take `⟨hlc, -, hstar, hpos, -⟩` from `B.e_adm`. Establish `him : (B.e 1).im = 0`. Establish `h` using `congrArg Complex.im (hstar 1)`. Rewrite `h` using `[inv_one, Complex.star_def, Complex.conj_im]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hre : 0 ≤ (B.e 1).re`. Establish `h` using `hpos 1 (fun _ => 1) (fun _ => 1)`. Simplify using `only [Fin.sum_univ_one, star_one, one_mul, inv_one] at h`. Conclude with `(Complex.nonneg_iff.mp h).1`.

Use `⟨him, hre, ?_, hlc.continuous⟩` and prove the remaining obligations. Introduce `y`. Use `set a := (B.e 1).re with ha`. Establish `h1 : B.e 1 = (a : ℂ)` using `Complex.ext (by simp [ha]) (by simp [him])`. Use `set b := B.e y with hb`.

Establish `hyi : B.e y⁻¹ = star b` using `hstar y`. Establish `key : star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hs : star ((‖b‖ : ℝ) : ℂ) = ((‖b‖ : ℝ) : ℂ)` using `Complex.conj_ofReal _`. Establish `h` using `hpos 2 ![1, y] ![b, -((‖b‖ : ℝ) : ℂ)]`. Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, inv_one, one_mul, mul_one, inv_mul_cancel, hyi, h1, star_neg, hs] at h`. Establish `hE : star b * b * (a : ℂ) + star b * -((‖b‖ : ℝ) : ℂ) * b + (-((‖b‖ : ℝ) : ℂ) * b * star b + -((‖b‖ : ℝ) : ℂ) * -((‖b‖ : ℝ) : ℂ) * (a : ℂ)) = ((2 * ‖b‖ ^ 2 * (a - ‖b‖) : ℝ) : ℂ)`. Move the coercions through the operations in `at key ⊢`.

Take the linear combination `((a : ℂ) - 2 * ((‖b‖ : ℝ) : ℂ)) * key`. Rewrite `h` using `[hE, Complex.zero_le_real]`. Use `le_of_not_gt fun hlt => ?_` and prove the remaining obligations. Establish `hb0 : 0 < ‖b‖` using `lt_of_le_of_lt hre hlt`. Establish `hneg : 2 * ‖b‖ ^ 2 * (a - ‖b‖) < 0` using `mul_neg_of_pos_of_neg (by positivity) (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rowsAut_idem_elementary : ∀ B : RowsAut,
    (B.e 1).im = 0 ∧ 0 ≤ (B.e 1).re ∧ (∀ y, ‖B.e y‖ ≤ (B.e 1).re) ∧ Continuous B.e := by
  intro B
  obtain ⟨hlc, -, hstar, hpos, -⟩ := B.e_adm

  have him : (B.e 1).im = 0 := by
    have h := congrArg Complex.im (hstar 1)
    rw [inv_one, Complex.star_def, Complex.conj_im] at h
    linarith

  have hre : 0 ≤ (B.e 1).re := by
    have h := hpos 1 (fun _ => 1) (fun _ => 1)
    simp only [Fin.sum_univ_one, star_one, one_mul, inv_one] at h
    exact (Complex.nonneg_iff.mp h).1
  refine ⟨him, hre, ?_, hlc.continuous⟩
  intro y
  set a := (B.e 1).re with ha
  have h1 : B.e 1 = (a : ℂ) := Complex.ext (by simp [ha]) (by simp [him])
  set b := B.e y with hb
  have hyi : B.e y⁻¹ = star b := hstar y
  have key : star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have hs : star ((‖b‖ : ℝ) : ℂ) = ((‖b‖ : ℝ) : ℂ) := Complex.conj_ofReal _

  have h := hpos 2 ![1, y] ![b, -((‖b‖ : ℝ) : ℂ)]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    inv_one, one_mul, mul_one, inv_mul_cancel, hyi, h1, star_neg, hs] at h
  have hE : star b * b * (a : ℂ) + star b * -((‖b‖ : ℝ) : ℂ) * b +
      (-((‖b‖ : ℝ) : ℂ) * b * star b + -((‖b‖ : ℝ) : ℂ) * -((‖b‖ : ℝ) : ℂ) * (a : ℂ)) =
      ((2 * ‖b‖ ^ 2 * (a - ‖b‖) : ℝ) : ℂ) := by
    push_cast at key ⊢
    linear_combination ((a : ℂ) - 2 * ((‖b‖ : ℝ) : ℂ)) * key
  rw [hE, Complex.zero_le_real] at h
  refine le_of_not_gt fun hlt => ?_
  have hb0 : 0 < ‖b‖ := lt_of_le_of_lt hre hlt
  have hneg : 2 * ‖b‖ ^ 2 * (a - ‖b‖) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
  linarith

end GlobalTheory
