import Mathlib

namespace GlobalTheory.IntegrableExpNegAbs

open MeasureTheory Set

/- English proof (translation)
Establish `h1 : IntegrableOn (fun s : ℝ ↦ Real.exp (-(c * |s|))) (Ioi 0) volume`. Use `(integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).congr_fun ?_ measurableSet_Ioi` and prove the remaining obligations. Introduce `x hx`. Establish `hx' : 0 < x` using `hx`. Simplify using `only [abs_of_pos hx', neg_mul]`.

Establish `h2 : IntegrableOn (fun s : ℝ ↦ Real.exp (-(c * |s|))) (Iic 0) volume`. Use `(integrableOn_exp_mul_Iic (a := c) hc 0).congr_fun ?_ measurableSet_Iic` and prove the remaining obligations. Introduce `x hx`. Establish `hx' : x ≤ 0` using `hx`. Simplify using `only [abs_of_nonpos hx', mul_neg, neg_neg]`.

Establish `h` using `h2.union h1`. Rewrite `h` using `[Iic_union_Ioi, integrableOn_univ]`. Then use the resulting hypothesis.
-/
theorem integrable_exp_neg_mul_abs {c : ℝ} (hc : (0 : ℝ) < c) :
    MeasureTheory.Integrable (fun (s : ℝ) ↦ Real.exp (-(c * |s|))) MeasureTheory.MeasureSpace.volume := by
  have h1 : IntegrableOn (fun s : ℝ ↦ Real.exp (-(c * |s|))) (Ioi 0) volume := by
    refine (integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := hx
    simp only [abs_of_pos hx', neg_mul]
  have h2 : IntegrableOn (fun s : ℝ ↦ Real.exp (-(c * |s|))) (Iic 0) volume := by
    refine (integrableOn_exp_mul_Iic (a := c) hc 0).congr_fun ?_ measurableSet_Iic
    intro x hx
    have hx' : x ≤ 0 := hx
    simp only [abs_of_nonpos hx', mul_neg, neg_neg]
  have h := h2.union h1
  rwa [Iic_union_Ioi, integrableOn_univ] at h

end GlobalTheory.IntegrableExpNegAbs
