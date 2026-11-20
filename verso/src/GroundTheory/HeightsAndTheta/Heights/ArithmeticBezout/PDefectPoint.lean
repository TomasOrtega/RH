import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/- English proof (translation)
Establish `hw : ∀ j : Fin n, groupWeight 1 n ((0 : Fin 1), j) = fun _ => 1`. Introduce `j`. Use function extensionality and compare the values at `i`. Rewrite using `[Fin.fin_one_eq_zero i]`. Simplify using `[groupWeight]`.

Establish `hsum : IsWeightedHomogeneous (groupWeight 1 n) (∑ j, C (y j) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin n) ℂ) (fun _ => 1)`. Rewrite using `[← mem_weightedHomogeneousSubmodule]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mem_weightedHomogeneousSubmodule]`. Establish `hX` using `isWeightedHomogeneous_X ℂ (groupWeight 1 n) ((0 : Fin 1), j)`.

Rewrite `hX` using `[hw j]`. Simplify `(isWeightedHomogeneous_C (groupWeight 1 n) (y j)).mul hX` using `[zero_add]`. Unfold `IsMultiHomog`. Simplify `(isWeightedHomogeneous_C (groupWeight 1 n) c).mul hsum` using `[zero_add]`.
-/
theorem isMultiHomog_pointForm (c : ℂ) (y : Fin n → ℂ) :
    IsMultiHomog 1 (C c * ∑ j, C (y j) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin n) ℂ) := by
  have hw : ∀ j : Fin n, groupWeight 1 n ((0 : Fin 1), j) = fun _ => 1 := by
    intro j
    funext i
    rw [Fin.fin_one_eq_zero i]
    simp [groupWeight]
  have hsum : IsWeightedHomogeneous (groupWeight 1 n)
      (∑ j, C (y j) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin n) ℂ) (fun _ => 1) := by
    rw [← mem_weightedHomogeneousSubmodule]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [mem_weightedHomogeneousSubmodule]
    have hX := isWeightedHomogeneous_X ℂ (groupWeight 1 n) ((0 : Fin 1), j)
    rw [hw j] at hX
    simpa [zero_add] using (isWeightedHomogeneous_C (groupWeight 1 n) (y j)).mul hX
  unfold IsMultiHomog
  simpa [zero_add] using (isWeightedHomogeneous_C (groupWeight 1 n) c).mul hsum

/- English proof (translation)
Introduce `n h W g hW hg`. Take `⟨y, hy0, hline, hmem⟩` from `h1 n W g hW hg`. Take `⟨c, hc, hgeq⟩` from `h2 n W g y hg hy0 hline`. Establish `hmass : coneIntegral h W 0 (fun _ => 1) = 1`. Use `h5 n 0 1 h W g hW hg (hgeq ▸ isMultiHomog_pointForm c y)` as an intermediate fact.

Simplify using `using this`. Establish `hd : 0 < h.dualNorm y` using `h.dualNorm_pos hy0`. Use `⟨Real.log ‖c‖ + Real.log (h.dualNorm y), fun u hu => ?_⟩` and prove the remaining obligations. Establish `hpair : ∑ j, u j * y j ≠ 0`. Introduce `h0`.

Apply `hu` to reduce the goal to its premises. Rewrite using `[hmem]`. Introduce `t`. Simplify using `only [linForm, map_sum, map_mul, eval_C, eval_X, Pi.smul_apply, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring`. Use `_ = 0 := by rw [h0, mul_zero]`. Establish `hev : eval (fun ij => u ij.2) g = c * ∑ j, u j * y j`. Rewrite using `[hgeq]`. Simplify using `only [map_mul, map_sum, eval_C, eval_X]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Establish `hcone : coneIntegral h W 0 (fsLog h u) = fsLog h u y`. Rewrite using `[h3 n h W y hline (fsLog h u) (fun t ht => h4 n h u y t ht), hmass, mul_one]`. Use `⟨by rw [hev]; exact mul_ne_zero hc hpair, ?_⟩` and prove the remaining obligations.

Rewrite using `[hev, hcone, fsLog, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hpair), Real.log_div (norm_ne_zero_iff.mpr hpair) hd.ne']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem DefectPoint.proof (h1 : PointLine.Statement) (h2 : PointChowForm.Statement)
    (h3 : ConeIntegralLine.Statement) (h4 : FsLogSmul.Statement) (h5 : ConeIntegralMass.Statement) :
    DefectPoint.Statement := by
  intro n h W g hW hg
  obtain ⟨y, hy0, hline, hmem⟩ := h1 n W g hW hg
  obtain ⟨c, hc, hgeq⟩ := h2 n W g y hg hy0 hline
  have hmass : coneIntegral h W 0 (fun _ => 1) = 1 := by
    have := h5 n 0 1 h W g hW hg (hgeq ▸ isMultiHomog_pointForm c y)
    simpa using this
  have hd : 0 < h.dualNorm y := h.dualNorm_pos hy0
  refine ⟨Real.log ‖c‖ + Real.log (h.dualNorm y), fun u hu => ?_⟩
  have hpair : ∑ j, u j * y j ≠ 0 := by
    intro h0
    apply hu
    rw [hmem]
    intro t
    simp only [linForm, map_sum, map_mul, eval_C, eval_X, Pi.smul_apply, smul_eq_mul]
    calc ∑ j, u j * (t * y j) = t * ∑ j, u j * y j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h0, mul_zero]
  have hev : eval (fun ij => u ij.2) g = c * ∑ j, u j * y j := by
    rw [hgeq]
    simp only [map_mul, map_sum, eval_C, eval_X]
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hcone : coneIntegral h W 0 (fsLog h u) = fsLog h u y := by
    rw [h3 n h W y hline (fsLog h u) (fun t ht => h4 n h u y t ht), hmass, mul_one]
  refine ⟨by rw [hev]; exact mul_ne_zero hc hpair, ?_⟩
  rw [hev, hcone, fsLog, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hpair),
    Real.log_div (norm_ne_zero_iff.mpr hpair) hd.ne']
  ring

end

end GroundTheory.Heights₂.Heights
