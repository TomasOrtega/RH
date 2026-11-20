import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

variable {n : ℕ}

def logReg (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) : ℝ :=
  Real.log (‖linEval u x‖ ^ 2 + ε) / 2

/- English proof (translation)
Unfold `linEval`. Conclude with `ContDiff.sum fun j _ => contDiff_const.mul ((contDiff_apply ℝ ℂ j).restrict_scalars ℝ)`.
-/
theorem contDiff_linEval (u : Fin n → ℂ) : ContDiff ℝ ∞ (fun x : Fin n → ℂ => linEval u x) := by
  unfold linEval
  exact ContDiff.sum fun j _ => contDiff_const.mul ((contDiff_apply ℝ ℂ j).restrict_scalars ℝ)

/- English proof (translation)
Unfold `logReg`. Use `ContDiff.div_const (ContDiff.log (((contDiff_norm_sq ℝ).comp (contDiff_linEval u)).add contDiff_const) fun x => ?_) _` and prove the remaining obligations. Establish `: 0 ≤ ‖linEval u x‖ ^ 2` using `sq_nonneg _`. Simplify using `only [Function.comp_apply]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem contDiff_logReg (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (logReg u ε) := by
  unfold logReg
  refine ContDiff.div_const (ContDiff.log (((contDiff_norm_sq ℝ).comp (contDiff_linEval u)).add
    contDiff_const) fun x => ?_) _
  have : 0 ≤ ‖linEval u x‖ ^ 2 := sq_nonneg _
  simp only [Function.comp_apply]
  linarith

/- English proof (translation)
Unfold `logReg`. Rewrite using `[add_zero, Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logReg_zero (u : Fin n → ℂ) (x : Fin n → ℂ) :
    logReg u 0 x = Real.log ‖linEval u x‖ := by
  unfold logReg
  rw [add_zero, Real.log_pow]
  push_cast
  ring

def LelongRegularise.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    ContDiff ℝ ∞ f → HasCompactSupport f → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      Tendsto (fun ε => varInt J (d + 1) (logReg u ε) (vecCons f φ)) (𝓝[>] 0)
        (𝓝 (varInt J (d + 1) (fun x => Real.log ‖linEval u x‖) (vecCons f φ)))

end

end GroundTheory.Heights₂.Heights
