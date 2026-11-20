import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BesselDerivatives.ContDiffOnDirectionalDerivative
import Formalism.PeriodIntegrals.BesselDeriv

open scoped ContDiff Topology
open Matrix

noncomputable section

namespace PI.BesselDerivW

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
/- English proof (translation)
Establish `hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) (NormedSpace.exp ((t : ℂ) • X) * X) t`. Introduce `t`. Establish `e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) = fun u : ℝ => NormedSpace.exp (u • X)`. Use function extensionality and compare the values at `t`. Rewrite using `[Complex.coe_smul]`.

Rewrite using `[e, Complex.coe_smul]`. Conclude with `hasDerivAt_exp_smul_const (𝕂 := ℝ) X t`. Use `set f := fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) with hf`. Establish `hdiff : Differentiable ℝ f` using `fun t => (hd t).differentiableAt`. Establish `hder : deriv f = fun t => f t * X` using `funext fun t => (hd t).deriv`.

Establish `hcd : ∀ m : ℕ, ContDiff ℝ m f`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => exact (contDiff_zero.2 hdiff.continuous).of_le (by simp)`. Consider the case `succ m ih`.

Establish `h' : ContDiff ℝ m (deriv f)` using `by rw [hder]; exact ih.mul contDiff_const`. Establish `h1 : ContDiff ℝ ((m : WithTop ℕ∞) + 1) f` using `by first`. Consider the case `exact contDiff_succ_iff_deriv.2 ⟨hdiff, by simp, h'⟩`. Consider the case `exact contDiff_succ_iff_deriv.2 ⟨hdiff, h'⟩`. Conclude with `h1.of_le (by norm_num)`.

Establish `hcf : ContDiff ℝ ∞ f` using `contDiff_infty.2 hcd`. Set `L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ` to `{ toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Conclude with `(LinearMap.toContinuousLinearMap L).contDiff.comp hcf`.
-/
theorem exp_entry_contDiff (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ContDiff ℝ ∞ (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X))
      (NormedSpace.exp ((t : ℂ) • X) * X) t := by
    intro t
    have e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) = fun u : ℝ => NormedSpace.exp (u • X) := by
      funext t; rw [Complex.coe_smul]
    rw [e, Complex.coe_smul]
    exact hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
  set f := fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) with hf
  have hdiff : Differentiable ℝ f := fun t => (hd t).differentiableAt
  have hder : deriv f = fun t => f t * X := funext fun t => (hd t).deriv
  have hcd : ∀ m : ℕ, ContDiff ℝ m f := by
    intro m
    induction m with
    | zero => exact (contDiff_zero.2 hdiff.continuous).of_le (by simp)
    | succ m ih =>
      have h' : ContDiff ℝ m (deriv f) := by rw [hder]; exact ih.mul contDiff_const
      have h1 : ContDiff ℝ ((m : WithTop ℕ∞) + 1) f := by
        first
        | exact contDiff_succ_iff_deriv.2 ⟨hdiff, by simp, h'⟩
        | exact contDiff_succ_iff_deriv.2 ⟨hdiff, h'⟩
      exact h1.of_le (by norm_num)
  have hcf : ContDiff ℝ ∞ f := contDiff_infty.2 hcd
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).contDiff.comp hcf

/- English proof (translation)
Use `contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_` and prove the remaining obligations. Conclude with `exp_entry_contDiff X i j`.
-/
theorem exp_contDiff (X : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  exact exp_entry_contDiff X i j

def mulRc (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

def mulLc (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)

end PI.BesselDerivW
