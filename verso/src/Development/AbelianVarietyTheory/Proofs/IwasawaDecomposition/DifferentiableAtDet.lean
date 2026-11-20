import Mathlib

namespace GlobalTheory.DifferentiableDet

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Use `DifferentiableAt.fun_sum fun π _ => ?_` and prove the remaining obligations. Use `DifferentiableAt.const_mul ?_ _` and prove the remaining obligations. Conclude with `(HasDerivAt.fun_finset_prod (u := Finset.univ) (f := fun i s => M s (π i) i) (fun i _ => (h (π i) i).hasDerivAt)).differentiableAt`.
-/
theorem differentiableAt_det {σ : Type} [Fintype σ] [DecidableEq σ] (M : ℝ → Matrix σ σ ℂ) (t : ℝ)
    (h : ∀ (i j : σ), DifferentiableAt ℝ (fun (s : ℝ) ↦ M s i j) t) :
    DifferentiableAt ℝ (fun (s : ℝ) ↦ Matrix.det (M s)) t := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun π _ => ?_
  refine DifferentiableAt.const_mul ?_ _
  exact (HasDerivAt.fun_finset_prod (u := Finset.univ) (f := fun i s => M s (π i) i)
    (fun i _ => (h (π i) i).hasDerivAt)).differentiableAt

end GlobalTheory.DifferentiableDet
