import Mathlib

namespace GlobalTheory.DifferentiableDet

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
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
