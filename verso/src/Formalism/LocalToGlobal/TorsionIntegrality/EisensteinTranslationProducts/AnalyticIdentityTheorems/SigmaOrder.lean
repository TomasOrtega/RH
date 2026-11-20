import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine

noncomputable section

namespace Formalism.L2.Th1.F

/- English proof (translation)
Introduce `L a b z ha`. Use `set f : ℂ → ℂ := fun w => wSigma L (a * w + b) with hfdef`. Establish `hlin : Differentiable ℂ (fun w : ℂ => a * w + b)` using `(differentiable_id.const_mul a).add_const b`. Establish `hfd : Differentiable ℂ f` using `(he L).comp hlin`. Establish `hfa : AnalyticAt ℂ f z` using `hfd.analyticAt z`.

Establish `hder : HasDerivAt f (deriv (wSigma L) (a * z + b) * (a * 1)) z`. Establish `h1 : HasDerivAt (fun w : ℂ => a * w + b) (a * 1) z` using `((hasDerivAt_id z).const_mul a).add_const b`. Conclude with `((he L) (a * z + b)).hasDerivAt.comp z h1`. Rewrite using `[hfa.meromorphicOrderAt_eq]`. Use `split_ifs with hmem`.

Establish `h0 : f z = 0` using `(hz L (a * z + b)).2 hmem`. Establish `hord : analyticOrderAt f z = ((1 : ℕ) : ℕ∞)`. Rewrite using `[hfa.analyticOrderAt_eq_natCast]`. Use `⟨dslope f z, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hon : DifferentiableOn ℂ (dslope f z) Set.univ` using `(Complex.differentiableOn_dslope Filter.univ_mem).2 hfd.differentiableOn`.

Conclude with `(differentiableOn_univ.1 hon).analyticAt z`. Rewrite using `[dslope_same, hder.deriv]`. Conclude with `mul_ne_zero ((hs L).2 _ hmem) (by simpa using ha)`. Use `filter_upwards with w`. Rewrite using `[pow_one, sub_smul_dslope, h0, sub_zero]`.

Rewrite using `[hord]`. Both sides reduce to the same expression. Establish `hne : f z ≠ 0` using `fun h => hmem ((hz L (a * z + b)).1 h)`. Establish `hord : analyticOrderAt f z = 0` using `analyticOrderAt_eq_zero.2 (Or.inr hne)`. Rewrite using `[hord]`.

Both sides reduce to the same expression.
-/
theorem sigmaOrder_of (he : SigmaEntire) (hz : SigmaZero) (hs : SigmaSimple) : SigmaOrder := by
  intro L a b z ha
  classical
  set f : ℂ → ℂ := fun w => wSigma L (a * w + b) with hfdef
  have hlin : Differentiable ℂ (fun w : ℂ => a * w + b) :=
    (differentiable_id.const_mul a).add_const b
  have hfd : Differentiable ℂ f := (he L).comp hlin
  have hfa : AnalyticAt ℂ f z := hfd.analyticAt z
  have hder : HasDerivAt f (deriv (wSigma L) (a * z + b) * (a * 1)) z := by
    have h1 : HasDerivAt (fun w : ℂ => a * w + b) (a * 1) z :=
      ((hasDerivAt_id z).const_mul a).add_const b
    exact ((he L) (a * z + b)).hasDerivAt.comp z h1
  rw [hfa.meromorphicOrderAt_eq]
  split_ifs with hmem
  · have h0 : f z = 0 := (hz L (a * z + b)).2 hmem
    have hord : analyticOrderAt f z = ((1 : ℕ) : ℕ∞) := by
      rw [hfa.analyticOrderAt_eq_natCast]
      refine ⟨dslope f z, ?_, ?_, ?_⟩
      · have hon : DifferentiableOn ℂ (dslope f z) Set.univ :=
          (Complex.differentiableOn_dslope Filter.univ_mem).2 hfd.differentiableOn
        exact (differentiableOn_univ.1 hon).analyticAt z
      · rw [dslope_same, hder.deriv]
        exact mul_ne_zero ((hs L).2 _ hmem) (by simpa using ha)
      · filter_upwards with w
        rw [pow_one, sub_smul_dslope, h0, sub_zero]
    rw [hord]
    rfl
  · have hne : f z ≠ 0 := fun h => hmem ((hz L (a * z + b)).1 h)
    have hord : analyticOrderAt f z = 0 := analyticOrderAt_eq_zero.2 (Or.inr hne)
    rw [hord]
    rfl

end Formalism.L2.Th1.F
