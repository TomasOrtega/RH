import Formalism.UnipotentAdelicQuotients.EllRegCut

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable def eL {d : ℕ} (ξ : E d) : E d →L[ℝ] ℂ :=
  (-(2 * (Real.pi : ℂ) * Complex.I)) • (Complex.ofRealCLM.comp (innerSL ℝ ξ))

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [eF, eL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul, real_inner_comm y ξ]`. Put the polynomial expressions in normal form.
-/
lemma eF_eq_exp {d : ℕ} (ξ : E d) : eF ξ = fun y => Complex.exp (eL ξ y) := by
  funext y
  simp only [eF, eL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul, real_inner_comm y ξ]
  ring_nf

/- English proof (translation)
Rewrite using `[eF_eq_exp]`. Conclude with `(eL ξ).hasFDerivAt.cexp`.
-/
lemma hasFDerivAt_eF {d : ℕ} (ξ y : E d) :
    HasFDerivAt (eF ξ) (Complex.exp (eL ξ y) • eL ξ) y := by
  rw [eF_eq_exp]
  exact (eL ξ).hasFDerivAt.cexp

/- English proof (translation)
Simplify using `only [eL, ev, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul, EuclideanSpace.inner_single_right]`. Simplify using the standard rewrite rules.
-/
lemma eL_ev {d : ℕ} (ξ : E d) (j : Fin d) : eL ξ (ev j) = -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ)) := by
  simp only [eL, ev, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul, EuclideanSpace.inner_single_right]
  simp

/- English proof (translation)
Introduce `d ξ w`. Proceed by induction on `w with`. Consider the case `nil => funext y`. Simplify using `[dw]`. Consider the case `cons j w ih`.

Use function extensionality and compare the values at `x`. Establish `hfun : dw w (eF ξ) = fun y => (w.map fun j => -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))).prod * eF ξ y` using `ih`. Use `show fderiv ℝ (dw w (eF ξ)) x (ev j) = _`. Rewrite using `[hfun, ((hasFDerivAt_eF ξ x).const_mul _).fderiv]`. Simplify using `only [ContinuousLinearMap.smul_apply, smul_eq_mul, eL_ev, List.map_cons, List.prod_cons, eF_eq_exp]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem iteratedPartialFourierChar : DwExp := by
  intro d ξ w
  induction w with
  | nil => funext y; simp [dw]
  | cons j w ih =>
    funext x
    have hfun : dw w (eF ξ) =
        fun y => (w.map fun j => -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))).prod * eF ξ y := ih
    show fderiv ℝ (dw w (eF ξ)) x (ev j) = _
    rw [hfun, ((hasFDerivAt_eF ξ x).const_mul _).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, eL_ev, List.map_cons, List.prod_cons,
      eF_eq_exp]
    ring

end ZetaZeros.D.EllReg
