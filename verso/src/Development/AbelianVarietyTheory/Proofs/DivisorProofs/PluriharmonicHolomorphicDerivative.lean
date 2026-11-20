import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory

/- English proof (translation)
Introduce `V _ _ f hf hh a z`. Establish `hf1 : ContDiff ℝ ∞ (fderiv ℝ f)` using `hf.fderiv_right (by simp)`. Establish `hf2 : Differentiable ℝ (fderiv ℝ f)` using `hf1.differentiable (by simp)`. Use `set B := fderiv ℝ (fderiv ℝ f) z with hB`. Establish `hsym : ∀ x y, B x y = B y x` using `fun x y => (hf.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.mpr le_top)) x y`.

Establish `hdc : ∀ c : V, DifferentiableAt ℝ (fun y => fderiv ℝ f y c) z` using `fun c => (hf2 z).clm_apply (differentiableAt_const c)`. Establish `hS : ∀ c x, fderiv ℝ (fun y => fderiv ℝ f y c) z x = B x c`. Introduce `c x`. Rewrite using `[fderiv_clm_apply (hf2 z) (differentiableAt_const c)]`. Simplify using `[hB]`.

Establish `hH : ∀ a w : V, B w (Complex.I • a) = B a (Complex.I • w)`. Introduce `a w`. Use `hh z a w` as an intermediate fact. Rewrite `this` using `[hS, hS]`. Then use the resulting hypothesis. Use `set D : V →L[ℝ] ℂ := Complex.ofRealCLM.comp (fderiv ℝ (fun y => fderiv ℝ f y a) z) - Complex.I • Complex.ofRealCLM.comp (fderiv ℝ (fun y => fderiv ℝ f y (Complex.I • a)) z) with hD`.

Establish `hder : HasFDerivAt (fun z => ((fderiv ℝ f z a : ℝ) : ℂ) - Complex.I * ((fderiv ℝ f z (Complex.I • a) : ℝ) : ℂ)) D z`. Establish `h1` using `Complex.ofRealCLM.hasFDerivAt.comp z (hdc a).hasFDerivAt`. Establish `h2` using `(Complex.ofRealCLM.hasFDerivAt.comp z (hdc (Complex.I • a)).hasFDerivAt).const_mul Complex.I`. Conclude with `h1.sub h2`. Establish `hDval : ∀ w, D w = ((B w a : ℝ) : ℂ) - Complex.I * ((B w (Complex.I • a) : ℝ) : ℂ)`.

Introduce `w`. Simplify using `[hD, hS]`. Establish `hDI : ∀ w, D (Complex.I • w) = Complex.I * D w`. Introduce `w`. Establish `e1 : B (Complex.I • w) a = B w (Complex.I • a)` using `by rw [hsym, hH]`.

Establish `e2 : B (Complex.I • w) (Complex.I • a) = - B w a`. Rewrite using `[hH, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg, hsym]`. Rewrite using `[hDval, hDval, e1, e2]`. Use `push_cast`. Take the linear combination `((B w (Complex.I • a) : ℝ) : ℂ) * Complex.I_sq`.

Set `L : V →L[ℂ] ℂ` to `{ toFun := fun w => D w map_add' := fun x y => D.map_add x y map_smul' := by`. Introduce `c w`. Simplify using `only [RingHom.id_apply, smul_eq_mul]`. Establish `hc : c • w = c.re • w + c.im • (Complex.I • w)` using `by conv_lhs => rw [← Complex.re_add_im c]`. Rewrite using `[add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]`.

Rewrite using `[hc, D.map_add, D.map_smul, D.map_smul, hDI, Complex.real_smul, Complex.real_smul]`. Use `conv_rhs => rw [← Complex.re_add_im c]`. Expand and normalize the polynomial expressions, which then agree. Use `cont := D.continuous }`. Establish `hL : L.restrictScalars ℝ = D` using `by ext w; rfl`.

Conclude with `(hasFDerivAt_of_restrictScalars ℝ hder hL).differentiableAt`.
-/
theorem pluriharmonic_dz_differentiable : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : V → ℝ), ContDiff ℝ ∞ f →
    (∀ z a w : V, fderiv ℝ (fun y => fderiv ℝ f y (Complex.I • a)) z w =
      fderiv ℝ (fun y => fderiv ℝ f y (Complex.I • w)) z a) →
    ∀ a : V, Differentiable ℂ (fun z => ((fderiv ℝ f z a : ℝ) : ℂ) -
      Complex.I * ((fderiv ℝ f z (Complex.I • a) : ℝ) : ℂ)) := by
  intro V _ _ f hf hh a z
  have hf1 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hf2 : Differentiable ℝ (fderiv ℝ f) := hf1.differentiable (by simp)
  set B := fderiv ℝ (fderiv ℝ f) z with hB
  have hsym : ∀ x y, B x y = B y x := fun x y =>
    (hf.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.mpr le_top)) x y
  have hdc : ∀ c : V, DifferentiableAt ℝ (fun y => fderiv ℝ f y c) z := fun c =>
    (hf2 z).clm_apply (differentiableAt_const c)
  have hS : ∀ c x, fderiv ℝ (fun y => fderiv ℝ f y c) z x = B x c := by
    intro c x
    rw [fderiv_clm_apply (hf2 z) (differentiableAt_const c)]
    simp [hB]
  have hH : ∀ a w : V, B w (Complex.I • a) = B a (Complex.I • w) := by
    intro a w; have := hh z a w; rwa [hS, hS] at this
  set D : V →L[ℝ] ℂ := Complex.ofRealCLM.comp (fderiv ℝ (fun y => fderiv ℝ f y a) z) -
    Complex.I • Complex.ofRealCLM.comp (fderiv ℝ (fun y => fderiv ℝ f y (Complex.I • a)) z) with hD
  have hder : HasFDerivAt (fun z => ((fderiv ℝ f z a : ℝ) : ℂ) -
      Complex.I * ((fderiv ℝ f z (Complex.I • a) : ℝ) : ℂ)) D z := by
    have h1 := Complex.ofRealCLM.hasFDerivAt.comp z (hdc a).hasFDerivAt
    have h2 := (Complex.ofRealCLM.hasFDerivAt.comp z (hdc (Complex.I • a)).hasFDerivAt).const_mul
      Complex.I
    exact h1.sub h2
  have hDval : ∀ w, D w = ((B w a : ℝ) : ℂ) - Complex.I * ((B w (Complex.I • a) : ℝ) : ℂ) := by
    intro w; simp [hD, hS]
  have hDI : ∀ w, D (Complex.I • w) = Complex.I * D w := by
    intro w
    have e1 : B (Complex.I • w) a = B w (Complex.I • a) := by rw [hsym, hH]
    have e2 : B (Complex.I • w) (Complex.I • a) = - B w a := by
      rw [hH, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg, hsym]
    rw [hDval, hDval, e1, e2]
    push_cast
    linear_combination ((B w (Complex.I • a) : ℝ) : ℂ) * Complex.I_sq
  let L : V →L[ℂ] ℂ :=
    { toFun := fun w => D w
      map_add' := fun x y => D.map_add x y
      map_smul' := by
        intro c w
        simp only [RingHom.id_apply, smul_eq_mul]
        have hc : c • w = c.re • w + c.im • (Complex.I • w) := by
          conv_lhs => rw [← Complex.re_add_im c]
          rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
        rw [hc, D.map_add, D.map_smul, D.map_smul, hDI, Complex.real_smul, Complex.real_smul]
        conv_rhs => rw [← Complex.re_add_im c]
        ring
      cont := D.continuous }
  have hL : L.restrictScalars ℝ = D := by ext w; rfl
  exact (hasFDerivAt_of_restrictScalars ℝ hder hL).differentiableAt

end GlobalTheory
