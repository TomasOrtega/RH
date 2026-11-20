import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

open scoped Matrix.Norms.Operator

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem ex_val (X : Lie E 2) (t : ℝ) : (ex X t).val = NormedSpace.exp (t • Matrix.of X) := rfl

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, ex_val, ex_val, ex_val, add_smul]`. Conclude with `NormedSpace.exp_add_of_commute (((Commute.refl (Matrix.of X)).smul_left s).smul_right t)`.
-/
private theorem ex_add (X : Lie E 2) (s t : ℝ) : ex X (s + t) = ex X s * ex X t := by
  refine Units.ext ?_
  rw [Units.val_mul, ex_val, ex_val, ex_val, add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl (Matrix.of X)).smul_left s).smul_right t)

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[ex_val, zero_smul, NormedSpace.exp_zero]`. Both sides reduce to the same expression.
-/
private theorem ex_zero (X : Lie E 2) : ex X 0 = 1 := by
  refine Units.ext ?_
  rw [ex_val, zero_smul, NormedSpace.exp_zero]
  rfl

/- English proof (translation)
The claim follows from `inv_eq_of_mul_eq_one_right (by rw [← ex_add, add_neg_cancel, ex_zero])`.
-/
private theorem ex_inv (X : Lie E 2) (t : ℝ) : (ex X t)⁻¹ = ex X (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← ex_add, add_neg_cancel, ex_zero])

/- English proof (translation)
The claim follows from `continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Matrix.of X) t).continuousAt`.
-/
private theorem ex_val_cont (X : Lie E 2) : Continuous fun t : ℝ => (ex X t).val :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Matrix.of X) t).continuousAt

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨ex_val_cont X, ?_⟩` and prove the remaining obligations. Simplify using `only [ex_inv]`. Conclude with `(ex_val_cont X).comp continuous_neg`.
-/
private theorem ex_cont (X : Lie E 2) : Continuous (ex X) := by
  refine Units.continuous_iff.2 ⟨ex_val_cont X, ?_⟩
  simp only [ex_inv]
  exact (ex_val_cont X).comp continuous_neg

/- English proof (translation)
Set `L : Matrix (Fin 2) (Fin 2) (Cinf E) →L[ℝ] Lie E 2` to `{ toLinearMap := (Matrix.ofLinearEquiv ℝ).symm.toLinearMap, cont := continuous_id }`. Establish `h : HasDerivAt (fun t : ℝ => L (NormedSpace.exp (t • Matrix.of X))) (L (NormedSpace.exp ((0 : ℝ) • Matrix.of X) * Matrix.of X)) 0` using `L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Matrix.of X) (0 : ℝ))`. Rewrite `h` using `[zero_smul, NormedSpace.exp_zero, one_mul]`. Conclude with `h`.
-/
private theorem ex_der (X : Lie E 2) : HasDerivAt (fun t => toL (ex X t).val) X 0 := by
  let L : Matrix (Fin 2) (Fin 2) (Cinf E) →L[ℝ] Lie E 2 :=
    { toLinearMap := (Matrix.ofLinearEquiv ℝ).symm.toLinearMap, cont := continuous_id }
  have h : HasDerivAt (fun t : ℝ => L (NormedSpace.exp (t • Matrix.of X)))
      (L (NormedSpace.exp ((0 : ℝ) • Matrix.of X) * Matrix.of X)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Matrix.of X) (0 : ℝ))
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h

/- English proof (translation)
The claim follows from `hasDerivAt_pi.1 (hasDerivAt_pi.1 (ex_der X) i) j`.
-/
private theorem ex_ent (X : Lie E 2) (i j : Fin 2) :
    HasDerivAt (fun t => (ex X t).val i j) (X i j) 0 :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 (ex_der X) i) j

/- English proof (translation)
Establish `h` using `((ex_ent X 0 0).mul (ex_ent X 1 1)).sub ((ex_ent X 0 1).mul (ex_ent X 1 0))`. Establish `e0 : (ex X 0).val = 1` using `by rw [ex_zero]; rfl`. Simplify using `only [e0, Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, Matrix.one_apply_ne, mul_one, one_mul, zero_mul, mul_zero, add_zero, sub_zero] at h`. Rewrite using `[Matrix.trace_fin_two]`. Simplify using `only [Matrix.det_fin_two]`.

Conclude with `h`.
-/
private theorem ex_det_der (X : Lie E 2) :
    HasDerivAt (fun t => (ex X t).val.det) ((Matrix.of X).trace) 0 := by
  have h := ((ex_ent X 0 0).mul (ex_ent X 1 1)).sub ((ex_ent X 0 1).mul (ex_ent X 1 0))
  have e0 : (ex X 0).val = 1 := by rw [ex_zero]; rfl
  simp only [e0, Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true,
    Matrix.one_apply_ne, mul_one, one_mul, zero_mul, mul_zero, add_zero, sub_zero] at h
  rw [Matrix.trace_fin_two]
  simp only [Matrix.det_fin_two]
  exact h

/- English proof (translation)
Establish `hm : ∀ s t, (ex X (s + t)).val.det = (ex X s).val.det * (ex X t).val.det` using `fun s t => by`. Rewrite using `[ex_add, Units.val_mul, Matrix.det_mul]`. Establish `hd : ∀ t, HasDerivAt (fun s => (ex X s).val.det) (0 : Cinf E) t` using `fun t => by`. Establish `h0` using `ex_det_der X`. Rewrite `h0` using `[hX]`.

Establish `h1 : HasDerivAt (fun s => (ex X (s - t)).val.det) (0 : Cinf E) t` using `HasDerivAt.comp_sub_const t t (by simpa using h0)`. Establish `h2` using `h1.const_mul (ex X t).val.det`. Rewrite `h2` using `[mul_zero]`. Use `h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Use `show (ex X s).val.det = (ex X t).val.det * (ex X (s - t)).val.det`.

Rewrite using `[← hm, add_sub_cancel]`. Establish `hc` using `is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0`. Establish `e0 : (ex X 0).val = 1` using `by rw [ex_zero]; rfl`. Simplify `hc` using `[e0]`.
-/
private theorem ex_det (X : Lie E 2) (hX : (Matrix.of X).trace = 0) (t : ℝ) : (ex X t).val.det = 1 := by
  have hm : ∀ s t, (ex X (s + t)).val.det = (ex X s).val.det * (ex X t).val.det := fun s t => by
    rw [ex_add, Units.val_mul, Matrix.det_mul]
  have hd : ∀ t, HasDerivAt (fun s => (ex X s).val.det) (0 : Cinf E) t := fun t => by
    have h0 := ex_det_der X
    rw [hX] at h0
    have h1 : HasDerivAt (fun s => (ex X (s - t)).val.det) (0 : Cinf E) t :=
      HasDerivAt.comp_sub_const t t (by simpa using h0)
    have h2 := h1.const_mul (ex X t).val.det
    rw [mul_zero] at h2
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show (ex X s).val.det = (ex X t).val.det * (ex X (s - t)).val.det
    rw [← hm, add_sub_cancel]
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
  have e0 : (ex X 0).val = 1 := by rw [ex_zero]; rfl
  simpa [e0] using hc

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, ex_val, ex_val, ex_val]`. Establish `e : Matrix.of (X + zE s) = Matrix.of (zE s) + Matrix.of X`. Rewrite using `[add_comm]`. Both sides reduce to the same expression.

Establish `c : Commute (Matrix.of (zE s)) (Matrix.of X)` using `Matrix.scalar_commute s (fun r => Commute.all _ _) (Matrix.of X)`. Rewrite using `[e, smul_add]`. Conclude with `NormedSpace.exp_add_of_commute ((c.smul_left t).smul_right t)`.
-/
private theorem ex_cen (X : Lie E 2) (s : Cinf E) (t : ℝ) : ex (X + zE s) t = ex (zE s) t * ex X t := by
  refine Units.ext ?_
  rw [Units.val_mul, ex_val, ex_val, ex_val]
  have e : Matrix.of (X + zE s) = Matrix.of (zE s) + Matrix.of X := by
    rw [add_comm]; rfl
  have c : Commute (Matrix.of (zE s)) (Matrix.of X) :=
    Matrix.scalar_commute s (fun r => Commute.all _ _) (Matrix.of X)
  rw [e, smul_add]
  exact NormedSpace.exp_add_of_commute ((c.smul_left t).smul_right t)

end

end UpperTheory.ConvolutionTheory.R2.Ff

/- English proof (translation)
Introduce `E _ _ _ X`. Conclude with `⟨ex_add X, ex_cont X, ex_der X, ex_det X, fun s t => ex_cen X s t⟩`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.exPar :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], ExPar E := by
  intro E _ _ _ X
  exact ⟨ex_add X, ex_cont X, ex_der X, ex_det X, fun s t => ex_cen X s t⟩
