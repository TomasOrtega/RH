import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.PsiLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompLinearMapMatrixNonarchLocalField

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

/- English proof (translation)
Introduce `F _ _ v a x X`. Use `set t : (Kv v)ˣ := Matrix.GeneralLinearGroup.det x with ht`. Establish `htv : (t : Kv v) = (x.val).det`. Rewrite using `[ht, Matrix.GeneralLinearGroup.val_det_apply]`. Establish `hxx : x.val * (x⁻¹).val = 1`.

Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hxx' : (x⁻¹).val * x.val = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `hdet : (t : Kv v) * ((x⁻¹).val).det = 1`. Rewrite using `[htv, ← Matrix.det_mul, hxx, Matrix.det_one]`.

Establish `htt : ((t⁻¹ : (Kv v)ˣ) : Kv v) * (t : Kv v) = 1` using `Units.inv_mul t`. Establish `htt' : (t : Kv v) * ((t⁻¹ : (Kv v)ˣ) : Kv v) = 1` using `Units.mul_inv t`. Set `A : M2 v` to `(t : Kv v) • (x⁻¹).val`. Set `B : M2 v` to `((t⁻¹ : (Kv v)ˣ) : Kv v) • x.val`. Establish `hAB : A * B = 1`.

Simplify using `only [A, B, Matrix.smul_mul, Matrix.mul_smul, hxx', smul_smul, htt, one_smul]`. Establish `hBA : B * A = 1`. Simplify using `only [A, B, Matrix.smul_mul, Matrix.mul_smul, hxx, smul_smul, htt', one_smul]`. Set `L : (Fin 2 → Kv v) ≃ₗ[Kv v] (Fin 2 → Kv v)` to `Matrix.toLin'OfInv hBA hAB`. Establish `hL : ∀ y, L y = A *ᵥ y` using `fun y => rfl`.

Establish `hLdet : ((LinearEquiv.det L : (Kv v)ˣ) : Kv v) = t`. Establish `h1 : ((LinearEquiv.det L : (Kv v)ˣ) : Kv v) = A.det`. Rewrite using `[LinearEquiv.coe_det]`. Conclude with `LinearMap.det_toLin' A`. Rewrite using `[h1, Matrix.det_smul, Fintype.card_fin, pow_two, mul_assoc, hdet, mul_one]`.

Establish `hLu : LinearEquiv.det L = t` using `Units.ext hLdet`. Establish `hmod : (((distribHaarChar (Kv v) t : NNReal) : ℝ) : ℂ) = ((ab (idl v t) : ℝ) : ℂ)`. Rewrite using `[(UpperTheory.ConvolutionTheory.R2.I.psiLaws F v).2.2.2.2.2 t, GroundTheory.LocalField.distribHaarChar_eq_modulus]`. Establish `hne : ((ab (idl v t) : ℝ) : ℂ) ≠ 0`. Rewrite using `[← hmod]`.

Conclude with `(distribHaarChar_pos (A := Kv v) (g := t)).ne'` after adjusting the coercions. Use `haveI : (μ2 v).IsAddHaarMeasure := by`. Unfold `μ2`. Use `infer_instance`. Establish `key` using `GlobalTheory.DetScale.integral_comp_linearEquiv (k := Kv v) (μ2 v) L (fun c' => a (cols (fun i => ((x⁻¹).val * X) i 1) c') * ψl v (((x⁻¹).val * X) 0 0 * c' 1 - ((x⁻¹).val * X) 1 0 * c' 0))`.

Rewrite `key` using `[hLu, hmod]`. Establish `hpt : ∀ y : Fin 2 → Kv v, a ((x⁻¹).val * cols (fun i => X i 1) y * (dd x).val) * ψl v (X 0 0 * y 1 - X 1 0 * y 0) = a (cols (fun i => ((x⁻¹).val * X) i 1) (L y)) * ψl v (((x⁻¹).val * X) 0 0 * (L y) 1 - ((x⁻¹).val * X) 1 0 * (L y) 0)`. Introduce `y`. Establish `hd2` using `hdet`. Rewrite `hd2` using `[Matrix.det_fin_two]`.

Establish `e1 : (x⁻¹).val * cols (fun i => X i 1) y * (dd x).val = cols (fun i => ((x⁻¹).val * X) i 1) (L y)`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [hL, A, cols, dd, dL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct, ← ht] <;> ring`. Establish `e2 : X 0 0 * y 1 - X 1 0 * y 0 = ((x⁻¹).val * X) 0 0 * (L y) 1 - ((x⁻¹).val * X) 1 0 * (L y) 0`.

Simplify using `only [hL, A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul]`. Take the linear combination `(-(X 0 0 * y 1 - X 1 0 * y 0)) * hd2`. Rewrite using `[e1, e2]`. Unfold `Pt`. Rewrite using `[integral_congr_ae (Eventually.of_forall hpt)]`.

Rewrite using `[show (fun a_1 => a (cols (fun i => ((x⁻¹).val * X) i 1) (L a_1)) * ψl v (((x⁻¹).val * X) 0 0 * (L a_1) 1 - ((x⁻¹).val * X) 1 0 * (L a_1) 0)) = _ from rfl]`. Rewrite using `[key, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.I.ptL :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (a : M2 v → ℂ) (x : GLv v) (X : M2 v),
      Pt a ((x⁻¹).val * X) = ((ab (idl v (Matrix.GeneralLinearGroup.det x)) : ℝ) : ℂ) * Pt (fun m => a ((x⁻¹).val * m * (dd x).val)) X := by
  intro F _ _ v a x X
  set t : (Kv v)ˣ := Matrix.GeneralLinearGroup.det x with ht
  have htv : (t : Kv v) = (x.val).det := by
    rw [ht, Matrix.GeneralLinearGroup.val_det_apply]
  have hxx : x.val * (x⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hxx' : (x⁻¹).val * x.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : (t : Kv v) * ((x⁻¹).val).det = 1 := by
    rw [htv, ← Matrix.det_mul, hxx, Matrix.det_one]
  have htt : ((t⁻¹ : (Kv v)ˣ) : Kv v) * (t : Kv v) = 1 := Units.inv_mul t
  have htt' : (t : Kv v) * ((t⁻¹ : (Kv v)ˣ) : Kv v) = 1 := Units.mul_inv t
  let A : M2 v := (t : Kv v) • (x⁻¹).val
  let B : M2 v := ((t⁻¹ : (Kv v)ˣ) : Kv v) • x.val
  have hAB : A * B = 1 := by
    simp only [A, B, Matrix.smul_mul, Matrix.mul_smul, hxx', smul_smul, htt, one_smul]
  have hBA : B * A = 1 := by
    simp only [A, B, Matrix.smul_mul, Matrix.mul_smul, hxx, smul_smul, htt', one_smul]
  let L : (Fin 2 → Kv v) ≃ₗ[Kv v] (Fin 2 → Kv v) := Matrix.toLin'OfInv hBA hAB
  have hL : ∀ y, L y = A *ᵥ y := fun y => rfl
  have hLdet : ((LinearEquiv.det L : (Kv v)ˣ) : Kv v) = t := by
    have h1 : ((LinearEquiv.det L : (Kv v)ˣ) : Kv v) = A.det := by
      rw [LinearEquiv.coe_det]
      exact LinearMap.det_toLin' A
    rw [h1, Matrix.det_smul, Fintype.card_fin, pow_two, mul_assoc, hdet, mul_one]
  have hLu : LinearEquiv.det L = t := Units.ext hLdet
  have hmod : (((distribHaarChar (Kv v) t : NNReal) : ℝ) : ℂ) = ((ab (idl v t) : ℝ) : ℂ) := by
    rw [(UpperTheory.ConvolutionTheory.R2.I.psiLaws F v).2.2.2.2.2 t, GroundTheory.LocalField.distribHaarChar_eq_modulus]
  have hne : ((ab (idl v t) : ℝ) : ℂ) ≠ 0 := by
    rw [← hmod]
    exact_mod_cast (distribHaarChar_pos (A := Kv v) (g := t)).ne'
  haveI : (μ2 v).IsAddHaarMeasure := by
    unfold μ2
    infer_instance
  have key := GlobalTheory.DetScale.integral_comp_linearEquiv (k := Kv v) (μ2 v) L
    (fun c' => a (cols (fun i => ((x⁻¹).val * X) i 1) c') *
      ψl v (((x⁻¹).val * X) 0 0 * c' 1 - ((x⁻¹).val * X) 1 0 * c' 0))
  rw [hLu, hmod] at key
  have hpt : ∀ y : Fin 2 → Kv v,
      a ((x⁻¹).val * cols (fun i => X i 1) y * (dd x).val) * ψl v (X 0 0 * y 1 - X 1 0 * y 0) =
      a (cols (fun i => ((x⁻¹).val * X) i 1) (L y)) *
        ψl v (((x⁻¹).val * X) 0 0 * (L y) 1 - ((x⁻¹).val * X) 1 0 * (L y) 0) := by
    intro y
    have hd2 := hdet
    rw [Matrix.det_fin_two] at hd2
    have e1 : (x⁻¹).val * cols (fun i => X i 1) y * (dd x).val =
        cols (fun i => ((x⁻¹).val * X) i 1) (L y) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hL, A, cols, dd, dL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct, ← ht] <;> ring
    have e2 : X 0 0 * y 1 - X 1 0 * y 0 =
        ((x⁻¹).val * X) 0 0 * (L y) 1 - ((x⁻¹).val * X) 1 0 * (L y) 0 := by
      simp only [hL, A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul]
      linear_combination (-(X 0 0 * y 1 - X 1 0 * y 0)) * hd2
    rw [e1, e2]
  unfold Pt
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  rw [show (fun a_1 => a (cols (fun i => ((x⁻¹).val * X) i 1) (L a_1)) * ψl v (((x⁻¹).val * X) 0 0 * (L a_1) 1 - ((x⁻¹).val * X) 1 0 * (L a_1) 0)) = _ from rfl]
  rw [key, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
