import Mathlib
import GroundTheory.AutomorphicForms.HermitianSpaces
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open GroundTheory.Automorphic Matrix

instance fact_gaussQ : Fact (∀ r : ℚ, r ^ 2 ≠ -1 + 0 * r) :=
  ⟨fun r h => by nlinarith [sq_nonneg r]⟩

abbrev GaussQ : Type := QuadraticAlgebra ℚ (-1) 0

instance : Algebra.IsQuadraticExtension ℚ GaussQ :=
  ⟨QuadraticAlgebra.finrank_eq_two _ _⟩

instance : NumberField GaussQ where

noncomputable abbrev gaussBasis : Module.Basis (Fin 2) ℚ GaussQ := QuadraticAlgebra.basis (-1 : ℚ) 0

/- English proof (translation)
Simplify using `[gaussBasis, QuadraticAlgebra.basis]`. Both sides reduce to the same expression.
-/
theorem gaussBasis_zero : gaussBasis 0 = 1 := by
  simp [gaussBasis, QuadraticAlgebra.basis]
  rfl

/- English proof (translation)
Simplify using `[gaussBasis, QuadraticAlgebra.basis]`.
-/
theorem gaussBasis_one : gaussBasis 1 = ⟨0, 1⟩ := by
  simp [gaussBasis, QuadraticAlgebra.basis]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gauss_algebraMap_re (q : ℚ) : (algebraMap ℚ GaussQ q).re = q := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gauss_algebraMap_im (q : ℚ) : (algebraMap ℚ GaussQ q).im = 0 := rfl

/- English proof (translation)
Rewrite using `[Algebra.trace_eq_matrix_trace gaussBasis, Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, gaussBasis_zero, gaussBasis_one]`. Express the relevant statement in the definitionally equal form `(![(z * 1).re, (z * 1).im] 0) + ![(z * ⟨0, 1⟩).re, (z * ⟨0, 1⟩).im] 1 = _`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, QuadraticAlgebra.im_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trace_gaussQ (z : GaussQ) : Algebra.trace ℚ GaussQ z = 2 * z.re := by
  rw [Algebra.trace_eq_matrix_trace gaussBasis, Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply,
    Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    gaussBasis_zero, gaussBasis_one]
  change (![(z * 1).re, (z * 1).im] 0) + ![(z * ⟨0, 1⟩).re, (z * ⟨0, 1⟩).im] 1 = _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, QuadraticAlgebra.im_mul]
  ring

/- English proof (translation)
Rewrite using `[conj_apply, trace_gaussQ]`. Use `ext`. Simplify using `only [QuadraticAlgebra.re_sub, gauss_algebraMap_re, QuadraticAlgebra.re_star]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [QuadraticAlgebra.im_sub, gauss_algebraMap_im, QuadraticAlgebra.im_star]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_gaussQ (z : GaussQ) : conj ℚ GaussQ z = star z := by
  rw [conj_apply, trace_gaussQ]
  ext
  · simp only [QuadraticAlgebra.re_sub, gauss_algebraMap_re, QuadraticAlgebra.re_star]; ring
  · simp only [QuadraticAlgebra.im_sub, gauss_algebraMap_im, QuadraticAlgebra.im_star]; ring

/- English proof (translation)
Rewrite using `[conj_gaussQ]`. Simplify using the standard rewrite rules.
-/
theorem conj_gaussQ_re (z : GaussQ) : (conj ℚ GaussQ z).re = z.re := by
  rw [conj_gaussQ]; simp

/- English proof (translation)
Rewrite using `[conj_gaussQ]`. Simplify using the standard rewrite rules.
-/
theorem conj_gaussQ_im (z : GaussQ) : (conj ℚ GaussQ z).im = -z.im := by
  rw [conj_gaussQ]; simp

noncomputable def gramAniso : Matrix (Fin 2) (Fin 2) GaussQ := Matrix.diagonal ![1, -3]

noncomputable def gramIso : Matrix (Fin 2) (Fin 2) GaussQ := Matrix.diagonal ![1, -1]

noncomputable def gaussValue (H : Matrix (Fin 2) (Fin 2) GaussQ) (x : Fin 2 → GaussQ) : GaussQ :=
  (fun i => conj ℚ GaussQ (x i)) ⬝ᵥ (H *ᵥ x)

/- English proof (translation)
Simplify using `only [gaussValue, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaussValue_diagonal (d : Fin 2 → GaussQ) (x : Fin 2 → GaussQ) :
    gaussValue (Matrix.diagonal d) x =
      d 0 * (x 0 * conj ℚ GaussQ (x 0)) + d 1 * (x 1 * conj ℚ GaussQ (x 1)) := by
  simp only [gaussValue, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two]
  ring

/- English proof (translation)
Rewrite using `[gramAniso, Matrix.det_diagonal, Fin.prod_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]`. Conclude with `(neg_ne_zero.mpr (three_ne_zero)).isUnit`.
-/
theorem isUnit_det_gramAniso : IsUnit gramAniso.det := by
  rw [gramAniso, Matrix.det_diagonal, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
  exact (neg_ne_zero.mpr (three_ne_zero)).isUnit

/- English proof (translation)
Rewrite using `[gramIso, Matrix.det_diagonal, Fin.prod_univ_two]`. Simplify using the standard rewrite rules.
-/
theorem isUnit_det_gramIso : IsUnit gramIso.det := by
  rw [gramIso, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

/- English proof (translation)
Unfold `IsHermitianFor gramAniso`. Rewrite using `[Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]`. Use `congr 1`. Use extensionality with `i : 1`. Apply the tactic sequence `fin_cases i <;> simp [conjHom, map_neg, map_ofNat]`.
-/
theorem isHermitianFor_gramAniso : IsHermitianFor (conjHom ℚ GaussQ) gramAniso := by
  unfold IsHermitianFor gramAniso
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
  congr 1
  ext i : 1
  fin_cases i <;> simp [conjHom, map_neg, map_ofNat]

/- English proof (translation)
Unfold `IsHermitianFor gramIso`. Rewrite using `[Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]`. Use `congr 1`. Use extensionality with `i : 1`. Apply the tactic sequence `fin_cases i <;> simp [conjHom, map_neg]`.
-/
theorem isHermitianFor_gramIso : IsHermitianFor (conjHom ℚ GaussQ) gramIso := by
  unfold IsHermitianFor gramIso
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
  congr 1
  ext i : 1
  fin_cases i <;> simp [conjHom, map_neg]

/- English proof (translation)
Use `⟨?_, ?_, by norm_num, by norm_num⟩` and prove the remaining obligations. Rewrite using `[gramAniso, gaussValue_diagonal]`. Simplify using the standard rewrite rules. Rewrite using `[gramAniso, gaussValue_diagonal]`. Simplify using the standard rewrite rules.
-/
theorem signature_gramAniso :
    gaussValue gramAniso ![1, 0] = algebraMap ℚ GaussQ 1 ∧
      gaussValue gramAniso ![0, 1] = algebraMap ℚ GaussQ (-3) ∧ (0 : ℚ) < 1 ∧ (-3 : ℚ) < 0 := by
  refine ⟨?_, ?_, by norm_num, by norm_num⟩
  · rw [gramAniso, gaussValue_diagonal]
    simp
  · rw [gramAniso, gaussValue_diagonal]
    simp

noncomputable def gaussPairing (H : Matrix (Fin 2) (Fin 2) GaussQ) (x y : Fin 2 → GaussQ) : GaussQ :=
  (fun i => conj ℚ GaussQ (x i)) ⬝ᵥ (H *ᵥ y)

/- English proof (translation)
Use `⟨fun h => one_ne_zero (congrFun h 0), ?_⟩` and prove the remaining obligations. Rewrite using `[gramIso, gaussValue_diagonal]`. Simplify using the standard rewrite rules.
-/
theorem isotropic_gramIso : (![1, 1] : Fin 2 → GaussQ) ≠ 0 ∧ gaussValue gramIso ![1, 1] = 0 := by
  refine ⟨fun h => one_ne_zero (congrFun h 0), ?_⟩
  rw [gramIso, gaussValue_diagonal]
  simp

end GroundTheory.Heights₂.Theta
