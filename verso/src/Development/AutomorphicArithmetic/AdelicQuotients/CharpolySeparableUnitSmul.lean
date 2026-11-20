import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open Polynomial

/- English proof (translation)
Establish `hc : (C (r : R) : R[X]) * C ((r⁻¹ : Rˣ) : R) = 1`. Rewrite using `[← C_mul, Units.mul_inv, C_1]`. Establish `hmat : Matrix.charmatrix ((r : R) • M) = (C (r : R) : R[X]) • (Matrix.charmatrix M).map (compRingHom (C ((r⁻¹ : Rˣ) : R) * X))`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `only [Matrix.charmatrix_apply_eq, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, coe_compRingHom_apply, sub_comp, X_comp, C_comp, mul_sub, ← mul_assoc, hc, one_mul, ← C_mul]`. Simplify using `only [Matrix.charmatrix_apply_ne _ _ _ h, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, coe_compRingHom_apply, neg_comp, C_comp, mul_neg, ← C_mul]`. Establish `hdet : M.charpoly.comp (C ((r⁻¹ : Rˣ) : R) * X) = ((Matrix.charmatrix M).map (compRingHom (C ((r⁻¹ : Rˣ) : R) * X))).det`. Rewrite using `[Matrix.charpoly, ← coe_compRingHom_apply, RingHom.map_det]`.

Both sides reduce to the same expression. Rewrite using `[Matrix.charpoly, hmat, Matrix.det_smul, Fintype.card_fin, hdet, C_pow]`.
-/
private theorem charpoly_unit_smul {R : Type} [CommRing R] {n : ℕ} (r : Rˣ)
    (M : Matrix (Fin n) (Fin n) R) :
    ((r : R) • M).charpoly =
      C ((r : R) ^ n) * M.charpoly.comp (C ((r⁻¹ : Rˣ) : R) * X) := by
  have hc : (C (r : R) : R[X]) * C ((r⁻¹ : Rˣ) : R) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  have hmat : Matrix.charmatrix ((r : R) • M) =
      (C (r : R) : R[X]) • (Matrix.charmatrix M).map
        (compRingHom (C ((r⁻¹ : Rˣ) : R) * X)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.charmatrix_apply_eq, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        coe_compRingHom_apply, sub_comp, X_comp, C_comp, mul_sub, ← mul_assoc, hc, one_mul,
        ← C_mul]
    · simp only [Matrix.charmatrix_apply_ne _ _ _ h, Matrix.smul_apply, Matrix.map_apply,
        smul_eq_mul, coe_compRingHom_apply, neg_comp, C_comp, mul_neg, ← C_mul]
  have hdet : M.charpoly.comp (C ((r⁻¹ : Rˣ) : R) * X) =
      ((Matrix.charmatrix M).map (compRingHom (C ((r⁻¹ : Rˣ) : R) * X))).det := by
    rw [Matrix.charpoly, ← coe_compRingHom_apply, RingHom.map_det]
    rfl
  rw [Matrix.charpoly, hmat, Matrix.det_smul, Fintype.card_fin, hdet, C_pow]

/- English proof (translation)
Take `⟨a, b, hab⟩` from `hp`. Use `set L : R[X] := C ((r⁻¹ : Rˣ) : R) * X with hL`. Establish `hd : derivative (p.comp L) = C ((r⁻¹ : Rˣ) : R) * (derivative p).comp L`. Rewrite using `[derivative_comp, hL, derivative_C_mul, derivative_X, mul_one]`. Establish `hc : (C (r : R) : R[X]) * C ((r⁻¹ : Rˣ) : R) = 1`.

Rewrite using `[← C_mul, Units.mul_inv, C_1]`. Use `⟨a.comp L, b.comp L * C (r : R), ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun q : R[X] => q.comp L) hab`. Simplify using `only [add_comp, mul_comp, one_comp] at h`. Rewrite using `[hd, ← h]`.

Take the linear combination `((b.comp L) * (derivative p).comp L) * hc`.
-/
private theorem separable_comp_unit {R : Type} [CommRing R] (r : Rˣ) {p : R[X]}
    (hp : p.Separable) : (p.comp (C ((r⁻¹ : Rˣ) : R) * X)).Separable := by
  obtain ⟨a, b, hab⟩ := hp
  set L : R[X] := C ((r⁻¹ : Rˣ) : R) * X with hL
  have hd : derivative (p.comp L) = C ((r⁻¹ : Rˣ) : R) * (derivative p).comp L := by
    rw [derivative_comp, hL, derivative_C_mul, derivative_X, mul_one]
  have hc : (C (r : R) : R[X]) * C ((r⁻¹ : Rˣ) : R) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  refine ⟨a.comp L, b.comp L * C (r : R), ?_⟩
  have h := congrArg (fun q : R[X] => q.comp L) hab
  simp only [add_comp, mul_comp, one_comp] at h
  rw [hd, ← h]
  linear_combination ((b.comp L) * (derivative p).comp L) * hc

/- English proof (translation)
Introduce `R _ n r M h`. Rewrite using `[charpoly_unit_smul, Polynomial.separable_def, derivative_C_mul]`. Conclude with `(isCoprime_mul_unit_left (isUnit_C.2 (r.isUnit.pow n)) _ _).2 (separable_comp_unit r h)`.
-/
theorem UpperTheory.charpoly_separable_unit_smul :
    SepSc := by
  intro R _ n r M h
  rw [charpoly_unit_smul, Polynomial.separable_def, derivative_C_mul]
  exact (isCoprime_mul_unit_left (isUnit_C.2 (r.isUnit.pow n)) _ _).2
    (separable_comp_unit r h)
