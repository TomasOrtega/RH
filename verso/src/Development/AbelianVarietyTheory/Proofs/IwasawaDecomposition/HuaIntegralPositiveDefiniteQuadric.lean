import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecOfMulToMatMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMeasurePreservingRowSucc

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.HuaQuadric

variable {p q : ℕ}

/- English proof (translation)
Use `open scoped MatrixOrder in`. Take `⟨R, hR⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.posSemidef.nonneg`. Use `⟨R, ?_, hR⟩` and prove the remaining obligations. Establish `h` using `hA.det_pos.ne'`. Rewrite `h` using `[hR, det_mul]`.

Conclude with `(right_ne_zero_of_mul h).isUnit`.
-/
theorem exists_factor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, IsUnit R.det ∧ A = Rᴴ * R := by
  open scoped MatrixOrder in
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.posSemidef.nonneg
  refine ⟨R, ?_, hR⟩
  have h := hA.det_pos.ne'
  rw [hR, det_mul] at h
  exact (right_ne_zero_of_mul h).isUnit

/- English proof (translation)
Simplify using `[shear, fromBlocks_conjTranspose, fromBlocks_multiply]`.
-/
theorem shear_fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) (b : Matrix (Fin p) (Fin q) ℂ) (c : Matrix (Fin q) (Fin p) ℂ)
    (d : Matrix (Fin q) (Fin q) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) :
    shear (fromBlocks a b c d) Z = fromBlocks a (a * Z + b) (Zᴴ * a + c) ((Zᴴ * a + c) * Z + (Zᴴ * b + d)) := by
  simp [shear, fromBlocks_conjTranspose, fromBlocks_multiply]

/- English proof (translation)
Take `⟨R, hR, ha⟩` from `exists_factor (posDef_blocks hA).1`. Establish `e : A.toBlocks₂₁ = A.toBlocks₁₂ᴴ`. Use extensionality with `a b`. Conclude with `(hA.1.apply _ _).symm`. Establish `hRh : IsUnit Rᴴ.det` using `by rw [det_conjTranspose]; exact hR.star`.

Take `⟨c, hc⟩ : ∃ c, A.toBlocks₁₂ = Rᴴ * R * c` from `⟨R⁻¹ * (Rᴴ⁻¹ * A.toBlocks₁₂), by`. Rewrite using `[Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hR, mul_nonsing_inv_cancel_left _ _ hRh]⟩`. Establish `hA' : A = fromBlocks (Rᴴ * R) (Rᴴ * R * c) (cᴴ * (Rᴴ * R)) A.toBlocks₂₂` using `by conv_lhs => rw [← fromBlocks_toBlocks A, e, ha, hc]`. Simplify using `[conjTranspose_mul, Matrix.mul_assoc]`. Generalize the expression as in `A.toBlocks₂₂ = d at hA'`.

Establish `hs : shear A (-c) = fromBlocks (Rᴴ * R) 0 0 (d - cᴴ * (Rᴴ * R * c))`. Rewrite using `[hA', shear_fromBlocks]`. Simplify using `[sub_eq_neg_add]`. Establish `hS` using `(posDef_blocks (posDef_shear hA (-c))).2.1`. Rewrite `hS` using `[hs, toBlocks_fromBlocks₂₂]`.

Take `⟨T, hT, ht⟩` from `exists_factor hS`. Establish `hTh : IsUnit Tᴴ.det` using `by rw [det_conjTranspose]; exact hT.star`. Use `⟨R, T, R * c * T⁻¹, hR, hT, ?_, fun Z => ?_⟩` and prove the remaining obligations. Rewrite using `[← det_shear A (-c), hs, ht, det_fromBlocks_zero₂₁, det_mul, det_mul, det_conjTranspose, det_conjTranspose]`. Use `push_cast`.

Rewrite using `[Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]`. Both sides reduce to the same expression. Rewrite using `[hA', shear_fromBlocks, toBlocks_fromBlocks₂₂, eq_add_of_sub_eq ht]`. Simplify using `only [conjTranspose_mul, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, conjTranspose_nonsing_inv, mul_nonsing_inv_cancel_left _ _ hTh, nonsing_inv_mul _ hT, Matrix.mul_one, Matrix.one_mul]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_square {A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hA : A.PosDef) :
    ∃ (R : Matrix (Fin p) (Fin p) ℂ) (T : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin p) (Fin q) ℂ),
      IsUnit R.det ∧ IsUnit T.det ∧ A.det = (Complex.normSq R.det * Complex.normSq T.det : ℝ) ∧
      ∀ Z, (shear A Z).toBlocks₂₂ = Tᴴ * (1 + (R * Z * T⁻¹ + C)ᴴ * (R * Z * T⁻¹ + C)) * T := by
  obtain ⟨R, hR, ha⟩ := exists_factor (posDef_blocks hA).1
  have e : A.toBlocks₂₁ = A.toBlocks₁₂ᴴ := by
    ext a b
    exact (hA.1.apply _ _).symm
  have hRh : IsUnit Rᴴ.det := by rw [det_conjTranspose]; exact hR.star
  obtain ⟨c, hc⟩ : ∃ c, A.toBlocks₁₂ = Rᴴ * R * c :=
    ⟨R⁻¹ * (Rᴴ⁻¹ * A.toBlocks₁₂), by
      rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hR, mul_nonsing_inv_cancel_left _ _ hRh]⟩
  have hA' : A = fromBlocks (Rᴴ * R) (Rᴴ * R * c) (cᴴ * (Rᴴ * R)) A.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks A, e, ha, hc]
    simp [conjTranspose_mul, Matrix.mul_assoc]
  generalize A.toBlocks₂₂ = d at hA'
  have hs : shear A (-c) = fromBlocks (Rᴴ * R) 0 0 (d - cᴴ * (Rᴴ * R * c)) := by
    rw [hA', shear_fromBlocks]
    simp [sub_eq_neg_add]
  have hS := (posDef_blocks (posDef_shear hA (-c))).2.1
  rw [hs, toBlocks_fromBlocks₂₂] at hS
  obtain ⟨T, hT, ht⟩ := exists_factor hS
  have hTh : IsUnit Tᴴ.det := by rw [det_conjTranspose]; exact hT.star
  refine ⟨R, T, R * c * T⁻¹, hR, hT, ?_, fun Z => ?_⟩
  · rw [← det_shear A (-c), hs, ht, det_fromBlocks_zero₂₁, det_mul, det_mul, det_conjTranspose, det_conjTranspose]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    rfl
  · rw [hA', shear_fromBlocks, toBlocks_fromBlocks₂₂, eq_add_of_sub_eq ht]
    simp only [conjTranspose_mul, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
      conjTranspose_nonsing_inv, mul_nonsing_inv_cancel_left _ _ hTh,
      nonsing_inv_mul _ hT, Matrix.mul_one, Matrix.one_mul]
    abel

/- English proof (translation)
Introduce `p q A hA`. Take `⟨R, T, C, hR, hT, hd, hZ⟩` from `exists_square hA`. Establish `hr : 0 < Complex.normSq R.det` using `Complex.normSq_pos.2 hR.ne_zero`. Establish `ht : 0 < Complex.normSq T.det` using `Complex.normSq_pos.2 hT.ne_zero`. Set `f : (Fin p × Fin q → ℂ) → ℝ≥0∞` to `fun v => ENNReal.ofReal ((1 + (toMat v)ᴴ * toMat v).det.re ^ (-((p + q : ℕ) : ℤ)))`.

Establish `hf : Measurable f` using `((Complex.continuous_re.comp (continuous_const.add (continuous_toMat.matrix_conjTranspose.matrix_mul continuous_toMat)).matrix_det).measurable.pow_const _).ennreal_ofReal`. Establish `h1 : ∀ v : Fin p × Fin q → ℂ, ENNReal.ofReal ((shear A (toMat v)).toBlocks₂₂.det.re ^ (-((p + q : ℕ) : ℤ))) = ENNReal.ofReal (Complex.normSq T.det ^ (-((p + q : ℕ) : ℤ))) * f (vecOf (R * toMat v * T⁻¹ + C))`. Introduce `v`. Simplify using `only [f, toMat_vecOf]`. Rewrite using `[← ENNReal.ofReal_mul (zpow_pos ht _).le, ← mul_zpow, hZ, det_mul, det_mul, det_conjTranspose, mul_right_comm, ← Complex.re_ofReal_mul, Complex.normSq_eq_conj_mul_self]`.

Both sides reduce to the same expression. Repeatedly rewrite using `[h1]`. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, GlobalTheory.FlagFibre.lintegral_affine p q R T⁻¹ C hR (isUnit_nonsing_inv_det _ hT) f hf]`. Establish `h2 : ∫⁻ v, f v = ENNReal.ofReal (grassConst p q)⁻¹` using `GlobalTheory.HuaIntegral.dual_mass p q`. Establish `h3 : Complex.normSq T⁻¹.det = (Complex.normSq T.det)⁻¹`.

Rewrite using `[det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀]`. Rewrite using `[h2, h3, ← mul_assoc, ← ENNReal.ofReal_mul (zpow_pos ht _).le, ← ENNReal.ofReal_mul (by positivity), hd, Complex.ofReal_re, div_eq_mul_inv]`. Use `congr 2`. Simplify using `only [_root_.zpow_neg, _root_.zpow_natCast, pow_add, mul_pow, inv_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem quadric : ∀ (p q : ℕ) (A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → ∫⁻ v : Fin p × Fin q → ℂ, ENNReal.ofReal ((shear A (toMat v)).toBlocks₂₂.det.re ^ (-((p + q : ℕ) : ℤ))) = ENNReal.ofReal (A.det.re ^ (-(q : ℤ)) / grassConst p q) := by
  intro p q A hA
  obtain ⟨R, T, C, hR, hT, hd, hZ⟩ := exists_square hA
  have hr : 0 < Complex.normSq R.det := Complex.normSq_pos.2 hR.ne_zero
  have ht : 0 < Complex.normSq T.det := Complex.normSq_pos.2 hT.ne_zero
  let f : (Fin p × Fin q → ℂ) → ℝ≥0∞ := fun v =>
    ENNReal.ofReal ((1 + (toMat v)ᴴ * toMat v).det.re ^ (-((p + q : ℕ) : ℤ)))
  have hf : Measurable f :=
    ((Complex.continuous_re.comp (continuous_const.add
      (continuous_toMat.matrix_conjTranspose.matrix_mul continuous_toMat)).matrix_det).measurable.pow_const
        _).ennreal_ofReal
  have h1 : ∀ v : Fin p × Fin q → ℂ,
      ENNReal.ofReal ((shear A (toMat v)).toBlocks₂₂.det.re ^ (-((p + q : ℕ) : ℤ))) =
        ENNReal.ofReal (Complex.normSq T.det ^ (-((p + q : ℕ) : ℤ))) * f (vecOf (R * toMat v * T⁻¹ + C)) := by
    intro v
    simp only [f, toMat_vecOf]
    rw [← ENNReal.ofReal_mul (zpow_pos ht _).le, ← mul_zpow, hZ, det_mul, det_mul, det_conjTranspose, mul_right_comm,
      ← Complex.re_ofReal_mul, Complex.normSq_eq_conj_mul_self]
    rfl
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    GlobalTheory.FlagFibre.lintegral_affine p q R T⁻¹ C hR (isUnit_nonsing_inv_det _ hT) f hf]
  have h2 : ∫⁻ v, f v = ENNReal.ofReal (grassConst p q)⁻¹ := GlobalTheory.HuaIntegral.dual_mass p q
  have h3 : Complex.normSq T⁻¹.det = (Complex.normSq T.det)⁻¹ := by
    rw [det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀]
  rw [h2, h3, ← mul_assoc, ← ENNReal.ofReal_mul (zpow_pos ht _).le, ← ENNReal.ofReal_mul (by positivity), hd,
    Complex.ofReal_re, div_eq_mul_inv]
  congr 2
  simp only [_root_.zpow_neg, _root_.zpow_natCast, pow_add, mul_pow, inv_pow]
  field_simp

end GlobalTheory.HuaQuadric
