import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

namespace GlobalTheory

/- English proof (translation)
Establish `hP : (T.map Complex.im).PosDef` using `hT.2`. Establish `hY : (T.map fun t => (t.im : ℂ)) = (T.map Complex.im).map (Complex.ofRealHom : ℝ →+* ℂ)`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `hdet : (T.map fun t => (t.im : ℂ)).det ≠ 0`.

Rewrite using `[hY, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(Complex.ofReal_ne_zero).2 hP.det_pos.ne'`. Establish `hsym : (T.map fun t => (t.im : ℂ))ᵀ = T.map fun t => (t.im : ℂ)`. Establish `h1 : (T.map Complex.im)ᵀ = T.map Complex.im`. Use `hP.1` as an intermediate fact.

Use extensionality with `i j`. Use `congrFun (congrFun this i) j` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_apply]`. Rewrite using `[hY, ← Matrix.transpose_map, h1]`. Rewrite using `[Matrix.transpose_nonsing_inv, hsym, Matrix.mul_smul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)]`.

Use extensionality with `i j`. Simplify using `[Matrix.one_apply, Matrix.ofNat_apply]`.
-/
theorem siegel_im_inv_transpose_mul_two {g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) (hT : GlobalTheory.IsSiegel T) :
    ((T.map fun t => (t.im : ℂ))⁻¹)ᵀ * ((2 : ℂ) • T.map fun t => (t.im : ℂ)) = 2 := by
  have hP : (T.map Complex.im).PosDef := hT.2
  have hY : (T.map fun t => (t.im : ℂ)) = (T.map Complex.im).map (Complex.ofRealHom : ℝ →+* ℂ) := by
    ext i j; simp
  have hdet : (T.map fun t => (t.im : ℂ)).det ≠ 0 := by
    rw [hY, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Complex.ofReal_ne_zero).2 hP.det_pos.ne'
  have hsym : (T.map fun t => (t.im : ℂ))ᵀ = T.map fun t => (t.im : ℂ) := by
    have h1 : (T.map Complex.im)ᵀ = T.map Complex.im := by
      have := hP.1
      ext i j
      have := congrFun (congrFun this i) j
      simpa [Matrix.conjTranspose_apply] using this
    rw [hY, ← Matrix.transpose_map, h1]
  rw [Matrix.transpose_nonsing_inv, hsym, Matrix.mul_smul,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)]
  ext i j
  simp [Matrix.one_apply, Matrix.ofNat_apply]

end GlobalTheory
