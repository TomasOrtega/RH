import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.ThK.SqIntHerm

open Matrix

/- English proof (translation)
Take `⟨hrs, A, hA⟩` from `h`. Set `e : Fin r ⊕ Fin s ≃ Fin n` to `finSumFinEquiv.trans (finCongr hrs)`. Set `Q : Matrix (Fin n) (Fin n) ℂ` to `A.submatrix id e.symm`. Establish `key : Qᵀ * M * Q.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm`. Rewrite using `[← hA]`.

Simplify using `only [Q]`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.submatrix_apply]`. Establish `hN : ((Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm).det ≠ 0`. Rewrite using `[Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]`.

Simplify using `[Matrix.det_neg]`. Introduce `h0`. Apply `hN` to reduce the goal to its premises. Rewrite using `[← key, Matrix.det_mul, Matrix.det_mul, h0]`. Simplify using the standard rewrite rules.
-/
theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let Q : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Qᵀ * M * Q.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]
    simp only [Q]
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix_apply]
  have hN : ((Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm).det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply hN
  rw [← key, Matrix.det_mul, Matrix.det_mul, h0]
  simp

/- English proof (translation)
The claim follows from `(f.map_det M).symm`.
-/
theorem det_map_ringHom {K L : Type} [CommRing K] [CommRing L] (f : K →+* L) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (M.map f).det = f M.det := (f.map_det M).symm

/- English proof (translation)
Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]`. Rewrite using `[hσc, hW.skew i j, map_neg, hW.skew j i]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Matrix.det_smul]`.

Establish `hmap : (W.J.map σ).det = σ W.J.det` using `det_map_ringHom (σ : E →+* E) W.J`. Rewrite using `[hmap]`. Use `mul_ne_zero (pow_ne_zero _ hc) ?_` and prove the remaining obligations. Introduce `h0`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`.

Establish `hM` using `det_ne_zero_of_hasSig (hW.sig w)`. Establish `hJ : W.J.det = 0` using `σ.toRingHom.injective (by simpa using h0)`. Apply `hM` to reduce the goal to its premises. Rewrite using `[Matrix.det_smul, det_map_ringHom, hJ, map_zero, mul_zero]`.
-/
theorem isHermND_smul_map (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (W : Spc F E n) (r s : ℕ) (hW : W.IsSkew σ B r s) (c : E) (hc : c ≠ 0) (hσc : σ c = -c) :
    IsHermND σ (c • W.J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    rw [hσc, hW.skew i j, map_neg, hW.skew j i]
    ring
  · rw [Matrix.det_smul]
    have hmap : (W.J.map σ).det = σ W.J.det := det_map_ringHom (σ : E →+* E) W.J
    rw [hmap]
    refine mul_ne_zero (pow_ne_zero _ hc) ?_
    intro h0
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hM := det_ne_zero_of_hasSig (hW.sig w)
    have hJ : W.J.det = 0 := σ.toRingHom.injective (by simpa using h0)
    apply hM
    rw [Matrix.det_smul, det_map_ringHom, hJ, map_zero, mul_zero]

end GlobalTheory.ThK.SqIntHerm
