import Development.WeilBound.ThetaLifts.TowerModels.PlaneHerm

noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

/- English proof (translation)
Take `⟨hrs, A, hA⟩` from `h`. Substitute `hrs` using the available equality. Introduce `hM`. Establish `key` using `congrArg Matrix.det hA`. Rewrite `key` using `[Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_fin]`.

Set `e : Fin r ⊕ Fin s ≃ Fin (r + s)` to `finSumFinEquiv`. Establish `hsub : (Aᵀ * M * A.map star).submatrix e.symm e.symm = (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.submatrix, Matrix.transpose_apply]`. Establish `h2` using `congrArg Matrix.det hsub`.

Rewrite `h2` using `[Matrix.det_submatrix_equiv_self, key, Matrix.det_mul, Matrix.det_mul, hM, mul_zero, zero_mul]`. Conclude with `pow_ne_zero _ (by norm_num) h2`.
-/
theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  subst hrs
  intro hM
  have key := congrArg Matrix.det hA
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one,
    Fintype.card_fin] at key
  let e : Fin r ⊕ Fin s ≃ Fin (r + s) := finSumFinEquiv
  have hsub : (Aᵀ * M * A.map star).submatrix e.symm e.symm =
      (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star := by
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix, Matrix.transpose_apply]
  have h2 := congrArg Matrix.det hsub
  rw [Matrix.det_submatrix_equiv_self, key, Matrix.det_mul, Matrix.det_mul, hM, mul_zero, zero_mul] at h2
  exact pow_ne_zero _ (by norm_num) h2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `h` using `det_ne_zero_of_hasSig (hX.sig w)`. Rewrite `h` using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `fun h0 => h (by rw [h0, map_zero])`.
-/
theorem det_herm {n : ℕ} {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  exact fun h0 => h (by rw [h0, map_zero])

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `h` using `det_ne_zero_of_hasSig (hX.sig w)`. Rewrite `h` using `[Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `fun h0 => h (by rw [h0, map_zero, mul_zero])`.
-/
theorem det_skew {n : ℕ} {X : Spc F E n} {r s : ℕ} (hX : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  exact fun h0 => h (by rw [h0, map_zero, mul_zero])

end PositivityTheory.ThKG.Tow

end
