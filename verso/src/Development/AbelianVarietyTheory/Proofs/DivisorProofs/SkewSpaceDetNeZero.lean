import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct

namespace GlobalTheory.SkewGram

/- English proof (translation)
Take `⟨hrs, A, hA⟩` from `h`. Set `e : Fin r ⊕ Fin s ≃ Fin n` to `finSumFinEquiv.trans (finCongr hrs)`. Set `A' : Matrix (Fin n) (Fin n) ℂ` to `A.submatrix id e.symm`. Establish `key : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm`. Rewrite using `[← hA]`.

Both sides reduce to the same expression. Establish `hdet : (A'ᵀ * M * A'.map star).det ≠ 0`. Rewrite using `[key, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]`. Simplify using `[Matrix.det_neg]`. Introduce `h0`.

Apply `hdet` to reduce the goal to its premises. Rewrite using `[Matrix.det_mul, Matrix.det_mul, h0]`. Simplify using the standard rewrite rules.
-/
theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; rfl
  have hdet : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [key, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply hdet
  rw [Matrix.det_mul, Matrix.det_mul, h0]
  simp

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B d r s W hW h0`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Apply `det_ne_zero_of_hasSig (hW.sig w)` to reduce the goal to its premises. Rewrite using `[Matrix.det_smul]`. Use `RingHom.map_det ((B.emb w).1 : E →+* ℂ) W.J` as an intermediate fact.

Rewrite `this` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← this, h0, map_zero, mul_zero]`.
-/
theorem det_ne_zero_of_isSkew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (d r s : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d),
    W.IsSkew σ B r s → W.J.det ≠ 0 := by
  intro F E _ _ _ _ _ σ B d r s W hW h0
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  apply det_ne_zero_of_hasSig (hW.sig w)
  rw [Matrix.det_smul]
  have := RingHom.map_det ((B.emb w).1 : E →+* ℂ) W.J
  rw [RingHom.mapMatrix_apply] at this
  rw [← this, h0, map_zero, mul_zero]

end GlobalTheory.SkewGram
