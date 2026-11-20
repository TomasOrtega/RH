import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.HermSelfDualLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨hrs, A, hA⟩` from `h`. Set `e : Fin r ⊕ Fin s ≃ Fin n` to `finSumFinEquiv.trans (finCongr hrs)`. Set `Q : Matrix (Fin n) (Fin n) ℂ` to `A.submatrix id e.symm`. Establish `key : Qᵀ * M * Q.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm`. Rewrite using `[← hA]`.

Simplify using `only [Q]`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.submatrix_apply]`. Establish `hN : ((Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm).det ≠ 0`. Rewrite using `[Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]`.

Simplify using `[Matrix.det_neg]`. Introduce `h0`. Apply `hN` to reduce the goal to its premises. Rewrite using `[← key, Matrix.det_mul, Matrix.det_mul, h0]`. Simplify using the standard rewrite rules.
-/
theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let Q : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Qᵀ * M * Q.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
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
Take `⟨w⟩` from `(inferInstance : Nonempty (InfinitePlace F))`. Establish `h` using `det_ne_zero_of_hasSig (hX.sig w)`. Establish `e : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det` using `(RingHom.map_det _ _).symm`. Introduce `h0`. Conclude with `h (by rw [e, h0, map_zero])`.
-/
theorem det_ne_zero_of_isHerm (σ : E →ₐ[F] E) (B : Base F E) {n : ℕ} {X : Spc F E n} {r s : ℕ}
    (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have h := det_ne_zero_of_hasSig (hX.sig w)
  have e : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det := (RingHom.map_det _ _).symm
  intro h0
  exact h (by rw [e, h0, map_zero])

/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [AlgHom.coe_toRingHom]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hE_transpose (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hE σ Jᵀ x y = form σ J y x := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [AlgHom.coe_toRingHom]
  ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨⟨e, h⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.isIntegral_coe⟩`.
-/
theorem isIntegral_iff_mem_range (e : E) : IsIntegral ℤ e ↔ e ∈ (algebraMap (𝓞 E) E).range :=
  ⟨fun h => ⟨⟨e, h⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.isIntegral_coe⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n X r s _ hX v`. Establish `hJ : (X.Jᵀ).det ≠ 0` using `by rw [Matrix.det_transpose]; exact det_ne_zero_of_isHerm σ B hX`. Use `(GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff hJ hX.lat).2 (fun y => ?_) v` and prove the remaining obligations. Rewrite using `[hX.dual y]`. Simplify using `only [hE_transpose, isIntegral_iff_mem_range]`.
-/
theorem isSelfDualAt_transpose : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ v : HeightOneSpectrum (𝓞 F), IsSelfDualAt σ X.Jᵀ X.L v := by
  intro F E _ _ _ _ _ σ B n X r s _ hX v
  have hJ : (X.Jᵀ).det ≠ 0 := by rw [Matrix.det_transpose]; exact det_ne_zero_of_isHerm σ B hX
  refine (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff hJ hX.lat).2 (fun y => ?_) v
  rw [hX.dual y]
  simp only [hE_transpose, isIntegral_iff_mem_range]

end GlobalTheory.HermSelfDualLoc

end
