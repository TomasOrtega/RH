import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.WeilBound.ThetaLifts.LeviDeterminants.WeilRepRationalDarbouxFixesThetaDistribution
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace PositivityTheory.ThKF0

/- English proof (translation)
Take `⟨hrs, A, hA⟩` from `h`. Set `e : Fin r ⊕ Fin s ≃ Fin n` to `finSumFinEquiv.trans (finCongr hrs)`. Establish `key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm`. Rewrite using `[← hA, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_mul Aᵀ M e.symm id id Function.bijective_id]`. Simplify using `[Matrix.transpose_submatrix, Matrix.submatrix_map]`.

Introduce `h0`. Use `congrArg Matrix.det key` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self]`. Simplify using `[Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at this`. Conclude with `pow_ne_zero s (by norm_num : (-1 : ℂ) ≠ 0) this.symm`.
-/
theorem rat_det_ne_zero_of_hasSig {n r s : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      Matrix.submatrix_mul Aᵀ M e.symm id id Function.bijective_id]
    simp [Matrix.transpose_submatrix, Matrix.submatrix_map]
  intro h0
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self] at this
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at this
  exact pow_ne_zero s (by norm_num : (-1 : ℂ) ≠ 0) this.symm

/- English proof (translation)
Introduce `h0`. Apply `h` to reduce the goal to its premises. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]`.
-/
theorem rat_det_ne_zero_of_map {E : Type} [Field E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ)
    (h : (J.map f).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' Φ hΦ`. Take `⟨w⟩` from `(inferInstance : Nonempty (InfinitePlace F))`. Establish `hX : X.J.det ≠ 0` using `rat_det_ne_zero_of_map X.J (B.emb w).1 (rat_det_ne_zero_of_hasSig _ (hP.herm.sig w))`. Establish `hW : W.J.det ≠ 0`. Use `rat_det_ne_zero_of_map W.J (B.emb w).1 fun h0 => rat_det_ne_zero_of_hasSig _ (hP.skew.sig w) ?_` and prove the remaining obligations.

Rewrite using `[Matrix.det_smul, h0, mul_zero]`. Conclude with `darboux_coordinates_rational_exist F E σ hP.base.cm B.ψ hP.base.std n d X.J W.J hP.herm.herm hX hP.skew.skew hW M.co hP.good.rat χX χW hP.hX hP.hW om hP.weil γ hγ γ' hγ' Φ hΦ`.
-/
theorem theta_sum_rational_invariance : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' Φ hΦ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hX : X.J.det ≠ 0 := rat_det_ne_zero_of_map X.J (B.emb w).1 (rat_det_ne_zero_of_hasSig _ (hP.herm.sig w))
  have hW : W.J.det ≠ 0 := by
    refine rat_det_ne_zero_of_map W.J (B.emb w).1 fun h0 => rat_det_ne_zero_of_hasSig _ (hP.skew.sig w) ?_
    rw [Matrix.det_smul, h0, mul_zero]
  exact darboux_coordinates_rational_exist F E σ hP.base.cm B.ψ hP.base.std n d X.J W.J hP.herm.herm hX hP.skew.skew hW M.co
    hP.good.rat χX χW hP.hX hP.hW om hP.weil γ hγ γ' hγ' Φ hΦ

end PositivityTheory.ThKF0
