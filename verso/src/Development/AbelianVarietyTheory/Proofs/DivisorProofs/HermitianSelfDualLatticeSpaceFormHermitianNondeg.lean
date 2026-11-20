import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodingerHerm

/- English proof (translation)
Simplify using `only [GlobalTheory.WeilSchrodinger.sesq, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply, smul_eq_mul, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem sesq_apply (D : D7) {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (x y : Fin k → D.host.E) :
    GlobalTheory.WeilSchrodinger.sesq D G x y = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [GlobalTheory.WeilSchrodinger.sesq, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply,
    smul_eq_mul, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Rewrite using `[sesq_apply, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]`. Both sides reduce to the same expression.
-/
theorem sesq_transpose_eq_form (D : D7) {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) (x y : Fin k → D.host.E) :
    GlobalTheory.WeilSchrodinger.sesq D Jᵀ y x = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig J x y := by
  rw [sesq_apply, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rfl

/- English proof (translation)
Take `⟨hrs, A, hA⟩` from `h`. Set `e : Fin r ⊕ Fin s ≃ Fin n` to `finSumFinEquiv.trans (finCongr hrs)`. Set `P : Matrix (Fin n) (Fin n) ℂ` to `A.submatrix id e.symm`. Establish `key : Pᵀ * M * P.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm`. Rewrite using `[← hA]`.

Both sides reduce to the same expression. Establish `hd` using `congrArg Matrix.det key`. Rewrite `hd` using `[Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg, Matrix.det_one, Matrix.det_mul, Matrix.det_mul]`. Introduce `h0`. Rewrite `hd` using `[h0, mul_zero, zero_mul]`.

Rewrite `hd` using `[Fintype.card_fin, one_mul, mul_one]`. Conclude with `pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hd.symm`.
-/
theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) :
    M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let P : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Pᵀ * M * P.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg,
    Matrix.det_one, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0, mul_zero, zero_mul] at hd
  rw [Fintype.card_fin, one_mul, mul_one] at hd
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hd.symm

variable (D : D7) (B : Base D.host.F D.host.E) {n : ℕ} (X : Spc D.host.F D.host.E n) {r s : ℕ}

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace D.host.F)` from `inferInstance`. Establish `h` using `det_ne_zero_of_hasSig (hX.sig w)`. Introduce `h0`. Apply `h` to reduce the goal to its premises. Establish `hm : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det` using `(RingHom.map_det _ _).symm`.

Rewrite using `[hm, h0, map_zero]`.
-/
theorem det_J_ne_zero (hX : X.IsHerm D.sp.cm.sig B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  intro h0
  apply h
  have hm : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det := (RingHom.map_det _ _).symm
  rw [hm, h0, map_zero]

/- English proof (translation)
Rewrite using `[Submodule.mem_one]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨o, rfl⟩`. Conclude with `o.isIntegral_coe`. Introduce `h`.

Conclude with `⟨⟨z, h⟩, rfl⟩`.
-/
theorem mem_one_iff (z : D.host.E) : z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨o, rfl⟩
    exact o.isIntegral_coe
  · intro h
    exact ⟨⟨z, h⟩, rfl⟩

/- English proof (translation)
Establish `hdet : X.Jᵀ.det ≠ 0` using `by rw [Matrix.det_transpose]; exact det_J_ne_zero D B X hX`. Use `⟨⟨fun x y => ?_⟩, ⟨fun x hx => ?_, fun y hy => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hs : ∀ i j, star (X.J i j) = X.J j i` using `fun i j => hX.herm j i`. Simplify using `only [sesq_apply, starRingEnd_apply, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Pi.star_apply, Matrix.transpose_apply, hs, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations. Establish `h1 : star x ᵥ* X.Jᵀ = 0`. Use `dotProduct_eq_zero _ fun v => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.dotProduct_mulVec, ← sesq_apply]`. Conclude with `hx v`.

Establish `h2 : star x = 0` using `Matrix.eq_zero_of_vecMul_eq_zero hdet h1`. Simplify using `using congrArg star h2`. Establish `h1 : X.Jᵀ *ᵥ y = 0`. Use `dotProduct_eq_zero _ fun v => ?_` and prove the remaining obligations. Rewrite using `[dotProduct_comm]`.

Use `hy (star v)` as an intermediate fact. Rewrite `this` using `[sesq_apply, star_star]`. Then use the resulting hypothesis. Conclude with `Matrix.eq_zero_of_mulVec_eq_zero hdet h1`. Use `show Formalism.E.hdual _ X.L = X.L`. Use extensionality with `x`.

Simplify using `only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]`. Rewrite using `[hX.dual x]`. Use `forall₂_congr fun y _ => ?_` and prove the remaining obligations. Rewrite using `[sesq_transpose_eq_form, mem_one_iff]`.
-/
theorem herm_nondeg_unimod (hX : X.IsHerm D.sp.cm.sig B r s) :
    (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).IsSymm ∧ (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).Nondegenerate ∧
      Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ) X.L := by
  have hdet : X.Jᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact det_J_ne_zero D B X hX
  refine ⟨⟨fun x y => ?_⟩, ⟨fun x hx => ?_, fun y hy => ?_⟩, ?_⟩
  ·
    have hs : ∀ i j, star (X.J i j) = X.J j i := fun i j => hX.herm j i
    simp only [sesq_apply, starRingEnd_apply, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star,
      Pi.star_apply, Matrix.transpose_apply, hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  ·
    have h1 : star x ᵥ* X.Jᵀ = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [← Matrix.dotProduct_mulVec, ← sesq_apply]
      exact hx v
    have h2 : star x = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
    simpa using congrArg star h2
  ·
    have h1 : X.Jᵀ *ᵥ y = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [dotProduct_comm]
      have := hy (star v)
      rwa [sesq_apply, star_star] at this
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1
  ·
    show Formalism.E.hdual _ X.L = X.L
    ext x
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
    rw [hX.dual x]
    refine forall₂_congr fun y _ => ?_
    rw [sesq_transpose_eq_form, mem_one_iff]

end GlobalTheory.WeilSchrodingerHerm

end

/- English proof (translation)
Introduce `D B _ _ X _ _ hX` and use `GlobalTheory.WeilSchrodingerHerm.herm_nondeg_unimod D B X hX`.
-/
theorem GlobalTheory.WeilSchrodingerHerm.main : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (n : ℕ) (X : Spc D.host.F D.host.E n) (r s : ℕ), X.IsHerm D.sp.cm.sig B r s →
      (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).IsSymm ∧ (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).Nondegenerate ∧
        Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ) X.L :=
  fun D B _ _ X _ _ hX => GlobalTheory.WeilSchrodingerHerm.herm_nondeg_unimod D B X hX
