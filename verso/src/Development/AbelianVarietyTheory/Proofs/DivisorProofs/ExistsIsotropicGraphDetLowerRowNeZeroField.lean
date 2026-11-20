import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewHermitianMulAddDetNeZeroOfPairStatement
open scoped Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ σ hσ hε n J hJ hJd g hg hQ`. Take `⟨ε, hε0, hε⟩` from `hε`. Establish `hmm : ∀ A : Matrix (Fin n) (Fin n) k, (A.map σ).map σ = A`. Introduce `A`. Use extensionality with `i j`.

Simplify using `[hσ]`. Establish `hJu : IsUnit J.det` using `isUnit_iff_ne_zero.mpr hJd`. Use `set K : Matrix (Fin n) (Fin n) k := J⁻¹ with hK`. Establish `hJK : J * K = 1` using `Matrix.mul_nonsing_inv J hJu`. Establish `hKJ : K * J = 1` using `Matrix.nonsing_inv_mul J hJu`.

Establish `hJh : (J.map σ)ᵀ = J` using `by ext i j; simp [hJ]`. Establish `hKh : (K.map σ)ᵀ = K`. Establish `h1 : (K.map σ)ᵀ * J = 1` using `by conv_lhs => rw [← hJh]`. Rewrite using `[← Matrix.transpose_mul, ← Matrix.map_mul, hJK]`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation. Establish `hKt : Kᵀ = K.map σ` using `by conv_lhs => rw [← hKh]`. Simplify using the standard rewrite rules. Establish `hQR : Matrix.fromBlocks 0 K K 0 * Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) k) J J 0 = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)`. Rewrite using `[Matrix.fromBlocks_multiply]`.

Simplify using `[hKJ]`. Establish `hRQ : Matrix.fromBlocks 0 J J 0 * Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) k) K K 0 = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)` using `mul_eq_one_comm.mp hQR`. Establish `h2 : (Matrix.fromBlocks 0 K K 0 * gᵀ * Matrix.fromBlocks 0 J J 0) * g.map σ = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᵀ, hQ, hQR]`. Establish `h3` using `mul_eq_one_comm.mp h2`.

Establish `h4 : g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ = Matrix.fromBlocks 0 K K 0`. Combine the equalities or inequalities in the displayed calculation. Take `⟨A, B, C, D, rfl⟩ : ∃ A B C D, g = Matrix.fromBlocks A B C D` from `⟨_, _, _, _, (Matrix.fromBlocks_toBlocks g).symm⟩`. Rewrite `h4` using `[Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]`. Establish `h5` using `h4.2.2.2`.

Simplify using `only [Matrix.mul_zero, zero_add, add_zero] at h5`. Establish `h6 : D * K.map σ * (C.map σ)ᵀ + C * K.map σ * (D.map σ)ᵀ = 0`. Use `congrArg (fun M : Matrix (Fin n) (Fin n) k => M.map σ) h5` as an intermediate fact. Simplify using `only [Matrix.map_add σ (map_add σ), Matrix.map_mul, hmm, Matrix.map_zero σ (map_zero σ)] at this`. Simplify `this` using `[Matrix.transpose_map]`.

Establish `hJσ : K.map σ * J.map σ = 1`. Rewrite using `[← Matrix.map_mul, hKJ]`. Simplify using the standard rewrite rules. Take `⟨V, hV, hdet⟩` from `GlobalTheory.T.exists_skewHermitian_mul_add_det_ne_zero k σ hσ ε hε0 hε n (C * K.map σ) D (by`. Rewrite using `[Matrix.map_mul, hmm, Matrix.transpose_mul, hKt, ← Matrix.mul_assoc, add_comm]`.

Conclude with `h6)`. Use the proof step `(by`. Introduce `a ha hD`. Establish `hC : a ᵥ* C = 0`. Establish `: a ᵥ* (C * K.map σ * J.map σ) = 0`.

Rewrite using `[← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]`. Rewrite `this` using `[Matrix.mul_assoc, hJσ, Matrix.mul_one]`. Then use the resulting hypothesis. Establish `h7 : (Sum.elim 0 a) ᵥ* Matrix.fromBlocks A B C D = 0`. Rewrite using `[Matrix.vecMul_fromBlocks]`. Simplify using `[hC, hD]`.

Establish `h8` using `Matrix.eq_zero_of_vecMul_eq_zero hg h7`. Use function extensionality and compare the values at `i`. Conclude with `congrFun h8 (Sum.inr i))`. Use `⟨K.map σ * V, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.transpose_mul, hKh, Matrix.mul_assoc, hKJ, Matrix.mul_one, Matrix.map_mul, hmm, ← Matrix.mul_assoc, hJK, Matrix.one_mul]`.

Establish `: V.map σ = -Vᵀ`. Rewrite using `[← Matrix.transpose_neg, ← hV, Matrix.transpose_transpose]`. Rewrite using `[this, add_neg_cancel]`. Simplify `hdet` using `[Matrix.mul_assoc]`.
-/
theorem exists_isotropic_graph_det_lowerRow_ne_zero_field :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → (∃ ε : k, ε ≠ 0 ∧ σ ε = -ε) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) k), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k, g.det ≠ 0 →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map σ = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) k, Zᵀ * J + J * Z.map σ = 0 ∧
        (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det ≠ 0 := by
  intro k _ σ hσ hε n J hJ hJd g hg hQ
  obtain ⟨ε, hε0, hε⟩ := hε
  have hmm : ∀ A : Matrix (Fin n) (Fin n) k, (A.map σ).map σ = A := by
    intro A; ext i j; simp [hσ]
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJd
  set K : Matrix (Fin n) (Fin n) k := J⁻¹ with hK
  have hJK : J * K = 1 := Matrix.mul_nonsing_inv J hJu
  have hKJ : K * J = 1 := Matrix.nonsing_inv_mul J hJu
  have hJh : (J.map σ)ᵀ = J := by ext i j; simp [hJ]
  have hKh : (K.map σ)ᵀ = K := by
    have h1 : (K.map σ)ᵀ * J = 1 := by
      conv_lhs => rw [← hJh]
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hJK]
      simp
    calc (K.map σ)ᵀ = (K.map σ)ᵀ * (J * K) := by rw [hJK, Matrix.mul_one]
      _ = K := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hKt : Kᵀ = K.map σ := by
    conv_lhs => rw [← hKh]
    simp
  have hQR : Matrix.fromBlocks 0 K K 0 * Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) k) J J 0
      = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := by
    rw [Matrix.fromBlocks_multiply]
    simp [hKJ]
  have hRQ : Matrix.fromBlocks 0 J J 0 * Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) k) K K 0
      = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := mul_eq_one_comm.mp hQR
  have h2 : (Matrix.fromBlocks 0 K K 0 * gᵀ * Matrix.fromBlocks 0 J J 0) * g.map σ = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᵀ, hQ, hQR]
  have h3 := mul_eq_one_comm.mp h2
  have h4 : g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ = Matrix.fromBlocks 0 K K 0 := by
    calc g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ
        = g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ *
          (Matrix.fromBlocks 0 J J 0 * Matrix.fromBlocks 0 K K 0) := by rw [hRQ, Matrix.mul_one]
      _ = (g.map σ * (Matrix.fromBlocks 0 K K 0 * gᵀ * Matrix.fromBlocks 0 J J 0)) *
          Matrix.fromBlocks 0 K K 0 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h3, Matrix.one_mul]
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, g = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks g).symm⟩
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at h4
  have h5 := h4.2.2.2
  simp only [Matrix.mul_zero, zero_add, add_zero] at h5
  have h6 : D * K.map σ * (C.map σ)ᵀ + C * K.map σ * (D.map σ)ᵀ = 0 := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) k => M.map σ) h5
    simp only [Matrix.map_add σ (map_add σ), Matrix.map_mul, hmm, Matrix.map_zero σ (map_zero σ)] at this
    simpa [Matrix.transpose_map] using this
  have hJσ : K.map σ * J.map σ = 1 := by
    rw [← Matrix.map_mul, hKJ]; simp
  obtain ⟨V, hV, hdet⟩ := GlobalTheory.T.exists_skewHermitian_mul_add_det_ne_zero k σ hσ ε hε0 hε n (C * K.map σ) D
    (by
      rw [Matrix.map_mul, hmm, Matrix.transpose_mul, hKt, ← Matrix.mul_assoc, add_comm]
      exact h6)
    (by
      intro a ha hD
      have hC : a ᵥ* C = 0 := by
        have : a ᵥ* (C * K.map σ * J.map σ) = 0 := by
          rw [← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]
        rwa [Matrix.mul_assoc, hJσ, Matrix.mul_one] at this
      have h7 : (Sum.elim 0 a) ᵥ* Matrix.fromBlocks A B C D = 0 := by
        rw [Matrix.vecMul_fromBlocks]
        simp [hC, hD]
      have h8 := Matrix.eq_zero_of_vecMul_eq_zero hg h7
      funext i
      exact congrFun h8 (Sum.inr i))
  refine ⟨K.map σ * V, ?_, ?_⟩
  · rw [Matrix.transpose_mul, hKh, Matrix.mul_assoc, hKJ, Matrix.mul_one, Matrix.map_mul, hmm,
      ← Matrix.mul_assoc, hJK, Matrix.one_mul]
    have : V.map σ = -Vᵀ := by
      rw [← Matrix.transpose_neg, ← hV, Matrix.transpose_transpose]
    rw [this, add_neg_cancel]
  · simpa [Matrix.mul_assoc] using hdet

end GlobalTheory
