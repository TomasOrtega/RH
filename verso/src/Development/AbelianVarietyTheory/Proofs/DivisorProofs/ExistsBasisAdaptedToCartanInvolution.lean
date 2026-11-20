import Mathlib
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

open scoped MatrixOrder in

/- English proof (translation)
Take `⟨R, hR⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hP.posSemidef.nonneg`. Establish `hd : IsUnit R.det`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h`. Establish `h1` using `hP.det_pos`.

Rewrite `h1` using `[hR, Matrix.det_mul, h]`. Simplify using `at h1`. Conclude with `⟨R, R⁻¹, Matrix.mul_nonsing_inv R hd, Matrix.nonsing_inv_mul R hd, hR⟩`.
-/
theorem posDef_exists_invertible_conjTranspose_mul_self {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.PosDef) :
    ∃ R Ri : Matrix (Fin n) (Fin n) ℂ, R * Ri = 1 ∧ Ri * R = 1 ∧ P = Rᴴ * R := by
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hP.posSemidef.nonneg
  have hd : IsUnit R.det := by
    rw [isUnit_iff_ne_zero]
    intro h
    have h1 := hP.det_pos
    rw [hR, Matrix.det_mul, h] at h1
    simp at h1
  exact ⟨R, R⁻¹, Matrix.mul_nonsing_inv R hd, Matrix.nonsing_inv_mul R hd, hR⟩

/- English proof (translation)
Establish `hH' : t.IsHermitian` using `hH`. Use `set U : Matrix (Fin n) (Fin n) ℂ := (hH'.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU`. Use `set d : Fin n → ℂ := fun i => ((hH'.eigenvalues i : ℝ) : ℂ) with hd`. Establish `hspec : t = U * diagonal d * Uᴴ`. Use `hH'.spectral_theorem` as an intermediate fact.

Simplify `this` using `[Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def]`. Establish `hUU : U * Uᴴ = 1`. Use `hH'.eigenvectorUnitary.2.2` as an intermediate fact. Simplify `this` using `[star_eq_conjTranspose]`. Establish `hUU' : Uᴴ * U = 1`.

Use `hH'.eigenvectorUnitary.2.1` as an intermediate fact. Simplify `this` using `[star_eq_conjTranspose]`. Establish `hD : Uᴴ * t * U = diagonal d`. Rewrite using `[hspec]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = diagonal d := by rw [hUU']; simp`. Establish `hDD : diagonal d * diagonal d = 1`. Rewrite using `[← hD]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hUU, Matrix.mul_one, ht, Matrix.mul_one, hUU']`. Establish `hsq : ∀ i, d i * d i = 1`. Introduce `i`. Use `congrFun (congrFun hDD i) i` as an intermediate fact.

Simplify `this` using `[diagonal_mul_diagonal]`. Set `e : Fin (Fintype.card {i // d i = 1}) ⊕ Fin (Fintype.card {i // ¬ d i = 1}) ≃ Fin n` to `(Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans (Equiv.sumCompl (fun i => d i = 1))`. Establish `he1 : ∀ a, d (e (Sum.inl a)) = 1` using `fun a => ((Fintype.equivFin {i // d i = 1}).symm a).2`. Establish `he2 : ∀ a, d (e (Sum.inr a)) = -1` using `fun a => (mul_self_eq_one_iff.1 (hsq _)).resolve_left ((Fintype.equivFin {i // ¬ d i = 1}).symm a).2`. Use `⟨_, _, U.submatrix id e, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[conjTranspose_submatrix, submatrix_mul_equiv, hUU, submatrix_id_id]`. Rewrite using `[conjTranspose_submatrix]`. Use `Matrix.submatrix_mul_equiv Uᴴ U e (Equiv.refl _) e` as an intermediate fact. Simplify using `only [Equiv.coe_refl] at this`. Rewrite using `[this, hUU', submatrix_one_equiv]`.

Establish `h1 : (U.submatrix id e)ᴴ * t * U.submatrix id e = (Uᴴ * t * U).submatrix e e`. Use extensionality with `a b`. Simplify using `[Matrix.mul_apply]`. Rewrite using `[h1, hD, submatrix_diagonal_equiv]`. Apply the tactic sequence `ext (a | a) (b | b) <;> simp [diagonal_apply, he1, he2, one_apply]`.

Apply the tactic sequence `all_goals (split_ifs <;> simp)`.
-/
theorem hermitian_involution_unitary_blocks {n : ℕ} (t : Matrix (Fin n) (Fin n) ℂ)
    (hH : tᴴ = t) (ht : t * t = 1) :
    ∃ (p q : ℕ) (V : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ), V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧
      Vᴴ * t * V = Matrix.fromBlocks 1 0 0 (-1) := by
  classical
  have hH' : t.IsHermitian := hH
  set U : Matrix (Fin n) (Fin n) ℂ := (hH'.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set d : Fin n → ℂ := fun i => ((hH'.eigenvalues i : ℝ) : ℂ) with hd
  have hspec : t = U * diagonal d * Uᴴ := by
    have := hH'.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def] using this
  have hUU : U * Uᴴ = 1 := by
    have := hH'.eigenvectorUnitary.2.2
    simpa [star_eq_conjTranspose] using this
  have hUU' : Uᴴ * U = 1 := by
    have := hH'.eigenvectorUnitary.2.1
    simpa [star_eq_conjTranspose] using this
  have hD : Uᴴ * t * U = diagonal d := by
    rw [hspec]
    calc Uᴴ * (U * diagonal d * Uᴴ) * U = (Uᴴ * U) * diagonal d * (Uᴴ * U) := by
          simp only [Matrix.mul_assoc]
      _ = diagonal d := by rw [hUU']; simp
  have hDD : diagonal d * diagonal d = 1 := by
    rw [← hD]
    calc Uᴴ * t * U * (Uᴴ * t * U) = Uᴴ * (t * (U * Uᴴ) * t) * U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, ht, Matrix.mul_one, hUU']
  have hsq : ∀ i, d i * d i = 1 := by
    intro i
    have := congrFun (congrFun hDD i) i
    simpa [diagonal_mul_diagonal] using this
  let e : Fin (Fintype.card {i // d i = 1}) ⊕ Fin (Fintype.card {i // ¬ d i = 1}) ≃ Fin n :=
    (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans
      (Equiv.sumCompl (fun i => d i = 1))
  have he1 : ∀ a, d (e (Sum.inl a)) = 1 := fun a => ((Fintype.equivFin {i // d i = 1}).symm a).2
  have he2 : ∀ a, d (e (Sum.inr a)) = -1 := fun a =>
    (mul_self_eq_one_iff.1 (hsq _)).resolve_left
      ((Fintype.equivFin {i // ¬ d i = 1}).symm a).2
  refine ⟨_, _, U.submatrix id e, ?_, ?_, ?_⟩
  · rw [conjTranspose_submatrix, submatrix_mul_equiv, hUU, submatrix_id_id]
  · rw [conjTranspose_submatrix]
    have := Matrix.submatrix_mul_equiv Uᴴ U e (Equiv.refl _) e
    simp only [Equiv.coe_refl] at this
    rw [this, hUU', submatrix_one_equiv]
  · have h1 : (U.submatrix id e)ᴴ * t * U.submatrix id e = (Uᴴ * t * U).submatrix e e := by
      ext a b
      simp [Matrix.mul_apply]
    rw [h1, hD, submatrix_diagonal_equiv]
    ext (a | a) (b | b) <;> simp [diagonal_apply, he1, he2, one_apply]
    all_goals (split_ifs <;> simp)

/- English proof (translation)
Introduce `n G s hs hG hP`. Take `⟨R, Ri, h1, h2, hR⟩` from `posDef_exists_invertible_conjTranspose_mul_self _ hP`. Establish `hG1 : G = Rᴴ * R * s` using `by rw [← hR, Matrix.mul_assoc, hs, Matrix.mul_one]`. Establish `hG2 : G = sᴴ * (Rᴴ * R)` using `by rw [← hR, ← Matrix.mul_assoc, hG]`. Establish `h3 : Riᴴ * Rᴴ = 1` using `by rw [← conjTranspose_mul, h1, conjTranspose_one]`.

Establish `hGt : Riᴴ * G * Ri = R * s * Ri`. Rewrite using `[hG1]`. Combine the equalities or inequalities in the displayed calculation. Establish `hherm : (R * s * Ri)ᴴ = R * s * Ri`. Rewrite using `[← hGt]`.

Use `conv_rhs => rw [hG2]`. Rewrite using `[hGt]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_one]`.

Use `_ = _ := by simp only [Matrix.mul_assoc]`. Establish `hinv : (R * s * Ri) * (R * s * Ri) = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [h2, Matrix.mul_one, hs, Matrix.mul_one, h1]`.

Take `⟨p, q, V, hV1, hV2, hV3⟩` from `hermitian_involution_unitary_blocks _ hherm hinv`. Use `⟨p, q, Ri * V, Vᴴ * R, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hV3, ← hGt]`.

Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[← hV3]`. Use `symm`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = _ := by rw [hV1, Matrix.mul_one, h2, Matrix.one_mul]`.
-/
theorem exists_basis_adapted_to_cartan_involution :
    ∀ (n : ℕ) (G s : Matrix (Fin n) (Fin n) ℂ), s * s = 1 → sᴴ * G * s = G → (G * s).PosDef →
      ∃ (p q : ℕ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ)
        (B' : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), B * B' = 1 ∧ B' * B = 1 ∧
        Bᴴ * G * B = Matrix.fromBlocks 1 0 0 (-1) ∧
        s * B = B * Matrix.fromBlocks 1 0 0 (-1) := by
  intro n G s hs hG hP
  obtain ⟨R, Ri, h1, h2, hR⟩ := posDef_exists_invertible_conjTranspose_mul_self _ hP
  have hG1 : G = Rᴴ * R * s := by rw [← hR, Matrix.mul_assoc, hs, Matrix.mul_one]
  have hG2 : G = sᴴ * (Rᴴ * R) := by rw [← hR, ← Matrix.mul_assoc, hG]
  have h3 : Riᴴ * Rᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have hGt : Riᴴ * G * Ri = R * s * Ri := by
    rw [hG1]
    calc Riᴴ * (Rᴴ * R * s) * Ri = (Riᴴ * Rᴴ) * (R * s * Ri) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h3, Matrix.one_mul]
  have hherm : (R * s * Ri)ᴴ = R * s * Ri := by
    rw [← hGt]
    conv_rhs => rw [hG2]
    rw [hGt]
    calc (R * s * Ri)ᴴ = Riᴴ * sᴴ * Rᴴ * (R * Ri) := by
          rw [h1]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hinv : (R * s * Ri) * (R * s * Ri) = 1 := by
    calc (R * s * Ri) * (R * s * Ri) = R * (s * (Ri * R) * s) * Ri := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, hs, Matrix.mul_one, h1]
  obtain ⟨p, q, V, hV1, hV2, hV3⟩ := hermitian_involution_unitary_blocks _ hherm hinv
  refine ⟨p, q, Ri * V, Vᴴ * R, ?_, ?_, ?_, ?_⟩
  · calc Ri * V * (Vᴴ * R) = Ri * (V * Vᴴ) * R := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV1, Matrix.mul_one, h2]
  · calc Vᴴ * R * (Ri * V) = Vᴴ * (R * Ri) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hV2]
  · rw [← hV3, ← hGt]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  · rw [← hV3]
    symm
    calc Ri * V * (Vᴴ * (R * s * Ri) * V) = Ri * (V * Vᴴ) * R * (s * (Ri * V)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV1, Matrix.mul_one, h2, Matrix.one_mul]

end GlobalTheory
