import Mathlib

open Matrix

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[Matrix.map_mul, Matrix.transpose_mul]`.
-/
theorem map_transpose_mul_rev {R : Type} [CommRing R] (s : R →+* R) {l m n : Type} [Fintype m]
    (A : Matrix l m R) (B : Matrix m n R) :
    ((A * B).map s)ᵀ = (B.map s)ᵀ * (A.map s)ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

/- English proof (translation)
Introduce `R _ s N ι κ _ _ _ _ _ _ J G G' Q Qi h1 h2 hD hG'`. Establish `h1s : (Qi.map s)ᵀ * (Q.map s)ᵀ = 1`. Rewrite using `[← map_transpose_mul_rev, h1, Matrix.map_one _ (map_zero s) (map_one s), transpose_one]`. Establish `hblk : ∀ (y : Matrix ι ι R) (c : Matrix κ ι R), ((Matrix.fromBlocks y 0 c (1 : Matrix κ κ R)).map s)ᵀ * Matrix.fromBlocks G 0 0 G' * Matrix.fromBlocks y 0 c (1 : Matrix κ κ R) = Matrix.fromBlocks ((y.map s)ᵀ * G * y + (c.map s)ᵀ * G' * c) ((c.map s)ᵀ * G') (G' * c) G'`. Introduce `y c`.

Rewrite using `[Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.map_one _ (map_zero s) (map_one s), Matrix.map_zero _ (map_zero s)]`. Simplify using the standard rewrite rules. Use `⟨fun y hy => ?_, fun h hh hfix => ?_⟩` and prove the remaining obligations. Establish `hb` using `hblk y 0`. Rewrite `hb` using `[hy]`.

Simplify using `only [Matrix.mul_zero, add_zero, Matrix.map_zero _ (map_zero s), transpose_zero, Matrix.zero_mul] at hb`. Rewrite using `[map_transpose_mul_rev, map_transpose_mul_rev]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (Qi.map s)ᵀ * ((Q.map s)ᵀ * J * Q) * Qi := by rw [hD, hb]`.

Use `_ = ((Qi.map s)ᵀ * (Q.map s)ᵀ) * J * (Q * Qi) := by simp only [Matrix.mul_assoc]`. Use `_ = J := by rw [h1s, h1, Matrix.one_mul, Matrix.mul_one]`. Use `set M : Matrix (ι ⊕ κ) (ι ⊕ κ) R := Qi * h * Q with hM`. Establish `hQM : Q * M = h * Q`. Rewrite using `[hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]`.

Establish `hhM : h = Q * M * Qi`. Rewrite using `[hQM, Matrix.mul_assoc, h1, Matrix.mul_one]`. Establish `hcol : ∀ x b, M x (Sum.inr b) = (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) R) x (Sum.inr b)`. Introduce `x b`. Rewrite using `[← h2, hM, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `congrFun (hfix b) i`. Establish `hMb : M = Matrix.fromBlocks M.toBlocks₁₁ 0 M.toBlocks₂₁ 1`. Use extensionality with `x z`.

Break down `z with z | z` into its components or cases. Apply the tactic sequence `rcases x with x | x <;> rfl`. Rewrite using `[hcol]`. Apply the tactic sequence `rcases x with x | x <;> simp [Matrix.one_apply]`. Establish `hU : (M.map s)ᵀ * Matrix.fromBlocks G 0 0 G' * M = Matrix.fromBlocks G 0 0 G'`.

Rewrite using `[← hD]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_transpose_mul_rev s Q M]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (Q.map s)ᵀ * ((h.map s)ᵀ * J * h) * Q := by`.

Rewrite using `[hQM, map_transpose_mul_rev]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hh]`. Rewrite `hU` using `[hMb, hblk, Matrix.fromBlocks_inj]`. Take `⟨ha, -, hc, -⟩` from `hU`.

Establish `hc0 : M.toBlocks₂₁ = 0`. Use `congrArg (G'⁻¹ * ·) hc` as an intermediate fact. Simplify `this` using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG']`. Rewrite `ha`, `hMb` using `[hc0]`. Use `⟨M.toBlocks₁₁, by simpa using ha, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hMb]`. Conclude with `hhM`.
-/
theorem unitary_stabiliser_orthogonal_summand :
    ∀ (R : Type) [CommRing R] (s : R →+* R) (N ι κ : Type) [Fintype N] [DecidableEq N] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (J : Matrix N N R) (G : Matrix ι ι R) (G' : Matrix κ κ R) (Q : Matrix N (ι ⊕ κ) R) (Qi : Matrix (ι ⊕ κ) N R), Q * Qi = 1 → Qi * Q = 1 → (Q.map s)ᵀ * J * Q = Matrix.fromBlocks G 0 0 G' → IsUnit G'.det → (∀ y : Matrix ι ι R, (y.map s)ᵀ * G * y = G → ((Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi).map s)ᵀ * J * (Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi) = J) ∧ ∀ h : Matrix N N R, (h.map s)ᵀ * J * h = J → (∀ b : κ, h *ᵥ (fun i => Q i (Sum.inr b)) = fun i => Q i (Sum.inr b)) → ∃ y : Matrix ι ι R, (y.map s)ᵀ * G * y = G ∧ h = Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi := by
  intro R _ s N ι κ _ _ _ _ _ _ J G G' Q Qi h1 h2 hD hG'
  have h1s : (Qi.map s)ᵀ * (Q.map s)ᵀ = 1 := by
    rw [← map_transpose_mul_rev, h1, Matrix.map_one _ (map_zero s) (map_one s), transpose_one]
  have hblk : ∀ (y : Matrix ι ι R) (c : Matrix κ ι R),
      ((Matrix.fromBlocks y 0 c (1 : Matrix κ κ R)).map s)ᵀ * Matrix.fromBlocks G 0 0 G' *
        Matrix.fromBlocks y 0 c (1 : Matrix κ κ R) =
      Matrix.fromBlocks ((y.map s)ᵀ * G * y + (c.map s)ᵀ * G' * c) ((c.map s)ᵀ * G') (G' * c) G' := by
    intro y c
    rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.map_one _ (map_zero s) (map_one s),
      Matrix.map_zero _ (map_zero s)]
    simp
  refine ⟨fun y hy => ?_, fun h hh hfix => ?_⟩
  · have hb := hblk y 0
    rw [hy] at hb
    simp only [Matrix.mul_zero, add_zero, Matrix.map_zero _ (map_zero s), transpose_zero,
      Matrix.zero_mul] at hb
    rw [map_transpose_mul_rev, map_transpose_mul_rev]
    calc _ = (Qi.map s)ᵀ * (((Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)).map s)ᵀ *
            ((Q.map s)ᵀ * J * Q) * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)) * Qi := by
          simp only [Matrix.mul_assoc]
      _ = (Qi.map s)ᵀ * ((Q.map s)ᵀ * J * Q) * Qi := by rw [hD, hb]
      _ = ((Qi.map s)ᵀ * (Q.map s)ᵀ) * J * (Q * Qi) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [h1s, h1, Matrix.one_mul, Matrix.mul_one]
  · set M : Matrix (ι ⊕ κ) (ι ⊕ κ) R := Qi * h * Q with hM
    have hQM : Q * M = h * Q := by
      rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    have hhM : h = Q * M * Qi := by
      rw [hQM, Matrix.mul_assoc, h1, Matrix.mul_one]
    have hcol : ∀ x b, M x (Sum.inr b) = (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) R) x (Sum.inr b) := by
      intro x b
      rw [← h2, hM, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      exact congrFun (hfix b) i
    have hMb : M = Matrix.fromBlocks M.toBlocks₁₁ 0 M.toBlocks₂₁ 1 := by
      ext x z
      rcases z with z | z
      · rcases x with x | x <;> rfl
      · rw [hcol]
        rcases x with x | x <;> simp [Matrix.one_apply]
    have hU : (M.map s)ᵀ * Matrix.fromBlocks G 0 0 G' * M = Matrix.fromBlocks G 0 0 G' := by
      rw [← hD]
      calc _ = ((Q * M).map s)ᵀ * J * (Q * M) := by
            rw [map_transpose_mul_rev s Q M]; simp only [Matrix.mul_assoc]
        _ = (Q.map s)ᵀ * ((h.map s)ᵀ * J * h) * Q := by
            rw [hQM, map_transpose_mul_rev]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hh]
    rw [hMb, hblk, Matrix.fromBlocks_inj] at hU
    obtain ⟨ha, -, hc, -⟩ := hU
    have hc0 : M.toBlocks₂₁ = 0 := by
      have := congrArg (G'⁻¹ * ·) hc
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG'] using this
    rw [hc0] at ha hMb
    refine ⟨M.toBlocks₁₁, by simpa using ha, ?_⟩
    rw [← hMb]
    exact hhM

end GlobalTheory
