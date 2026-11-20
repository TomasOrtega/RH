import Mathlib
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]`.
-/
private lemma dot_transpose_mulVec' {m n : Type} [Fintype m] [Fintype n]
    (X : Matrix m n ℂ) (u : n → ℂ) (v : m → ℂ) : u ⬝ᵥ Xᵀ *ᵥ v = v ⬝ᵥ X *ᵥ u := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

/- English proof (translation)
Introduce `S T w u`. Establish `hM : IsUnit (1 - B * C).det` using `by rwa [det_one_sub_mul_comm]`. Use `set M := (1 - B * C)⁻¹ with hMdef`. Use `set N := (1 - C * B)⁻¹ with hNdef`. Establish `hM1 : M * (1 - B * C) = 1` using `nonsing_inv_mul _ hM`.

Establish `hM2 : (1 - B * C) * M = 1` using `mul_nonsing_inv _ hM`. Establish `hN1 : N * (1 - C * B) = 1` using `nonsing_inv_mul _ hN`. Establish `hN2 : (1 - C * B) * N = 1` using `mul_nonsing_inv _ hN`. Establish `hMB : B * N = M * B`. Establish `h : B * (1 - C * B) = (1 - B * C) * B`.

Simplify using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, hM1, Matrix.one_mul]`. Use `_ = M * B := by`. Rewrite using `[← h, Matrix.mul_assoc, Matrix.mul_assoc, hN2, Matrix.mul_one]`.

Establish `hCM : C * M = N * C`. Establish `h : C * (1 - B * C) = (1 - C * B) * C`. Simplify using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, hN1, Matrix.one_mul]`.

Use `_ = N * C := by`. Rewrite using `[← h, Matrix.mul_assoc, Matrix.mul_assoc, hM2, Matrix.mul_one]`. Establish `hMBC : B * (N * C) = M - 1`. Rewrite using `[← Matrix.mul_assoc, hMB, ← hM1, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws.

Establish `hNCB : N * C * B = N - 1`. Rewrite using `[← hN1, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Establish `hinv : (1 - T * S)⁻¹ = fromBlocks M 0 0 Nᵀ`. Apply `inv_eq_left_inv` to reduce the goal to its premises.

Establish `h1 : (1 - T * S) = fromBlocks (1 - B * C) 0 0 (1 - C * B)ᵀ`. Simplify using `only [T, S, fromBlocks_multiply, ← fromBlocks_one]`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [transpose_mul, one_apply, eq_comm]`. Rewrite using `[h1, fromBlocks_multiply, ← transpose_mul, hM1, hN2]`. Simplify using the standard rewrite rules.

Establish `hw : w = Sum.elim (M *ᵥ (c + B *ᵥ b)) (Nᵀ *ᵥ (d + Bᵀ *ᵥ a))`. Establish `h : Sum.elim c d + T *ᵥ Sum.elim a b = Sum.elim (c + B *ᵥ b) (d + Bᵀ *ᵥ a)`. Simplify using `only [T, fromBlocks_mulVec]`. Apply the tactic sequence `ext (i | i) <;> simp`. Simplify using `only [w]`.

Rewrite using `[hinv, h, fromBlocks_mulVec]`. Simplify using the standard rewrite rules. Establish `hu : u = Sum.elim (a + (N * C)ᵀ *ᵥ (d + Bᵀ *ᵥ a)) (b + (N * C) *ᵥ (c + B *ᵥ b))`. Simplify using `only [u, S]`. Rewrite using `[hw, fromBlocks_mulVec]`.

Simplify using `only [Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_mulVec, ← transpose_mul, hCM]`. Apply the tactic sequence `ext (i | i) <;> simp`. Rewrite using `[hu, hw, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim]`. Simplify using `only [dotProduct_add, mulVec_add, mulVec_mulVec, ← transpose_mul, dot_transpose_mulVec', hMB, hMBC, hNCB, sub_mulVec, one_mulVec, dotProduct_sub]`. Rewrite using `[dotProduct_comm c a]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaussian_phase_critical_value_blocks_general {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (C : Matrix n m ℂ) (B : Matrix m n ℂ)
    (a c : m → ℂ) (b d : n → ℂ) (hN : IsUnit (1 - C * B).det) :
    let S : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 0 Cᵀ C 0
    let T : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 0 B Bᵀ 0
    let w : m ⊕ n → ℂ := (1 - T * S)⁻¹ *ᵥ (Sum.elim c d + T *ᵥ Sum.elim a b)
    let u : m ⊕ n → ℂ := Sum.elim a b + S *ᵥ w
    1 / 2 * (Sum.elim a b ⬝ᵥ w + Sum.elim c d ⬝ᵥ u)
      = a ⬝ᵥ (1 - B * C)⁻¹ *ᵥ c + d ⬝ᵥ (1 - C * B)⁻¹ *ᵥ b
        + a ⬝ᵥ ((1 - B * C)⁻¹ * B) *ᵥ b + d ⬝ᵥ ((1 - C * B)⁻¹ * C) *ᵥ c := by
  intro S T w u
  have hM : IsUnit (1 - B * C).det := by rwa [det_one_sub_mul_comm]
  set M := (1 - B * C)⁻¹ with hMdef
  set N := (1 - C * B)⁻¹ with hNdef
  have hM1 : M * (1 - B * C) = 1 := nonsing_inv_mul _ hM
  have hM2 : (1 - B * C) * M = 1 := mul_nonsing_inv _ hM
  have hN1 : N * (1 - C * B) = 1 := nonsing_inv_mul _ hN
  have hN2 : (1 - C * B) * N = 1 := mul_nonsing_inv _ hN
  have hMB : B * N = M * B := by
    have h : B * (1 - C * B) = (1 - B * C) * B := by
      simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    calc B * N = M * ((1 - B * C) * B) * N := by
          rw [← Matrix.mul_assoc, hM1, Matrix.one_mul]
      _ = M * B := by
          rw [← h, Matrix.mul_assoc, Matrix.mul_assoc, hN2, Matrix.mul_one]
  have hCM : C * M = N * C := by
    have h : C * (1 - B * C) = (1 - C * B) * C := by
      simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    calc C * M = N * ((1 - C * B) * C) * M := by
          rw [← Matrix.mul_assoc, hN1, Matrix.one_mul]
      _ = N * C := by
          rw [← h, Matrix.mul_assoc, Matrix.mul_assoc, hM2, Matrix.mul_one]
  have hMBC : B * (N * C) = M - 1 := by
    rw [← Matrix.mul_assoc, hMB, ← hM1, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hNCB : N * C * B = N - 1 := by
    rw [← hN1, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hinv : (1 - T * S)⁻¹ = fromBlocks M 0 0 Nᵀ := by
    apply inv_eq_left_inv
    have h1 : (1 - T * S) = fromBlocks (1 - B * C) 0 0 (1 - C * B)ᵀ := by
      simp only [T, S, fromBlocks_multiply, ← fromBlocks_one]
      ext (i | i) (j | j) <;> simp [transpose_mul, one_apply, eq_comm]
    rw [h1, fromBlocks_multiply, ← transpose_mul, hM1, hN2]
    simp
  have hw : w = Sum.elim (M *ᵥ (c + B *ᵥ b)) (Nᵀ *ᵥ (d + Bᵀ *ᵥ a)) := by
    have h : Sum.elim c d + T *ᵥ Sum.elim a b = Sum.elim (c + B *ᵥ b) (d + Bᵀ *ᵥ a) := by
      simp only [T, fromBlocks_mulVec]
      ext (i | i) <;> simp
    simp only [w]
    rw [hinv, h, fromBlocks_mulVec]
    simp
  have hu : u = Sum.elim (a + (N * C)ᵀ *ᵥ (d + Bᵀ *ᵥ a)) (b + (N * C) *ᵥ (c + B *ᵥ b)) := by
    simp only [u, S]
    rw [hw, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr,
      mulVec_mulVec, ← transpose_mul, hCM]
    ext (i | i) <;> simp
  rw [hu, hw, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim]
  simp only [dotProduct_add, mulVec_add, mulVec_mulVec, ← transpose_mul, dot_transpose_mulVec',
    hMB, hMBC, hNCB, sub_mulVec, one_mulVec, dotProduct_sub]
  rw [dotProduct_comm c a]
  ring

/- English proof (translation)
Introduce `_ _ A B a c b d h` and use `gaussian_phase_critical_value_blocks_general Aᴴ B a c b d h`.
-/
theorem gaussian_phase_critical_value_blocks :
    ∀ (P Q : ℕ) (A B : Matrix (Fin P) (Fin Q) ℂ) (a c : Fin P → ℂ) (b d : Fin Q → ℂ), IsUnit (1 - Aᴴ * B).det → let S : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 Aᴴᵀ Aᴴ 0; let T : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 B Bᵀ 0; let w : Fin P ⊕ Fin Q → ℂ := (1 - T * S)⁻¹ *ᵥ (Sum.elim c d + T *ᵥ Sum.elim a b); let u : Fin P ⊕ Fin Q → ℂ := Sum.elim a b + S *ᵥ w; 1 / 2 * (Sum.elim a b ⬝ᵥ w + Sum.elim c d ⬝ᵥ u) = a ⬝ᵥ (1 - B * Aᴴ)⁻¹ *ᵥ c + d ⬝ᵥ (1 - Aᴴ * B)⁻¹ *ᵥ b + a ⬝ᵥ ((1 - B * Aᴴ)⁻¹ * B) *ᵥ b + d ⬝ᵥ ((1 - Aᴴ * B)⁻¹ * Aᴴ) *ᵥ c :=
  fun _ _ A B a c b d h => gaussian_phase_critical_value_blocks_general Aᴴ B a c b d h

end GlobalTheory
