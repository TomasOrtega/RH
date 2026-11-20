import Mathlib

open Matrix

namespace GlobalTheory

/- English proof (translation)
Use extensionality with `j k`. Take `⟨k, rfl⟩` from `finSumFinEquiv.surjective k`. Break down `k with k | k` into its components or cases. Simplify using `[Matrix.one_apply, Fin.ext_iff]`. Use `j.2` as an intermediate fact.

Establish `h : (j : ℕ) ≠ N + k` using `by omega`. Simplify using `[h]`.
-/
theorem rectId_eq_fromCols (R : Type) [Semiring R] (N r : ℕ) :
    (Matrix.of fun (j : Fin N) (k : Fin (N + r)) => if (j : ℕ) = (k : ℕ) then (1 : R) else 0)
      = (Matrix.fromCols (1 : Matrix (Fin N) (Fin N) R) (0 : Matrix (Fin N) (Fin r) R)).submatrix
          id finSumFinEquiv.symm := by
  ext j k
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  rcases k with k | k
  · simp [Matrix.one_apply, Fin.ext_iff]
  · have := j.2
    have h : (j : ℕ) ≠ N + k := by omega
    simp [h]

/- English proof (translation)
Take `⟨r, rfl⟩` from `Nat.exists_eq_add_of_le hN`. Set `E : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin (N + r)) (Fin (N + r)) ℂ` to `fun B => (Matrix.fromBlocks B 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm`. Establish `Edet : ∀ B, (E B).det = B.det` using `fun B => by`. Simplify using `[E, Matrix.det_submatrix_equiv_self]`. Establish `Emul : ∀ B C, E (B * C) = E B * E C` using `fun B C => by`.

Simplify using `[E, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`. Establish `Eone : E 1 = 1` using `by simp [E]`. Establish `Estar : ∀ B, E (star B) = star (E B)` using `fun B => by`. Simplify using `[E, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]`. Establish `Emap : ∀ B, E (B.map (starRingEnd ℂ)) = (E B).map (starRingEnd ℂ)` using `fun B => by`.

Simplify using `only [E]`. Rewrite using `[← Matrix.submatrix_map, Matrix.fromBlocks_map]`. Simplify using the standard rewrite rules. Use `⟨fun σ => M.map σ * E (A σ), fun σ => ?_, fun σ => ?_, fun σ => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, Edet]`.

Use `mul_ne_zero ?_ (hA σ)` and prove the remaining obligations. Establish `h` using `σ.map_det M`. Rewrite `h` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← h]`. Conclude with `(_root_.map_ne_zero σ).2 hM`.

Take `⟨U, hUm, hUe⟩` from `hU σ`. Use `⟨E U, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hUm`, the goal using `[Matrix.mem_unitaryGroup_iff]`. Rewrite using `[← Estar, ← Emul, hUm, Eone]`. Simplify using `only`.

Rewrite using `[hUe, Emul, Emap, Matrix.map_mul, Matrix.map_map, Matrix.mul_assoc]`. Both sides reduce to the same expression. Simplify using `only`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.map_mul, hg]`. Establish `h1 : (Matrix.of fun (j : Fin N) (k : Fin (N + r)) => if (j : ℕ) = (k : ℕ) then (1 : K) else 0).map σ = (Matrix.of fun (j : Fin N) (k : Fin (N + r)) => if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0)`.

Use extensionality with `j k`. Simplify using `[apply_ite σ]`. Rewrite using `[h1, rectId_eq_fromCols]`. Simplify using `only [E]`. Rewrite using `[Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]`.

Use extensionality with `j k`. Take `⟨k, rfl⟩` from `finSumFinEquiv.surjective k`. Break down `k with k | k` into its components or cases. Simplify using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `[Matrix.mul_apply]`.
-/
theorem exists_frames_extend (K : Type) [Field K] (N n : ℕ) (g : Matrix (Fin N) (Fin n) K)
    (M : Matrix (Fin n) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (hN : N ≤ n)
    (hM : M.det ≠ 0)
    (hg : g * M = (Matrix.of fun (j : Fin N) (k : Fin n) =>
      if (j : ℕ) = (k : ℕ) then (1 : K) else 0))
    (hA : ∀ σ, (A σ).det ≠ 0)
    (hU : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ,
      A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U) :
    ∃ A' : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, (∀ σ, (A' σ).det ≠ 0) ∧
      (∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
        A' ((starRingEnd ℂ).comp σ) = (A' σ).map (starRingEnd ℂ) * U) ∧
      ∀ σ : K →+* ℂ, g.map σ * A' σ = A σ * (Matrix.of fun (j : Fin N) (k : Fin n) =>
        if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hN
  let E : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin (N + r)) (Fin (N + r)) ℂ := fun B =>
    (Matrix.fromBlocks B 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm
  have Edet : ∀ B, (E B).det = B.det := fun B => by
    simp [E, Matrix.det_submatrix_equiv_self]
  have Emul : ∀ B C, E (B * C) = E B * E C := fun B C => by
    simp [E, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  have Eone : E 1 = 1 := by simp [E]
  have Estar : ∀ B, E (star B) = star (E B) := fun B => by
    simp [E, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.fromBlocks_conjTranspose]
  have Emap : ∀ B, E (B.map (starRingEnd ℂ)) = (E B).map (starRingEnd ℂ) := fun B => by
    simp only [E]
    rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
    simp
  refine ⟨fun σ => M.map σ * E (A σ), fun σ => ?_, fun σ => ?_, fun σ => ?_⟩
  · rw [Matrix.det_mul, Edet]
    refine mul_ne_zero ?_ (hA σ)
    have h := σ.map_det M
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]
    exact (_root_.map_ne_zero σ).2 hM
  · obtain ⟨U, hUm, hUe⟩ := hU σ
    refine ⟨E U, ?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff] at hUm ⊢
      rw [← Estar, ← Emul, hUm, Eone]
    · simp only
      rw [hUe, Emul, Emap, Matrix.map_mul, Matrix.map_map, Matrix.mul_assoc]
      rfl
  · simp only
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, hg]
    have h1 : (Matrix.of fun (j : Fin N) (k : Fin (N + r)) =>
        if (j : ℕ) = (k : ℕ) then (1 : K) else 0).map σ
        = (Matrix.of fun (j : Fin N) (k : Fin (N + r)) =>
        if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) := by
      ext j k
      simp [apply_ite σ]
    rw [h1, rectId_eq_fromCols]
    simp only [E]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
    ext j k
    obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
    rcases k with k | k
    · simp [Matrix.mul_apply, Matrix.one_apply]
    · simp [Matrix.mul_apply]

end GlobalTheory
