import Mathlib

open Matrix

namespace GlobalTheory.CompanionTheory.Matrixlemmas

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c, ξ c ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Conclude with `hξ (funext fun i => by_contra fun hi => hcon ⟨i, hi⟩)`. Set `σ : Equiv.Perm (Fin (n + 1))` to `Equiv.swap c (Fin.last n)`. Set `U : Matrix (Fin (n + 1)) (Fin (n + 1)) k` to `(1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow c ξ`.

Establish `hU : U.det = ξ c`. Establish `hT : Uᵀ = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol c ξ`. Simplify using `only [U]`. Rewrite using `[← Matrix.updateCol_transpose, Matrix.transpose_one]`. Rewrite using `[← Matrix.det_transpose, hT, ← Matrix.cramer_apply, Matrix.cramer_one]`.

Both sides reduce to the same expression. Set `h : Matrix (Fin (n + 1)) (Fin (n + 1)) k` to `U.submatrix σ id`. Establish `hdet : IsUnit h.det`. Establish `: h.det = Equiv.Perm.sign σ * U.det` using `Matrix.det_permute σ U`. Rewrite using `[this, hU]`.

Use `IsUnit.mul ?_ (isUnit_iff_ne_zero.mpr hc)` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]`. Establish `hrow : Matrix.vecMul (Pi.single (Fin.last n) 1) h = ξ`. Rewrite using `[Matrix.single_one_vecMul]`. Use function extensionality and compare the values at `j`.

Simplify using `[h, U, σ]`. Use `⟨(Matrix.nonsingInvUnit h hdet)⁻¹, ?_⟩` and prove the remaining obligations. Establish `hinv : h * (((Matrix.nonsingInvUnit h hdet)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 1` using `(Matrix.nonsingInvUnit h hdet).mul_inv`. Use `conv_lhs => rw [← hrow]`. Rewrite using `[Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]`.
-/
theorem exists_GL_vecMul_eq_single_last {k : Type} [Field k] (n : ℕ) (ξ : Fin (n + 1) → k) (hξ : ξ ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k,
      Matrix.vecMul ξ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = Pi.single (Fin.last n) 1 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c, ξ c ≠ 0 := by
    by_contra hcon
    exact hξ (funext fun i => by_contra fun hi => hcon ⟨i, hi⟩)
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap c (Fin.last n)
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow c ξ
  have hU : U.det = ξ c := by
    have hT : Uᵀ = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol c ξ := by
      simp only [U]
      rw [← Matrix.updateCol_transpose, Matrix.transpose_one]
    rw [← Matrix.det_transpose, hT, ← Matrix.cramer_apply, Matrix.cramer_one]
    rfl
  let h : Matrix (Fin (n + 1)) (Fin (n + 1)) k := U.submatrix σ id
  have hdet : IsUnit h.det := by
    have : h.det = Equiv.Perm.sign σ * U.det := Matrix.det_permute σ U
    rw [this, hU]
    refine IsUnit.mul ?_ (isUnit_iff_ne_zero.mpr hc)
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]
  have hrow : Matrix.vecMul (Pi.single (Fin.last n) 1) h = ξ := by
    rw [Matrix.single_one_vecMul]
    funext j
    simp [h, U, σ]
  refine ⟨(Matrix.nonsingInvUnit h hdet)⁻¹, ?_⟩
  have hinv : h * (((Matrix.nonsingInvUnit h hdet)⁻¹ : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 1 :=
    (Matrix.nonsingInvUnit h hdet).mul_inv
  conv_lhs => rw [← hrow]
  rw [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]

end GlobalTheory.CompanionTheory.Matrixlemmas
