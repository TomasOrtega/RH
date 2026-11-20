import Mathlib

namespace GlobalTheory.DiagonalConjugateExistence

/- English proof (translation)
Establish `hev : ∀ i, ∃ v : Fin n → ℂ, v ≠ 0 ∧ A.mulVec v = t i • v`. Introduce `i`. Establish `h0 : (Matrix.scalar (Fin n) (t i) - A).det = 0`. Rewrite using `[← Matrix.eval_charpoly, hA, Polynomial.eval_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp)`.

Take `⟨v, hv, hv0⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Rewrite `hv0` using `[Matrix.sub_mulVec, sub_eq_zero]`. Rewrite using `[← hv0]`. Use extensionality with `j`.

Simplify using `[Matrix.scalar_apply, Matrix.mulVec_diagonal]`. Use `choose v hv0 hv using hev`. Establish `hli : LinearIndependent ℂ v`. Use `Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) t ht v ?_` and prove the remaining obligations. Introduce `i`.

Use `⟨?_, hv0 i⟩` and prove the remaining obligations. Rewrite using `[Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hv]`. Establish `hu : IsUnit (Matrix.of fun i j => v j i : Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[← Matrix.linearIndependent_cols_iff_isUnit]`. Conclude with `hli`.

Use `⟨hu.unit, ?_⟩` and prove the remaining obligations. Rewrite using `[hu.unit_spec]`. Use extensionality with `i j`. Use `congrFun (hv j) i` as an intermediate fact. Rewrite using `[Matrix.mul_diagonal]`.

Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Rewrite using `[this, mul_comm]`.
-/
theorem exists_conj_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : Fin n → ℂ)
    (ht : Function.Injective t)
    (hA : Matrix.charpoly A = ∏ i : Fin n, (Polynomial.X - Polynomial.C (t i))) :
    ∃ P : GL (Fin n) ℂ, A * (P : Matrix (Fin n) (Fin n) ℂ)
      = (P : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal t := by
  have hev : ∀ i, ∃ v : Fin n → ℂ, v ≠ 0 ∧ A.mulVec v = t i • v := by
    intro i
    have h0 : (Matrix.scalar (Fin n) (t i) - A).det = 0 := by
      rw [← Matrix.eval_charpoly, hA, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv0
    rw [← hv0]
    ext j
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  choose v hv0 hv using hev
  have hli : LinearIndependent ℂ v := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) t ht v ?_
    intro i
    refine ⟨?_, hv0 i⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hv]
  have hu : IsUnit (Matrix.of fun i j => v j i : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]
  ext i j
  have := congrFun (hv j) i
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [this, mul_comm]

end GlobalTheory.DiagonalConjugateExistence
