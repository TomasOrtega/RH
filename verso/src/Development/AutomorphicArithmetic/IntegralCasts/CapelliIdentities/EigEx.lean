import Mathlib

/- English proof (translation)
Introduce `k _ n P a h i`. Establish `hroot : P.charpoly.eval (a i) = 0`. Rewrite using `[h, Polynomial.eval_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp)`. Rewrite `hroot` using `[Matrix.eval_charpoly]`.

Take `⟨v, hv, hv0⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hroot`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Rewrite `hv0` using `[Matrix.sub_mulVec, sub_eq_zero]`. Rewrite using `[← hv0]`. Use extensionality with `j`.

Simplify using `[Matrix.mulVec_diagonal]`.
-/
theorem UpperTheory.Reformulated.B.Qi37.eig_ex :
    ∀ {k : Type} [inst : Field k] {n : ℕ} (P : Matrix (Fin n) (Fin n) k)
    (a : Fin n → k),
    P.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : k → Polynomial k) (a i)) →
      ∀ (i : Fin n), ∃ (v : Fin n → k), v ≠ (0 : Fin n → k) ∧ P.mulVec v = a i • v := by
  intro k _ n P a h i
  have hroot : P.charpoly.eval (a i) = 0 := by
    rw [h, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at hv0
  rw [← hv0]
  ext j
  simp [Matrix.mulVec_diagonal]
