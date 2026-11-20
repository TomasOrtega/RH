import Mathlib

/- English proof (translation)
Introduce `K _ r N h k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Introduce `hk`. Distinguish the cases in `hkr : k ≤ r`.

Conclude with `h k hk hkr`. Take `⟨m, rfl⟩ : ∃ m, k = m + 1 + r` from `⟨k - r - 1, by omega⟩`. Establish `hd : N.charpoly.natDegree = r`. Rewrite using `[Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Establish `hc : N.charpoly.coeff r = 1`.

Use `(Matrix.charpoly_monic N).coeff_natDegree` as an intermediate fact. Rewrite `this` using `[hd]`. Then use the resulting hypothesis. Establish `hCH` using `Matrix.aeval_self_charpoly N`. Rewrite `hCH` using `[Polynomial.aeval_eq_sum_range, hd, Finset.sum_range_succ, hc, one_smul]`. Establish `h2` using `congrArg (fun A => Matrix.trace (N ^ (m + 1) * A)) hCH`.

Simplify using `only [mul_add, Finset.mul_sum, Matrix.mul_smul, ← pow_add, mul_zero, Matrix.trace_zero, Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul] at h2`. Rewrite `h2` using `[Finset.sum_eq_zero, zero_add]`. Conclude with `h2`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`.

Rewrite using `[ih (m + 1 + i) (by omega) (by omega), smul_zero]`.
-/
theorem UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim.{u_1} :
    ∀ {K : Type u_1}
    [inst : Field K] (r : ℕ) (N : Matrix (Fin r) (Fin r) K),
    (∀ (k : ℕ), (1 : ℕ) ≤ k → k ≤ r → (N ^ k).trace = (0 : K)) → ∀ (k : ℕ), (1 : ℕ) ≤ k → (N ^ k).trace = (0 : K) := by
  intro K _ r N h k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hkr : k ≤ r
    · exact h k hk hkr
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 + r := ⟨k - r - 1, by omega⟩
      have hd : N.charpoly.natDegree = r := by
        rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      have hc : N.charpoly.coeff r = 1 := by
        have := (Matrix.charpoly_monic N).coeff_natDegree
        rwa [hd] at this
      have hCH := Matrix.aeval_self_charpoly N
      rw [Polynomial.aeval_eq_sum_range, hd, Finset.sum_range_succ, hc, one_smul] at hCH
      have h2 := congrArg (fun A => Matrix.trace (N ^ (m + 1) * A)) hCH
      simp only [mul_add, Finset.mul_sum, Matrix.mul_smul, ← pow_add, mul_zero, Matrix.trace_zero,
        Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul] at h2
      rw [Finset.sum_eq_zero, zero_add] at h2
      · exact h2
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [ih (m + 1 + i) (by omega) (by omega), smul_zero]
