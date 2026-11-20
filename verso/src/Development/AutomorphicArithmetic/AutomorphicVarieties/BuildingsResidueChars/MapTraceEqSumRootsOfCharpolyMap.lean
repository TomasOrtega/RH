import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

/- English proof (translation)
Introduce `k _ φ B`. Use `⟨fun M hM => ?_, fun M hM => ?_⟩` and prove the remaining obligations. Rewrite using `[AddMonoidHom.map_trace, Matrix.trace_eq_sum_roots_charpoly, Matrix.charpoly_map, hM, Polynomial.roots_multiset_prod_X_sub_C]`. Establish `hN : (M.map φ).charpoly = (B.map fun b => X - C b).prod` using `by rw [Matrix.charpoly_map, hM]`. Establish `ht : (M.map φ).trace = B.sum`.

Rewrite using `[Matrix.trace_eq_sum_roots_charpoly, hN, Polynomial.roots_multiset_prod_X_sub_C]`. Establish `hc : B.card = 2`. Use `Matrix.charpoly_natDegree_eq_dim (M.map φ)` as an intermediate fact. Rewrite `this` using `[hN, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]`. Simplify using `using this`.

Take `⟨b1, b2, rfl⟩` from `Multiset.card_eq_two.mp hc`. Establish `h0` using `Matrix.aeval_self_charpoly (M.map φ)`. Rewrite `h0` using `[hN]`. Simplify using `only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h0`. Use `set N := M.map φ with hNdef`.

Establish `hCH : N * N = (b1 + b2) • N - (b1 * b2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)`. Establish `e : N * N - ((b1 + b2) • N - (b1 * b2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0`. Rewrite using `[← h0]`. Simplify using `only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]`. Use `module`.

Conclude with `sub_eq_zero.mp e`. Establish `key : ∀ h : ℕ, (N ^ h).trace = b1 ^ h + b2 ^ h ∧ (N ^ (h + 1)).trace = b1 ^ (h + 1) + b2 ^ (h + 1)`. Introduce `h`. Proceed by induction on `h with`. Consider the case `zero`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.trace_one]`. Evaluate the numerical expressions. Simplify `ht` using `[add_comm]`. Consider the case `succ h ih`.

Use `⟨ih.2, ?_⟩` and prove the remaining obligations. Establish `e : N ^ (h + 1 + 1) = (b1 + b2) • N ^ (h + 1) - (b1 * b2) • N ^ h`. Rewrite using `[pow_succ, pow_succ, mul_assoc, hCH, mul_sub, mul_smul_comm, mul_smul_comm, mul_one, ← pow_succ]`. Rewrite using `[e, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, ih.1, ih.2, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `h`. Rewrite using `[AddMonoidHom.map_trace, Matrix.map_pow, (key h).1]`. Simplify using `[add_comm]`.
-/
theorem UpperTheory.map_trace_eq_sum_roots_of_charpoly_map :
    ∀ (k : Type) [Field k] (φ : k →+* ℂ) (B : Multiset ℂ), (∀ M : Matrix (Fin 3) (Fin 3) k, M.charpoly.map φ = (B.map fun b => X - C b).prod → φ M.trace = B.sum) ∧ ∀ M : Matrix (Fin 2) (Fin 2) k, M.charpoly.map φ = (B.map fun b => X - C b).prod → ∀ h : ℕ, φ (M ^ h).trace = (B.map (· ^ h)).sum := by
  intro k _ φ B
  refine ⟨fun M hM => ?_, fun M hM => ?_⟩
  · rw [AddMonoidHom.map_trace, Matrix.trace_eq_sum_roots_charpoly, Matrix.charpoly_map, hM,
      Polynomial.roots_multiset_prod_X_sub_C]
  · have hN : (M.map φ).charpoly = (B.map fun b => X - C b).prod := by rw [Matrix.charpoly_map, hM]
    have ht : (M.map φ).trace = B.sum := by
      rw [Matrix.trace_eq_sum_roots_charpoly, hN, Polynomial.roots_multiset_prod_X_sub_C]
    have hc : B.card = 2 := by
      have := Matrix.charpoly_natDegree_eq_dim (M.map φ)
      rw [hN, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at this
      simpa using this
    obtain ⟨b1, b2, rfl⟩ := Multiset.card_eq_two.mp hc
    have h0 := Matrix.aeval_self_charpoly (M.map φ)
    rw [hN] at h0
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
      Multiset.prod_singleton, map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h0
    set N := M.map φ with hNdef
    have hCH : N * N = (b1 + b2) • N - (b1 * b2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      have e : N * N - ((b1 + b2) • N - (b1 * b2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
        rw [← h0]
        simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
        module
      exact sub_eq_zero.mp e
    have key : ∀ h : ℕ, (N ^ h).trace = b1 ^ h + b2 ^ h ∧
        (N ^ (h + 1)).trace = b1 ^ (h + 1) + b2 ^ (h + 1) := by
      intro h
      induction h with
      | zero =>
        refine ⟨?_, ?_⟩
        · simp [Matrix.trace_one]
          norm_num
        · simpa [add_comm] using ht
      | succ h ih =>
        refine ⟨ih.2, ?_⟩
        have e : N ^ (h + 1 + 1) = (b1 + b2) • N ^ (h + 1) - (b1 * b2) • N ^ h := by
          rw [pow_succ, pow_succ, mul_assoc, hCH, mul_sub, mul_smul_comm, mul_smul_comm, mul_one,
            ← pow_succ]
        rw [e, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, ih.1, ih.2, smul_eq_mul,
          smul_eq_mul]
        ring
    intro h
    rw [AddMonoidHom.map_trace, Matrix.map_pow, (key h).1]
    simp [add_comm]
