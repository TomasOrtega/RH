import Mathlib

open Polynomial in
/- English proof (translation)
Rewrite using `[← List.prod_ofFn, map_list_prod, List.map_ofFn]`. Use `congrArg _ (congrArg _ (funext fun k => ?_))` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Apply the tactic sequence `split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]`.
-/
private theorem UpperTheory.V.Th.product_factors_aeval {S : Type} [CommRing S] {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) S) (V : Fin n → S) (i : Fin n) :
    (List.ofFn fun k => if k = i then 1 else Q - V k • (1 : Matrix (Fin n) (Fin n) S)).prod
      = aeval Q (∏ k, if k = i then (1 : S[X]) else X - C (V k)) := by
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  refine congrArg _ (congrArg _ (funext fun k => ?_))
  simp only [Function.comp_apply]
  split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]

open Polynomial in
/- English proof (translation)
Introduce `K S _ _ f n N E P T α β U i hN hU h`. Establish `hsm : ∀ a : K, (a • (1 : Matrix (Fin n) (Fin n) K)).map f = f a • (1 : Matrix (Fin n) (Fin n) S)`. Introduce `a`. Use extensionality with `p q`. Apply the tactic sequence `by_cases hpq : p = q <;> simp [Matrix.one_apply, hpq]`.

Establish `e1 : (⇑f.mapMatrix ∘ fun k => if k = i then 1 else P - α k • (1 : Matrix (Fin n) (Fin n) K)) = fun k => if k = i then 1 else P.map f - f (α k) • (1 : Matrix (Fin n) (Fin n) S)`. Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp_apply]`. Use `split_ifs`. Simplify using the standard rewrite rules.

Simplify using `[Matrix.map_sub, hsm]`. Establish `hL : (List.ofFn fun k => if k = i then 1 else P.map f - f (α k) • (1 : Matrix (Fin n) (Fin n) S)).prod * (T.map f - f β • (1 : Matrix (Fin n) (Fin n) S)) = 0`. Establish `h2` using `congrArg f.mapMatrix h`. Rewrite `h2` using `[map_mul, map_list_prod, List.map_ofFn, map_zero, e1]`. Establish `e2 : f.mapMatrix (T - β • (1 : Matrix (Fin n) (Fin n) K)) = T.map f - f β • (1 : Matrix (Fin n) (Fin n) S)`.

Simplify using `[Matrix.map_sub, hsm]`. Rewrite `h2` using `[e2]`. Conclude with `h2`. Establish `hdvd : (∏ k, if k = i then (1 : S[X]) else X - C (f (α k))) ∣ (∏ k, if k = i then (1 : S[X]) else X - C (U k)) ^ (E + 1)`. Rewrite using `[← Finset.prod_pow]`.

Apply `Finset.prod_dvd_prod_of_dvd` to reduce the goal to its premises. Introduce `k _`. Use `split_ifs`. Simplify using the standard rewrite rules. Rewrite using `[Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_pow]`.

Simplify using `only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]`. Establish `: (f (α k) - U k) ^ N = 0`. Rewrite using `[← neg_sub, neg_pow, hU k, mul_zero]`. Conclude with `pow_eq_zero_of_le hN this`. Take `⟨G, hG⟩` from `hdvd`.

Rewrite using `[UpperTheory.V.Th.product_factors_aeval, ← map_pow, hG, mul_comm, map_mul, mul_assoc, ← UpperTheory.V.Th.product_factors_aeval (P.map f) (fun k => f (α k)) i, hL, mul_zero]`.
-/
theorem UpperTheory.V.Th.powRel :
    ∀ (K S : Type) [CommRing K] [CommRing S] (f : K →+* S) (n N E : ℕ) (P T : Matrix (Fin n) (Fin n) K) (α : Fin n → K) (β : K) (U : Fin n → S) (i : Fin n), N ≤ E + 1 → (∀ k, (U k - f (α k)) ^ N = 0) → (List.ofFn fun k => if k = i then 1 else P - α k • (1 : Matrix (Fin n) (Fin n) K)).prod * (T - β • (1 : Matrix (Fin n) (Fin n) K)) = 0 → (List.ofFn fun k => if k = i then 1 else P.map f - U k • (1 : Matrix (Fin n) (Fin n) S)).prod ^ (E + 1) * (T.map f - f β • (1 : Matrix (Fin n) (Fin n) S)) = 0 := by
  intro K S _ _ f n N E P T α β U i hN hU h
  have hsm : ∀ a : K, (a • (1 : Matrix (Fin n) (Fin n) K)).map f = f a • (1 : Matrix (Fin n) (Fin n) S) := by
    intro a
    ext p q
    by_cases hpq : p = q <;> simp [Matrix.one_apply, hpq]
  have e1 : (⇑f.mapMatrix ∘ fun k => if k = i then 1 else P - α k • (1 : Matrix (Fin n) (Fin n) K))
      = fun k => if k = i then 1 else P.map f - f (α k) • (1 : Matrix (Fin n) (Fin n) S) := by
    funext k
    simp only [Function.comp_apply]
    split_ifs
    · simp
    · simp [Matrix.map_sub, hsm]
  have hL : (List.ofFn fun k => if k = i then 1 else P.map f - f (α k) • (1 : Matrix (Fin n) (Fin n) S)).prod
      * (T.map f - f β • (1 : Matrix (Fin n) (Fin n) S)) = 0 := by
    have h2 := congrArg f.mapMatrix h
    rw [map_mul, map_list_prod, List.map_ofFn, map_zero, e1] at h2
    have e2 : f.mapMatrix (T - β • (1 : Matrix (Fin n) (Fin n) K)) = T.map f - f β • (1 : Matrix (Fin n) (Fin n) S) := by
      simp [Matrix.map_sub, hsm]
    rw [e2] at h2
    exact h2
  have hdvd : (∏ k, if k = i then (1 : S[X]) else X - C (f (α k))) ∣
      (∏ k, if k = i then (1 : S[X]) else X - C (U k)) ^ (E + 1) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_dvd_prod_of_dvd
    intro k _
    split_ifs
    · simp
    · rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_pow]
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      have : (f (α k) - U k) ^ N = 0 := by
        rw [← neg_sub, neg_pow, hU k, mul_zero]
      exact pow_eq_zero_of_le hN this
  obtain ⟨G, hG⟩ := hdvd
  rw [UpperTheory.V.Th.product_factors_aeval, ← map_pow, hG, mul_comm, map_mul, mul_assoc,
    ← UpperTheory.V.Th.product_factors_aeval (P.map f) (fun k => f (α k)) i, hL, mul_zero]
