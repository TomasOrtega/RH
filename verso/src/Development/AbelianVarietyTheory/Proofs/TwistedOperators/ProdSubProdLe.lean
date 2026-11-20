import Mathlib

namespace GlobalTheory.ProdSubProdBound

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.prod_insert hj]`. Establish `hB : v (∏ i ∈ s, b i) ≤ 1`.

Rewrite using `[map_prod]`. Conclude with `Finset.prod_le_one' (fun i _ => hb i)`. Establish `e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i = a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i` using `by ring`. Rewrite using `[e]`. Use `(v.map_add _ _).trans (max_le ?_ ?_)` and prove the remaining obligations.

Rewrite using `[v.map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[v.map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem prod_sub_prod_le {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ}
    {ι : Type} (s : Finset ι) {c : Γ} {a b : ι → K}
    (ha : ∀ i, v (a i) ≤ 1) (hb : ∀ i, v (b i) ≤ 1) (hab : ∀ i, v (a i - b i) ≤ c) :
    v (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    have hB : v (∏ i ∈ s, b i) ≤ 1 := by
      rw [map_prod]; exact Finset.prod_le_one' (fun i _ => hb i)
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i
        = a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [e]
    refine (v.map_add _ _).trans (max_le ?_ ?_)
    · rw [v.map_mul]
      calc v (a j) * v (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ 1 * c := mul_le_mul' (ha j) ih
        _ = c := one_mul c
    · rw [v.map_mul]
      calc v (a j - b j) * v (∏ i ∈ s, b i) ≤ c * 1 := mul_le_mul' (hab j) hB
        _ = c := mul_one c

/- English proof (translation)
Introduce `s` and use `prod_sub_prod_le s`.
-/
theorem main : ∀ {K Γ : Type} [inst : Field K] [inst_1 : LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ} {ι : Type} (s : Finset ι) {c : Γ} {a b : ι → K}, (∀ (i : ι), (v : K → Γ) (a i) ≤ (1 : Γ)) → (∀ (i : ι), (v : K → Γ) (b i) ≤ (1 : Γ)) → (∀ (i : ι), (v : K → Γ) (a i - b i) ≤ c) → (v : K → Γ) (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ c :=
  fun s => prod_sub_prod_le s

end GlobalTheory.ProdSubProdBound
