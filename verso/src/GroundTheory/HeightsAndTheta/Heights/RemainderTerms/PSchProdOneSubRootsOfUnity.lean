import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Polynomial Finset

/- English proof (translation)
Introduce `k hk`. Establish `hk0 : 0 < k` using `hk`. Establish `: NeZero k` using `⟨Nat.pos_iff_ne_zero.mp hk0⟩`. Establish `hζ : IsPrimitiveRoot (rootOfUnity k) k`. Unfold `rootOfUnity`.

Conclude with `Complex.isPrimitiveRoot_exp k (Nat.pos_iff_ne_zero.mp hk0)`. Use `set p : ℂ[X] := ∏ i ∈ range k, (1 - C (rootOfUnity k ^ i) * X) with hp`. Use `set q : ℂ[X] := 1 - X ^ k with hq`. Establish `hpdeg : p.natDegree ≤ k`. Establish `h1 : ∀ i ∈ range k, (1 - C (rootOfUnity k ^ i) * X).natDegree ≤ 1` using `fun i _ => by compute_degree`.

Use `(natDegree_prod_le _ _).trans ((sum_le_sum h1).trans ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hqdeg : q.natDegree ≤ k`. Rewrite using `[hq]`. Use `compute_degree`.

Establish `hdeg : (p - q).degree < #(insert (0 : ℂ) (nthRootsFinset k (1 : ℂ)))`. Rewrite using `[card_insert_of_notMem (by simp [mem_nthRootsFinset hk0, zero_pow hk0.ne']), hζ.card_nthRootsFinset]`. Use `(degree_le_of_natDegree_le ((natDegree_sub_le _ _).trans (max_le hpdeg hqdeg))).trans_lt ?_` and prove the remaining obligations. Conclude with `Nat.lt_succ_self k` after adjusting the coercions. Use `eq_of_degree_sub_lt_of_eval_finset_eq _ hdeg fun x hx => ?_` and prove the remaining obligations.

Break down `mem_insert.mp hx with rfl | hx` into its components or cases. Simplify using `[hp, hq, eval_prod, zero_pow hk0.ne']`. Establish `hxk : x ^ k = 1` using `(mem_nthRootsFinset hk0 _).mp hx`. Establish `hinv : x⁻¹ ^ k = 1` using `by rw [inv_pow, hxk, inv_one]`. Take `⟨i, hi, hi'⟩` from `hζ.eq_pow_of_pow_eq_one hinv`.

Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Simplify using `[zero_pow hk0.ne'] at hxk`. Establish `hzero : p.eval x = 0`. Rewrite using `[hp, eval_prod]`.

Use `prod_eq_zero (mem_range.mpr hi) ?_` and prove the remaining obligations. Simplify using `[hi', inv_mul_cancel₀ hx0]`. Rewrite using `[hzero, hq]`. Simplify using `[hxk]`.
-/
theorem SchProdOneSubRootsOfUnity.proof : SchProdOneSubRootsOfUnity.Statement := by
  intro k hk
  have hk0 : 0 < k := hk
  have : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk0⟩
  have hζ : IsPrimitiveRoot (rootOfUnity k) k := by
    unfold rootOfUnity
    exact Complex.isPrimitiveRoot_exp k (Nat.pos_iff_ne_zero.mp hk0)
  set p : ℂ[X] := ∏ i ∈ range k, (1 - C (rootOfUnity k ^ i) * X) with hp
  set q : ℂ[X] := 1 - X ^ k with hq
  have hpdeg : p.natDegree ≤ k := by
    have h1 : ∀ i ∈ range k, (1 - C (rootOfUnity k ^ i) * X).natDegree ≤ 1 := fun i _ => by
      compute_degree
    refine (natDegree_prod_le _ _).trans ((sum_le_sum h1).trans ?_)
    simp
  have hqdeg : q.natDegree ≤ k := by
    rw [hq]; compute_degree
  have hdeg : (p - q).degree < #(insert (0 : ℂ) (nthRootsFinset k (1 : ℂ))) := by
    rw [card_insert_of_notMem (by simp [mem_nthRootsFinset hk0, zero_pow hk0.ne']),
      hζ.card_nthRootsFinset]
    refine (degree_le_of_natDegree_le ((natDegree_sub_le _ _).trans (max_le hpdeg hqdeg))).trans_lt ?_
    exact_mod_cast Nat.lt_succ_self k
  refine eq_of_degree_sub_lt_of_eval_finset_eq _ hdeg fun x hx => ?_
  rcases mem_insert.mp hx with rfl | hx
  · simp [hp, hq, eval_prod, zero_pow hk0.ne']
  · have hxk : x ^ k = 1 := (mem_nthRootsFinset hk0 _).mp hx
    have hinv : x⁻¹ ^ k = 1 := by rw [inv_pow, hxk, inv_one]
    obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one hinv
    have hx0 : x ≠ 0 := by
      rintro rfl; simp [zero_pow hk0.ne'] at hxk
    have hzero : p.eval x = 0 := by
      rw [hp, eval_prod]
      refine prod_eq_zero (mem_range.mpr hi) ?_
      simp [hi', inv_mul_cancel₀ hx0]
    rw [hzero, hq]
    simp [hxk]

end GroundTheory.Heights₂.Heights.RestTerms
