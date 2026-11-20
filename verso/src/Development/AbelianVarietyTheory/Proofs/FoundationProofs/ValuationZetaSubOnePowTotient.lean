import Mathlib

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Establish `h : x ^ k - 1 = (∑ i ∈ Finset.range k, x ^ i) * (x - 1)` using `(geom_sum_mul x k).symm`. Rewrite using `[h, map_mul]`. Establish `hs : A.valuation (∑ i ∈ Finset.range k, x ^ i) ≤ 1`. Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `i _`.

Rewrite using `[map_pow]`. Conclude with `pow_le_one' hx i`. Conclude with `mul_le_of_le_one_left' hs`.
-/
theorem valuationSubring_pow_sub_one_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {x : Ω}
    (hx : A.valuation x ≤ 1) (k : ℕ) :
    A.valuation (x ^ k - 1) ≤ A.valuation (x - 1) := by
  have h : x ^ k - 1 = (∑ i ∈ Finset.range k, x ^ i) * (x - 1) := (geom_sum_mul x k).symm
  rw [h, map_mul]
  have hs : A.valuation (∑ i ∈ Finset.range k, x ^ i) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_pow]; exact pow_le_one' hx i
  exact mul_le_of_le_one_left' hs

/- English proof (translation)
Establish `hN : 0 < l ^ n` using `pow_pos (Fact.out : l.Prime).pos n`. Establish `hv1 : ∀ {μ : Ω}, IsPrimitiveRoot μ (l ^ n) → A.valuation μ ≤ 1`. Introduce `μ hμ`. Establish `h1 : A.valuation μ ^ (l ^ n) = 1` using `by rw [← map_pow, hμ.pow_eq_one, map_one]`. Conclude with `(pow_eq_one_iff.1 h1 |>.resolve_right hN.ne').le`.

Establish `key : ∀ μ ∈ primitiveRoots (l ^ n) Ω, A.valuation (1 - μ) = A.valuation (ζ - 1)`. Introduce `μ hμ`. Rewrite `hμ` using `[mem_primitiveRoots hN]`. Rewrite using `[Valuation.map_sub_swap]`. Take `⟨i, -, hi⟩` from `hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one`.

Take `⟨j, -, hj⟩` from `hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← hi]`. Conclude with `valuationSubring_pow_sub_one_le A (hv1 hζ) i`. Rewrite using `[← hj]`.

Conclude with `valuationSubring_pow_sub_one_le A (hv1 hμ) j`. Establish `hcyc` using `cyclotomic_eq_prod_X_sub_primitiveRoots hζ`. Take `⟨k, rfl⟩ : ∃ k, n = k + 1` from `⟨n - 1, by omega⟩`. Establish `h1 : (l : Ω) = ∏ μ ∈ primitiveRoots (l ^ (k + 1)) Ω, (1 - μ)`. Use `congrArg (eval 1) hcyc` as an intermediate fact.

Rewrite `this` using `[eval_one_cyclotomic_prime_pow, eval_prod]`. Simplify using `using this`. Rewrite using `[h1, map_prod, Finset.prod_congr rfl key, Finset.prod_const, hζ.card_primitiveRoots]`.
-/
theorem valuation_zeta_sub_one_pow_totient (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] (A : ValuationSubring Ω) (n : ℕ) (ζ : Ω) (hn : 1 ≤ n)
    (hζ : IsPrimitiveRoot ζ (l ^ n)) :
    A.valuation (ζ - 1) ^ (l ^ n).totient = A.valuation (l : Ω) := by
  have hN : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have hv1 : ∀ {μ : Ω}, IsPrimitiveRoot μ (l ^ n) → A.valuation μ ≤ 1 := by
    intro μ hμ
    have h1 : A.valuation μ ^ (l ^ n) = 1 := by rw [← map_pow, hμ.pow_eq_one, map_one]
    exact (pow_eq_one_iff.1 h1 |>.resolve_right hN.ne').le
  have key : ∀ μ ∈ primitiveRoots (l ^ n) Ω, A.valuation (1 - μ) = A.valuation (ζ - 1) := by
    intro μ hμ
    rw [mem_primitiveRoots hN] at hμ
    rw [Valuation.map_sub_swap]
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    obtain ⟨j, -, hj⟩ := hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one
    apply le_antisymm
    · rw [← hi]; exact valuationSubring_pow_sub_one_le A (hv1 hζ) i
    · rw [← hj]; exact valuationSubring_pow_sub_one_le A (hv1 hμ) j
  have hcyc := cyclotomic_eq_prod_X_sub_primitiveRoots hζ
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : (l : Ω) = ∏ μ ∈ primitiveRoots (l ^ (k + 1)) Ω, (1 - μ) := by
    have := congrArg (eval 1) hcyc
    rw [eval_one_cyclotomic_prime_pow, eval_prod] at this
    simpa using this
  rw [h1, map_prod, Finset.prod_congr rfl key, Finset.prod_const, hζ.card_primitiveRoots]

end GlobalTheory
