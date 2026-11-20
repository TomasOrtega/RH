import Mathlib

namespace GlobalTheory

/- English proof (translation)
Use `set v := A.valuation with hv`. Use `set b := v ℓ with hb`. Establish `hb0 : 0 < b` using `lt_of_le_of_ne zero_le' (Ne.symm ((Valuation.ne_zero_iff v).2 hℓ))`. Use `set t : ℕ → A.ValueGroup := fun i => v (c i * π ^ i) with ht`. Establish `hpow : ∀ i (k : ℤ), v (c i) = b ^ k → t i ^ N = b ^ ((N : ℤ) * k + i)`.

Introduce `i k hk`. Simplify using `only [ht, map_mul, map_pow, hk]`. Rewrite using `[mul_pow, ← pow_mul, mul_comm i N, pow_mul, hπ, zpow_add₀ hb0.ne', mul_comm (N : ℤ) k, zpow_mul, zpow_natCast, zpow_natCast]`. Establish `hdist : ∀ i < N, ∀ j < N, c i ≠ 0 → c j ≠ 0 → t i = t j → i = j`. Introduce `i hi j hj hci hcj hij`.

Take `⟨k, hk⟩` from `hc i hi hci`. Take `⟨l, hl⟩` from `hc j hj hcj`. Establish `e : b ^ ((N : ℤ) * k + i) = b ^ ((N : ℤ) * l + j)`. Rewrite using `[← hpow i k hk, ← hpow j l hl, hij]`. Establish `e2` using `(zpow_right_strictAnti₀ hb0 hℓ1).injective e`.

Establish `h1 : ((N : ℤ) * k + i) % N = (i : ℤ)`. Rewrite using `[add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]`. Establish `h2 : ((N : ℤ) * l + j) % N = (j : ℤ)`. Rewrite using `[add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]`. Establish `: (i : ℤ) = j` using `by rw [← h1, ← h2, e2]`.

Conclude with `this` after adjusting the coercions. Establish `hle : ∀ i ∈ Finset.range N, t i ≤ 1`. Take `⟨j, hj, hmax⟩` from `Finset.exists_max_image (Finset.range N) t ⟨0, Finset.mem_range.2 hN⟩`. It suffices to establish `t j ≤ 1 from fun i hi => (hmax i hi).trans this`. Distinguish the cases in `htj : t j = 0`.

Rewrite using `[htj]`. Conclude with `zero_le'`. Establish `hcj : c j ≠ 0`. Introduce `h`. Apply `htj` to reduce the goal to its premises.

Simplify using `[ht, h]`. Establish `hlt : ∀ i ∈ Finset.range N \ {j}, v (c i * π ^ i) < v (c j * π ^ j)`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_sdiff, Finset.mem_singleton]`. Use `lt_of_le_of_ne (hmax i hi.1) ?_` and prove the remaining obligations.

Introduce `heq`. Distinguish the cases in `hci : c i = 0`. Apply `htj` to reduce the goal to its premises. Use `show v (c j * π ^ j) = 0`. Rewrite using `[← heq]`.

Simplify using `[hci]`. Conclude with `hi.2 (hdist i (Finset.mem_range.1 hi.1) j (Finset.mem_range.1 hj) hci hcj heq)`. Use `Valuation.map_sum_eq_of_lt v hj hlt` as an intermediate fact. Rewrite `hsum` using `[← (A.valuation_le_one_iff _)]`. Use `show v (c j * π ^ j) ≤ 1`.

Rewrite using `[← this]`. Conclude with `hsum`. Introduce `i hi`. Distinguish the cases in `hci : c i = 0`. Rewrite using `[hci]`.

Conclude with `A.zero_mem`. Take `⟨k, hk⟩` from `hc i hi hci`. Establish `h1 : t i ^ N ≤ 1` using `pow_le_one₀ zero_le' (hle i (Finset.mem_range.2 hi))`. Rewrite `h1` using `[hpow i k hk, zpow_le_one_iff_right_of_lt_one₀ hb0 hℓ1]`. Establish `hk0 : 0 ≤ k`.

Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`. Establish `: (N : ℤ) * k ≤ -(N : ℤ)` using `by nlinarith`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← A.valuation_le_one_iff, hk]`.

Conclude with `zpow_le_one₀ hb0 hℓ1.le hk0`.
-/
theorem mem_of_sum_mul_pow_mem_of_valuation_zpow (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    (N : ℕ) (π ℓ : Ω) (c : ℕ → Ω) (hN : 0 < N) (hℓ : ℓ ≠ 0)
    (hℓ1 : A.valuation ℓ < 1) (hπ : A.valuation π ^ N = A.valuation ℓ)
    (hc : ∀ i < N, c i ≠ 0 → ∃ k : ℤ, A.valuation (c i) = A.valuation ℓ ^ k)
    (hsum : (∑ i ∈ Finset.range N, c i * π ^ i) ∈ A) : ∀ i < N, c i ∈ A := by
  classical
  set v := A.valuation with hv
  set b := v ℓ with hb
  have hb0 : 0 < b := lt_of_le_of_ne zero_le' (Ne.symm ((Valuation.ne_zero_iff v).2 hℓ))
  set t : ℕ → A.ValueGroup := fun i => v (c i * π ^ i) with ht

  have hpow : ∀ i (k : ℤ), v (c i) = b ^ k → t i ^ N = b ^ ((N : ℤ) * k + i) := by
    intro i k hk
    simp only [ht, map_mul, map_pow, hk]
    rw [mul_pow, ← pow_mul, mul_comm i N, pow_mul, hπ, zpow_add₀ hb0.ne', mul_comm (N : ℤ) k,
      zpow_mul, zpow_natCast, zpow_natCast]

  have hdist : ∀ i < N, ∀ j < N, c i ≠ 0 → c j ≠ 0 → t i = t j → i = j := by
    intro i hi j hj hci hcj hij
    obtain ⟨k, hk⟩ := hc i hi hci
    obtain ⟨l, hl⟩ := hc j hj hcj
    have e : b ^ ((N : ℤ) * k + i) = b ^ ((N : ℤ) * l + j) := by
      rw [← hpow i k hk, ← hpow j l hl, hij]
    have e2 := (zpow_right_strictAnti₀ hb0 hℓ1).injective e
    have h1 : ((N : ℤ) * k + i) % N = (i : ℤ) := by
      rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    have h2 : ((N : ℤ) * l + j) % N = (j : ℤ) := by
      rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    have : (i : ℤ) = j := by rw [← h1, ← h2, e2]
    exact_mod_cast this

  have hle : ∀ i ∈ Finset.range N, t i ≤ 1 := by
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range N) t ⟨0, Finset.mem_range.2 hN⟩
    suffices t j ≤ 1 from fun i hi => (hmax i hi).trans this
    by_cases htj : t j = 0
    · rw [htj]; exact zero_le'
    have hcj : c j ≠ 0 := by
      intro h; apply htj; simp [ht, h]
    have hlt : ∀ i ∈ Finset.range N \ {j}, v (c i * π ^ i) < v (c j * π ^ j) := by
      intro i hi
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
      refine lt_of_le_of_ne (hmax i hi.1) ?_
      intro heq
      by_cases hci : c i = 0
      · apply htj; show v (c j * π ^ j) = 0; rw [← heq]; simp [hci]
      · exact hi.2 (hdist i (Finset.mem_range.1 hi.1) j (Finset.mem_range.1 hj) hci hcj heq)
    have := Valuation.map_sum_eq_of_lt v hj hlt
    rw [← (A.valuation_le_one_iff _)] at hsum
    show v (c j * π ^ j) ≤ 1
    rw [← this]; exact hsum
  intro i hi
  by_cases hci : c i = 0
  · rw [hci]; exact A.zero_mem
  obtain ⟨k, hk⟩ := hc i hi hci
  have h1 : t i ^ N ≤ 1 := pow_le_one₀ zero_le' (hle i (Finset.mem_range.2 hi))
  rw [hpow i k hk, zpow_le_one_iff_right_of_lt_one₀ hb0 hℓ1] at h1
  have hk0 : 0 ≤ k := by
    by_contra hneg
    push_neg at hneg
    have : (N : ℤ) * k ≤ -(N : ℤ) := by nlinarith
    omega
  rw [← A.valuation_le_one_iff, hk]
  exact zpow_le_one₀ hb0 hℓ1.le hk0

end GlobalTheory
