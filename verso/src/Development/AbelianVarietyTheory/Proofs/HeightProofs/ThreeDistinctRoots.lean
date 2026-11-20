import Mathlib

namespace GlobalTheory.ThreeDistinctRoots

open Polynomial

/- English proof (translation)
Introduce `K _ _ g₂ g₃ h2 hΔ`. Establish `h4 : (4 : K) ≠ 0`. Establish `: (4 : K) = 2 * 2` using `by norm_num`. Rewrite using `[this]`. Conclude with `mul_ne_zero h2 h2`.

Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : K, (4 : K) * x ^ 3 - g₂ * x - g₃ = 0 := by`. Establish `hdeg : (C (4 : K) * X ^ 3 - C g₂ * X - C g₃).degree ≠ 0`. Establish `: (C (4 : K) * X ^ 3 - C g₂ * X - C g₃).degree = 3` using `by compute_degree!`. Rewrite using `[this]`. Evaluate the decidable proposition.

Take `⟨x, hx⟩` from `IsAlgClosed.exists_root _ hdeg`. Use `⟨x, ?_⟩` and prove the remaining obligations. Simplify using `using hx`. Take `⟨s, hs⟩` from `IsAlgClosed.exists_eq_mul_self (g₂ - 3 * x ^ 2)`. Take `⟨y, hy⟩ : ∃ y : K, 2 * y = s - x` from `⟨(s - x) / 2, by field_simp⟩`.

Establish `hq : 4 * y ^ 2 + 4 * x * y + 4 * x ^ 2 - g₂ = 0`. Take the linear combination `(2 * y + x + s) * hy - hs`. Establish `hg₂ : g₂ = 4 * (x ^ 2 + x * y + y ^ 2)` using `by linear_combination -hq`. Establish `hg₃ : g₃ = -4 * x * y * (x + y)`. Take the linear combination `-hx + x * hq`.

Use `⟨x, y, -x - y, ?_⟩` and prove the remaining obligations. Establish `key : g₂ ^ 3 - 27 * g₃ ^ 2 = 16 * ((x - y) * (y - (-x - y)) * ((-x - y) - x)) ^ 2`. Rewrite using `[hg₂, hg₃]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h`. Apply `hΔ` to reduce the goal to its premises. Rewrite using `[key, sub_eq_zero.mpr h]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h`.

Apply `hΔ` to reduce the goal to its premises. Rewrite using `[key, show (-x - y) - x = -(x - (-x - y)) by ring, sub_eq_zero.mpr h]; ring`. Introduce `h`. Apply `hΔ` to reduce the goal to its premises. Rewrite using `[key, sub_eq_zero.mpr h]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `hx`. Rewrite using `[hg₂, hg₃]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hg₂, hg₃]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem three_distinct_roots :
    ∀ {K : Type} [inst : Field K] [IsAlgClosed K] (g₂ g₃ : K), (2 : K) ≠ (0 : K) →
      g₂ ^ (3 : ℕ) - (27 : K) * g₃ ^ (2 : ℕ) ≠ (0 : K) →
      ∃ (x : K) (y : K) (z : K), x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        (4 : K) * x ^ (3 : ℕ) - g₂ * x - g₃ = (0 : K) ∧
        (4 : K) * y ^ (3 : ℕ) - g₂ * y - g₃ = (0 : K) ∧
        (4 : K) * z ^ (3 : ℕ) - g₂ * z - g₃ = (0 : K) := by
  intro K _ _ g₂ g₃ h2 hΔ
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2

  obtain ⟨x, hx⟩ : ∃ x : K, (4 : K) * x ^ 3 - g₂ * x - g₃ = 0 := by
    have hdeg : (C (4 : K) * X ^ 3 - C g₂ * X - C g₃).degree ≠ 0 := by
      have : (C (4 : K) * X ^ 3 - C g₂ * X - C g₃).degree = 3 := by
        compute_degree!
      rw [this]; decide
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨x, ?_⟩
    simpa using hx

  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (g₂ - 3 * x ^ 2)
  obtain ⟨y, hy⟩ : ∃ y : K, 2 * y = s - x := ⟨(s - x) / 2, by field_simp⟩
  have hq : 4 * y ^ 2 + 4 * x * y + 4 * x ^ 2 - g₂ = 0 := by
    linear_combination (2 * y + x + s) * hy - hs
  have hg₂ : g₂ = 4 * (x ^ 2 + x * y + y ^ 2) := by linear_combination -hq
  have hg₃ : g₃ = -4 * x * y * (x + y) := by
    linear_combination -hx + x * hq
  refine ⟨x, y, -x - y, ?_⟩
  have key : g₂ ^ 3 - 27 * g₃ ^ 2 = 16 * ((x - y) * (y - (-x - y)) * ((-x - y) - x)) ^ 2 := by
    rw [hg₂, hg₃]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; apply hΔ; rw [key, sub_eq_zero.mpr h]; ring
  · intro h; apply hΔ
    rw [key, show (-x - y) - x = -(x - (-x - y)) by ring, sub_eq_zero.mpr h]; ring
  · intro h; apply hΔ
    rw [key, sub_eq_zero.mpr h]; ring
  · exact hx
  · rw [hg₂, hg₃]; ring
  · rw [hg₂, hg₃]; ring

end GlobalTheory.ThreeDistinctRoots
