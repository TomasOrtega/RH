import Mathlib
import Formalism.TruncatedSeriesCounting.StatementX

namespace Formalism.TruncatedSeriesCounting.X

/- English proof (translation)
Introduce `R _ ℓ hℓ π₀ y K c hc`. Break down `Nat.eq_zero_or_pos y with hy | hy` into its components or cases. Substitute `hy` using the available equality. Establish `hc0 : c = 0` using `by push_cast at hc; omega`. Substitute `hc0` using the available equality.

Rewrite using `[pow_zero]`. Conclude with `Ideal.subset_span (Set.mem_insert _ _) |> fun h => by simpa using h`. Take `⟨y', rfl⟩ : ∃ y', y = y' + 1` from `⟨y - 1, by omega⟩`. Establish `e : (π₀ * (π₀ + (ℓ : R)) ^ (ℓ - 1)) ^ (y' + 1) = π₀ * ((π₀ + (ℓ : R)) + (-(ℓ : R))) ^ y' * (π₀ + (ℓ : R)) ^ ((ℓ - 1) * (y' + 1))`. Rewrite using `[show (π₀ + (ℓ : R)) + (-(ℓ : R)) = π₀ by ring, mul_pow, ← pow_mul, pow_succ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, add_pow (π₀ + (ℓ : R)) (-(ℓ : R)) y', Finset.mul_sum, Finset.sum_mul]`. Use `Ideal.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Establish `hm' : m ≤ y'` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)`. Distinguish the cases in `hj : c ≤ y' - m`.

Establish `h1 : (-(ℓ : R)) ^ (y' - m) = (ℓ : R) ^ c * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c))`. Establish `hsplit : (ℓ : R) ^ (y' - m) = (ℓ : R) ^ c * (ℓ : R) ^ (y' - m - c)`. Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[neg_pow, hsplit]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : (ℓ : R) ^ c ∈ Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K}` using `Ideal.subset_span (Set.mem_insert _ _)`. Rewrite using `[h1]`. Establish `: π₀ * ((π₀ + ↑ℓ) ^ m * ((ℓ : R) ^ c * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c))) * ↑(y'.choose m)) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)) = (ℓ : R) ^ c * (π₀ * (π₀ + ↑ℓ) ^ m * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c)) * ↑(y'.choose m) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)))` using `by ring`.

Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ hmem`. Establish `hK : K ≤ m + (ℓ - 1) * (y' + 1)` using `by push_neg at hj`. Establish `h2 : (c : ℤ) ≤ (ℓ : ℤ) * ((y' + 1 : ℕ) : ℤ) - K` using `hc`. Move the coercions through the operations in `at h2`.

Establish `h3 : (c : ℤ) ≥ (y' : ℤ) - m + 1` using `by omega`. Use `zify [hℓ]`. Use polynomial arithmetic with `[h2, h3]`. Establish `hmem : π₀ * (π₀ + (ℓ : R)) ^ K ∈ Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K}` using `Ideal.subset_span (Set.mem_insert_of_mem _ rfl)`. Establish `: π₀ * ((π₀ + ↑ℓ) ^ m * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m)) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)) = π₀ * (π₀ + (ℓ : R)) ^ K * ((π₀ + ↑ℓ) ^ (m + (ℓ - 1) * (y' + 1) - K) * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m))`.

Establish `e2 : (π₀ + (ℓ : R)) ^ K * (π₀ + (ℓ : R)) ^ (m + (ℓ - 1) * (y' + 1) - K) = (π₀ + (ℓ : R)) ^ m * (π₀ + (ℓ : R)) ^ ((ℓ - 1) * (y' + 1))`. Rewrite using `[← pow_add, ← pow_add, Nat.add_sub_cancel' hK]`. Take the linear combination `(π₀ * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m)) * e2.symm`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ hmem`.
-/
theorem truncation_remainder_bound : TruncRem1 := by
  intro R _ ℓ hℓ π₀ y K c hc
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy
    have hc0 : c = 0 := by push_cast at hc; omega
    subst hc0
    rw [pow_zero]
    exact Ideal.subset_span (Set.mem_insert _ _) |> fun h => by simpa using h
  · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    have e : (π₀ * (π₀ + (ℓ : R)) ^ (ℓ - 1)) ^ (y' + 1) =
        π₀ * ((π₀ + (ℓ : R)) + (-(ℓ : R))) ^ y' * (π₀ + (ℓ : R)) ^ ((ℓ - 1) * (y' + 1)) := by
      rw [show (π₀ + (ℓ : R)) + (-(ℓ : R)) = π₀ by ring, mul_pow, ← pow_mul, pow_succ]
      ring
    rw [e, add_pow (π₀ + (ℓ : R)) (-(ℓ : R)) y', Finset.mul_sum, Finset.sum_mul]
    refine Ideal.sum_mem _ fun m hm => ?_
    have hm' : m ≤ y' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    by_cases hj : c ≤ y' - m
    · have h1 : (-(ℓ : R)) ^ (y' - m) = (ℓ : R) ^ c * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c)) := by
        have hsplit : (ℓ : R) ^ (y' - m) = (ℓ : R) ^ c * (ℓ : R) ^ (y' - m - c) := by
          rw [← pow_add]
          congr 1
          omega
        rw [neg_pow, hsplit]
        ring
      have hmem : (ℓ : R) ^ c ∈ Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K} :=
        Ideal.subset_span (Set.mem_insert _ _)
      rw [h1]
      have : π₀ * ((π₀ + ↑ℓ) ^ m * ((ℓ : R) ^ c * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c))) * ↑(y'.choose m)) *
          (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)) = (ℓ : R) ^ c * (π₀ * (π₀ + ↑ℓ) ^ m * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c)) *
          ↑(y'.choose m) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1))) := by ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hmem
    · have hK : K ≤ m + (ℓ - 1) * (y' + 1) := by
        push_neg at hj
        have h2 : (c : ℤ) ≤ (ℓ : ℤ) * ((y' + 1 : ℕ) : ℤ) - K := hc
        push_cast at h2
        have h3 : (c : ℤ) ≥ (y' : ℤ) - m + 1 := by omega
        zify [hℓ]
        nlinarith [h2, h3]
      have hmem : π₀ * (π₀ + (ℓ : R)) ^ K ∈ Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      have : π₀ * ((π₀ + ↑ℓ) ^ m * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m)) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)) =
          π₀ * (π₀ + (ℓ : R)) ^ K * ((π₀ + ↑ℓ) ^ (m + (ℓ - 1) * (y' + 1) - K) * (-(ℓ : R)) ^ (y' - m) *
            ↑(y'.choose m)) := by
        have e2 : (π₀ + (ℓ : R)) ^ K * (π₀ + (ℓ : R)) ^ (m + (ℓ - 1) * (y' + 1) - K) =
            (π₀ + (ℓ : R)) ^ m * (π₀ + (ℓ : R)) ^ ((ℓ - 1) * (y' + 1)) := by
          rw [← pow_add, ← pow_add, Nat.add_sub_cancel' hK]
        linear_combination (π₀ * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m)) * e2.symm
      rw [this]
      exact Ideal.mul_mem_right _ _ hmem

end Formalism.TruncatedSeriesCounting.X
