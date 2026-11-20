import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

/- English proof (translation)
Introduce `k n c y v`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `lag`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations.

Establish `hmn : m ≤ n` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)`. Establish `h : v ^ n = v ^ (n - m) * v ^ m` using `by rw [← pow_add, Nat.sub_add_cancel hmn]`. Rewrite using `[h, mul_pow, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Unfold `lag`.

Rewrite using `[Finset.sum_range_succ, Finset.sum_eq_zero]`. Simplify using `[rco]`. Introduce `m hm`. Establish `hmn : n - m ≠ 0` using `Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hm)`. Simplify using `[hmn]`.
-/
theorem lag_homogeneous : ∀ (k n : ℕ) (c y v : ℂ), lag k n (v * c) (v * y) = v ^ n * lag k n c y ∧ lag k n 0 y = y ^ n := by
  intro k n c y v
  refine ⟨?_, ?_⟩
  · unfold lag
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have h : v ^ n = v ^ (n - m) * v ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
    rw [h, mul_pow, mul_pow]; ring
  · unfold lag
    rw [Finset.sum_range_succ, Finset.sum_eq_zero]
    · simp [rco]
    · intro m hm
      have hmn : n - m ≠ 0 := Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hm)
      simp [hmn]

end GlobalTheory.HilbFam
