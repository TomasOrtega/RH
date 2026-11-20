import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.UniNilp

open Matrix Finset Real

namespace GlobalTheory

/- English proof (translation)
Establish `hc : Commute A (-1 : Matrix (Fin n) (Fin n) K)` using `(Commute.one_right A).neg_right`. Establish `hall : ∀ m ∈ Finset.range (k + 1), (A ^ m).trace = (n : K)`. Introduce `m hm`. Break down `Nat.eq_zero_or_pos m with rfl | hm0` into its components or cases. Simplify using the standard rewrite rules.

Conclude with `h m hm0 (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hkn)`. Rewrite using `[sub_eq_add_neg, hc.add_pow, Matrix.trace_sum]`. Establish `hterm : ∀ m ∈ Finset.range (k + 1), (A ^ m * (-1 : Matrix (Fin n) (Fin n) K) ^ (k - m) * (k.choose m : Matrix (Fin n) (Fin n) K)).trace = (n : K) * ((1 : K) ^ m * (-1 : K) ^ (k - m) * (k.choose m : K))`. Introduce `m hm`. Establish `e1 : (-1 : Matrix (Fin n) (Fin n) K) ^ (k - m) = ((-1 : K) ^ (k - m)) • (1 : Matrix (Fin n) (Fin n) K)`.

Rewrite using `[← neg_one_smul K (1 : Matrix (Fin n) (Fin n) K), smul_pow, one_pow]`. Establish `e2 : ((k.choose m : ℕ) : Matrix (Fin n) (Fin n) K) = (k.choose m : K) • (1 : Matrix (Fin n) (Fin n) K)`. Rewrite using `[Nat.cast_smul_eq_nsmul, nsmul_one]`. Rewrite using `[e1, e2, Matrix.mul_smul, mul_one, Matrix.mul_smul, mul_one, smul_smul, Matrix.trace_smul, hall m hm, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← add_pow]`. Simplify using `[Nat.pos_iff_ne_zero.mp hk1]`.
-/
private theorem trace_sub_one_pow_eq_zero_of_trace_pow_eq (K : Type) [Field K] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) K)
    (h : ∀ j, 1 ≤ j → j ≤ n → (A ^ j).trace = n) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ((A - 1) ^ k).trace = 0 := by
  have hc : Commute A (-1 : Matrix (Fin n) (Fin n) K) := (Commute.one_right A).neg_right
  have hall : ∀ m ∈ Finset.range (k + 1), (A ^ m).trace = (n : K) := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · exact h m hm0 (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hkn)
  rw [sub_eq_add_neg, hc.add_pow, Matrix.trace_sum]
  have hterm : ∀ m ∈ Finset.range (k + 1),
      (A ^ m * (-1 : Matrix (Fin n) (Fin n) K) ^ (k - m) * (k.choose m : Matrix (Fin n) (Fin n) K)).trace
        = (n : K) * ((1 : K) ^ m * (-1 : K) ^ (k - m) * (k.choose m : K)) := by
    intro m hm
    have e1 : (-1 : Matrix (Fin n) (Fin n) K) ^ (k - m) = ((-1 : K) ^ (k - m)) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [← neg_one_smul K (1 : Matrix (Fin n) (Fin n) K), smul_pow, one_pow]
    have e2 : ((k.choose m : ℕ) : Matrix (Fin n) (Fin n) K) = (k.choose m : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_one]
    rw [e1, e2, Matrix.mul_smul, mul_one, Matrix.mul_smul, mul_one, smul_smul,
      Matrix.trace_smul, hall m hm, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← add_pow]
  simp [Nat.pos_iff_ne_zero.mp hk1]

/- English proof (translation)
Establish `htr : ∀ k, 1 ≤ k → k ≤ n → ((A - 1) ^ k).trace = 0` using `fun k hk1 hkn => trace_sub_one_pow_eq_zero_of_trace_pow_eq K n A h k hk1 hkn`. Establish `hB : IsNilpotent (A - 1)` using `ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow n (A - 1) htr`. Establish `hchar : (A - 1).charpoly = Polynomial.X ^ n`. Use `(Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hB).eq_zero` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : A - 1 - Matrix.scalar (Fin n) (-1 : K) = A`. Rewrite using `[map_neg, map_one, sub_neg_eq_add, sub_add_cancel]`. Establish `hs` using `Matrix.charpoly_sub_scalar (A - 1) (-1 : K)`. Rewrite `hs` using `[e, hchar]`.

Rewrite using `[hs, Polynomial.pow_comp, Polynomial.X_comp, map_neg, map_one, ← sub_eq_add_neg]`. Use `Matrix.aeval_self_charpoly (A - 1)` as an intermediate fact. Rewrite `this` using `[hchar, map_pow, Polynomial.aeval_X]`. Then use the resulting hypothesis.
-/
theorem unipotent_of_trace_pow_eq_size (K : Type) [Field K] [CharZero K] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) K)
    (h : ∀ j, 1 ≤ j → j ≤ n → (A ^ j).trace = n) :
    A.charpoly = (Polynomial.X - 1) ^ n ∧ (A - 1) ^ n = 0 := by
  have htr : ∀ k, 1 ≤ k → k ≤ n → ((A - 1) ^ k).trace = 0 :=
    fun k hk1 hkn => trace_sub_one_pow_eq_zero_of_trace_pow_eq K n A h k hk1 hkn
  have hB : IsNilpotent (A - 1) :=
    ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow n (A - 1) htr
  have hchar : (A - 1).charpoly = Polynomial.X ^ n := by
    have := (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hB).eq_zero
    simpa [sub_eq_zero] using this
  refine ⟨?_, ?_⟩
  · have e : A - 1 - Matrix.scalar (Fin n) (-1 : K) = A := by
      rw [map_neg, map_one, sub_neg_eq_add, sub_add_cancel]
    have hs := Matrix.charpoly_sub_scalar (A - 1) (-1 : K)
    rw [e, hchar] at hs
    rw [hs, Polynomial.pow_comp, Polynomial.X_comp, map_neg, map_one, ← sub_eq_add_neg]
  · have := Matrix.aeval_self_charpoly (A - 1)
    rwa [hchar, map_pow, Polynomial.aeval_X] at this

end GlobalTheory
