import Mathlib

namespace GlobalTheory.TraceExpSmul

open Finset

variable {K : Type*} {n : Type*} [Field K] [Fintype n] [DecidableEq n]

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[pow_succ, mul_assoc, h, mul_smul_comm, ← mul_assoc, ih, smul_mul_assoc, smul_smul, mul_assoc, ← pow_succ, pow_succ' d]`.
-/
theorem pow_mul_eq {R N : Matrix n n K} {d : K} (h : N * R = d • (R * N)) :
    ∀ j : ℕ, N ^ j * R = d ^ j • (R * N ^ j) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_assoc, h, mul_smul_comm, ← mul_assoc, ih, smul_mul_assoc, smul_smul,
      mul_assoc, ← pow_succ, pow_succ' d]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => exact ⟨1, by simp⟩`. Consider the case `succ m ih`. Take `⟨c, hc⟩` from `ih`.

Use `⟨c * d ^ (k * m), ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, hc, smul_mul_assoc, mul_assoc, ← mul_assoc (N ^ (k * m)), pow_mul_eq h, smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc, ← mul_assoc, ← pow_succ, mul_assoc, ← pow_add, Nat.mul_succ]`.
-/
theorem pow_R_mul (R N : Matrix n n K) {d : K} (h : N * R = d • (R * N)) (k : ℕ) :
    ∀ m : ℕ, ∃ c : K, (R * N ^ k) ^ m = c • (R ^ m * N ^ (k * m)) := by
  intro m
  induction m with
  | zero => exact ⟨1, by simp⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c * d ^ (k * m), ?_⟩
    rw [pow_succ, hc, smul_mul_assoc, mul_assoc, ← mul_assoc (N ^ (k * m)), pow_mul_eq h,
      smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc, ← mul_assoc, ← pow_succ,
      mul_assoc, ← pow_add, Nat.mul_succ]

/- English proof (translation)
Take `⟨p, hp⟩` from `hN`. Establish `hnil : IsNilpotent (R * N ^ k)`. Take `⟨c, hc⟩` from `pow_R_mul R N h k p`. Use `⟨p, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, pow_eq_zero_of_le (Nat.le_mul_of_pos_left p hk) hp, mul_zero, smul_zero]`.

Conclude with `(Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero`.
-/
theorem trace_R_mul_pow_eq_zero {R N : Matrix n n K} (hN : IsNilpotent N) {d : K}
    (h : N * R = d • (R * N)) (k : ℕ) (hk : 1 ≤ k) : Matrix.trace (R * N ^ k) = 0 := by
  obtain ⟨p, hp⟩ := hN
  have hnil : IsNilpotent (R * N ^ k) := by
    obtain ⟨c, hc⟩ := pow_R_mul R N h k p
    refine ⟨p, ?_⟩
    rw [hc, pow_eq_zero_of_le (Nat.le_mul_of_pos_left p hk) hp, mul_zero, smul_zero]
  exact (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero

/- English proof (translation)
Introduce `K n _ _ _ _ R N hN d h s`. Take `⟨p, hp⟩` from `id hN`. Establish `hsN : (s • N) ^ (p + 1) = 0`. Rewrite using `[smul_pow, pow_succ N, hp, zero_mul, smul_zero]`. Rewrite using `[IsNilpotent.exp_eq_sum hsN, mul_sum, Matrix.trace_sum, sum_range_succ']`.

Simplify using `only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, mul_one]`. Rewrite using `[add_eq_right]`. Use `sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, Matrix.trace_smul, smul_pow, mul_smul_comm, Matrix.trace_smul, trace_R_mul_pow_eq_zero hN h (i + 1) (by omega), smul_zero, smul_zero]`.
-/
theorem trace_mul_exp_smul.{u, v} : ∀ {K : Type u} {n : Type v} [inst : Field K] [inst_1 : CharZero K] [inst_2 : Fintype n] [inst_3 : DecidableEq n] {R N : Matrix n n K}, IsNilpotent N → ∀ {d : K}, N * R = d • (R * N) → ∀ (s : K), Matrix.trace (R * IsNilpotent.exp (s • N)) = Matrix.trace R := by
  intro K n _ _ _ _ R N hN d h s
  obtain ⟨p, hp⟩ := id hN
  have hsN : (s • N) ^ (p + 1) = 0 := by
    rw [smul_pow, pow_succ N, hp, zero_mul, smul_zero]
  rw [IsNilpotent.exp_eq_sum hsN, mul_sum, Matrix.trace_sum, sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, mul_one]
  rw [add_eq_right]
  refine sum_eq_zero fun i _ => ?_
  rw [mul_smul_comm, Matrix.trace_smul, smul_pow, mul_smul_comm, Matrix.trace_smul,
    trace_R_mul_pow_eq_zero hN h (i + 1) (by omega), smul_zero, smul_zero]

end GlobalTheory.TraceExpSmul
