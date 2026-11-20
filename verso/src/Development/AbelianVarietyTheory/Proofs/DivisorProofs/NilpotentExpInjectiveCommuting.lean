import Mathlib

namespace GlobalTheory

open Finset

/- English proof (translation)
Take `⟨k, hk⟩` from `hm`. Establish `hk2 : m ^ (k + 2) = 0` using `pow_eq_zero_of_le (by omega) hk`. Set `v : A` to `∑ i ∈ range k, (((i + 2).factorial : ℚ)⁻¹) • m ^ i`. Set `w : A` to `∑ i ∈ range (k + 1), (((i + 1).factorial : ℚ)⁻¹) • m ^ i`. Establish `hw : w = 1 + m * v`.

Simplify using `only [w, v]`. Rewrite using `[sum_range_succ', mul_sum, add_comm]`. Use `congr 1`. Simplify using the standard rewrite rules. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_smul_comm, ← pow_succ']`. Establish `hcomm : Commute m v` using `Commute.sum_right _ _ _ fun i _ => ((Commute.refl m).pow_right i).smul_right _`. Establish `hnil : IsNilpotent (m * v)` using `by first`. Consider the case `exact hcomm.isNilpotent_mul_right ⟨k, hk⟩`. Consider the case `exact hcomm.symm.isNilpotent_mul_left ⟨k, hk⟩`.

Consider the case `exact hcomm.isNilpotent_mul_left ⟨k, hk⟩`. Establish `hunit : IsUnit w` using `hw ▸ hnil.isUnit_one_add`. Establish `hmw : m * w = 0`. Rewrite `h` using `[IsNilpotent.exp_eq_sum hk2, sum_range_succ']`. Simplify using `only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, add_eq_right] at h`.

Rewrite using `[← h]`. Simplify using `only [w]`. Rewrite using `[mul_sum]`. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, ← pow_succ']`.

Conclude with `hunit.mul_left_eq_zero.mp hmw`.
-/
theorem eq_zero_of_isNilpotent_of_exp_eq_one {A : Type} [Ring A] [Algebra ℚ A] {m : A}
    (hm : IsNilpotent m) (h : IsNilpotent.exp m = 1) : m = 0 := by
  obtain ⟨k, hk⟩ := hm
  have hk2 : m ^ (k + 2) = 0 := pow_eq_zero_of_le (by omega) hk
  let v : A := ∑ i ∈ range k, (((i + 2).factorial : ℚ)⁻¹) • m ^ i
  let w : A := ∑ i ∈ range (k + 1), (((i + 1).factorial : ℚ)⁻¹) • m ^ i
  have hw : w = 1 + m * v := by
    simp only [w, v]
    rw [sum_range_succ', mul_sum, add_comm]
    congr 1
    · simp
    · refine sum_congr rfl fun i _ => ?_
      rw [mul_smul_comm, ← pow_succ']
  have hcomm : Commute m v :=
    Commute.sum_right _ _ _ fun i _ => ((Commute.refl m).pow_right i).smul_right _
  have hnil : IsNilpotent (m * v) := by
    first
      | exact hcomm.isNilpotent_mul_right ⟨k, hk⟩
      | exact hcomm.symm.isNilpotent_mul_left ⟨k, hk⟩
      | exact hcomm.isNilpotent_mul_left ⟨k, hk⟩
  have hunit : IsUnit w := hw ▸ hnil.isUnit_one_add
  have hmw : m * w = 0 := by
    rw [IsNilpotent.exp_eq_sum hk2, sum_range_succ'] at h
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
      add_eq_right] at h
    rw [← h]
    simp only [w]
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, ← pow_succ']

  exact hunit.mul_left_eq_zero.mp hmw

/- English proof (translation)
Introduce `A _ _ a b hab ha hb h`. Establish `hm : IsNilpotent (a - b)` using `hab.isNilpotent_sub ha hb`. Establish `hc : Commute (a - b) b` using `(hab.sub_left (Commute.refl b))`. Establish `h1 : IsNilpotent.exp (a - b) * IsNilpotent.exp b = 1 * IsNilpotent.exp b`. Rewrite using `[← IsNilpotent.exp_add_of_commute hc hm hb, sub_add_cancel, h, one_mul]`.

Establish `h2 : IsNilpotent.exp (a - b) = 1` using `(IsNilpotent.isUnit_exp hb).mul_right_cancel h1`. Conclude with `sub_eq_zero.mp (eq_zero_of_isNilpotent_of_exp_eq_one hm h2)`.
-/
theorem exp_injective_of_commute : ∀ (A : Type) [Ring A] [Algebra ℚ A] (a b : A), Commute a b →
    IsNilpotent a → IsNilpotent b → IsNilpotent.exp a = IsNilpotent.exp b → a = b := by
  intro A _ _ a b hab ha hb h
  have hm : IsNilpotent (a - b) := hab.isNilpotent_sub ha hb
  have hc : Commute (a - b) b := (hab.sub_left (Commute.refl b))
  have h1 : IsNilpotent.exp (a - b) * IsNilpotent.exp b = 1 * IsNilpotent.exp b := by
    rw [← IsNilpotent.exp_add_of_commute hc hm hb, sub_add_cancel, h, one_mul]
  have h2 : IsNilpotent.exp (a - b) = 1 :=
    (IsNilpotent.isUnit_exp hb).mul_right_cancel h1
  exact sub_eq_zero.mp (eq_zero_of_isNilpotent_of_exp_eq_one hm h2)

end GlobalTheory
