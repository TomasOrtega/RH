import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL Finset

namespace GlobalTheory.TracedComatrix

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `a b`. Simplify using `[epow]`.

Consider the case `succ k ih`. Introduce `a b`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Conclude with `Finset.sum_comm`.

Use `_ = ∑ d, E a d * epow E (k + 1) d b := rfl`.
-/
theorem epow_succ_left {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) :
    ∀ (k : ℕ) (a b : Fin n), epow E (k + 1) a b = ∑ c, E a c * epow E k c b := by
  intro k
  induction k with
  | zero =>
    intro a b
    simp [epow]
  | succ k ih =>
    intro a b
    calc epow E (k + 1 + 1) a b = ∑ c, epow E (k + 1) a c * E c b := rfl
      _ = ∑ c, (∑ d, E a d * epow E k d c) * E c b :=
          Finset.sum_congr rfl fun c _ => by rw [ih a c]
      _ = ∑ d, E a d * ∑ c, epow E k d c * E c b := by
          simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
      _ = ∑ d, E a d * epow E (k + 1) d b := rfl

/- English proof (translation)
Establish `h1 : ∀ k, ∑ l, Tm E x j l * epow E k l i = algebraMap ℂ A x * epow E k j i + epow E (k + 1) j i`. Introduce `k`. Rewrite using `[epow_succ_left]`. Simplify using `[Tm, add_mul, Finset.sum_add_distrib, ite_mul]`. Establish `h2 : ∑ l, Tm E x j l * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) * epow E k l i = ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) * ∑ l, Tm E x j l * epow E k l i`.

Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← mul_assoc, Algebra.commutes]`. Rewrite using `[h2]`.

Repeatedly rewrite using `[h1]`. Use `set a : ℕ → A := fun k => algebraMap ℂ A ((-1) ^ k * x ^ (N + 1 - k)) * epow E k j i with ha`. Establish `h3 : ∀ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) * (algebraMap ℂ A x * epow E k j i + epow E (k + 1) j i) = a k - a (k + 1)`. Introduce `k hk`. Establish `hk' : N + 1 - k = (N - k) + 1`.

Use `Finset.mem_range.mp hk` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `only [ha, hk', Nat.add_sub_add_right, mul_add, ← mul_assoc, ← map_mul, sub_eq_add_neg, ← neg_mul, ← map_neg]`. Apply the tactic sequence `congr 3 <;> ring`. Rewrite using `[Finset.sum_congr rfl h3, Finset.sum_range_sub']`.

Simplify using `only [ha, Nat.sub_self, pow_zero, mul_one, one_mul, Nat.sub_zero, sub_eq_add_neg, ← neg_mul, ← map_neg]`. Use `congr 2`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem key {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x : ℂ) (N : ℕ)
    (j i : Fin n) :
    ∑ l, Tm E x j l * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) * epow E k l i =
      algebraMap ℂ A (x ^ (N + 1)) * (if j = i then 1 else 0) +
        algebraMap ℂ A ((-1) ^ N) * epow E (N + 1) j i := by
  have h1 : ∀ k, ∑ l, Tm E x j l * epow E k l i = algebraMap ℂ A x * epow E k j i + epow E (k + 1) j i := by
    intro k
    rw [epow_succ_left]
    simp [Tm, add_mul, Finset.sum_add_distrib, ite_mul]
  have h2 : ∑ l, Tm E x j l * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) * epow E k l i
      = ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) * ∑ l, Tm E x j l * epow E k l i := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, ← mul_assoc, Algebra.commutes]
  rw [h2]
  simp_rw [h1]
  set a : ℕ → A := fun k => algebraMap ℂ A ((-1) ^ k * x ^ (N + 1 - k)) * epow E k j i with ha
  have h3 : ∀ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) *
      (algebraMap ℂ A x * epow E k j i + epow E (k + 1) j i) = a k - a (k + 1) := by
    intro k hk
    have hk' : N + 1 - k = (N - k) + 1 := by
      have := Finset.mem_range.mp hk; omega
    simp only [ha, hk', Nat.add_sub_add_right, mul_add, ← mul_assoc, ← map_mul, sub_eq_add_neg,
      ← neg_mul, ← map_neg]
    congr 3 <;> ring
  rw [Finset.sum_congr rfl h3, Finset.sum_range_sub']
  simp only [ha, Nat.sub_self, pow_zero, mul_one, one_mul, Nat.sub_zero, sub_eq_add_neg, ← neg_mul, ← map_neg]
  congr 2
  congr 1
  ring

/- English proof (translation)
Introduce `A _ _ m E hE u N`. Use `set C : Fin (m + 1) → Fin (m + 1) → A := fun i j => (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u with hC`. Use `set P : Fin (m + 1) → Fin (m + 1) → A := fun l i => ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * epow E k l i with hP`. Establish `hQ` using `qComatrix A m E hE u`. Establish `S1 : ∑ i, ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i = qdet E u * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr E k`.

Simplify using `only [hC, hQ, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[← Finset.mul_sum]`. Use `congr 1`. Simplify using `only [hP, etr, Finset.mul_sum]`. Conclude with `Finset.sum_comm`.

Establish `S2 : ∑ i, ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i = algebraMap ℂ A ((u - m) ^ (N + 1)) * ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u + algebraMap ℂ A ((-1) ^ N) * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * q …`. Establish `h : ∀ i, ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i = ∑ j, C i j * (algebraMap ℂ A ((u - m) ^ (N + 1)) * (if j = i then 1 else 0) + algebraMap ℂ A ((-1) ^ N) * epow E (N + 1) j i)`. Introduce `i`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_mul, Finset.mul_sum, mul_assoc]`.

Conclude with `Finset.sum_comm`. Use `_ = _ := Finset.sum_congr rfl fun j _ => congrArg (C i j * ·) (key E (u - (m : ℂ)) N j i)`. Simplify using `only [h, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← Algebra.commutes]`. Simplify using `[hC, ← two_mul, pow_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← mul_assoc, ← Algebra.commutes, hC]`. Conclude with `S2.symm.trans S1`.
-/
theorem traced_comatrix : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E → ∀ (u : ℂ) (N : ℕ), algebraMap ℂ A ((u - m) ^ (N + 1)) * ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u + algebraMap ℂ A ((-1) ^ N) * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u * epow E (N + 1) j i = qdet E u * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr E k := by
  intro A _ _ m E hE u N
  set C : Fin (m + 1) → Fin (m + 1) → A := fun i j =>
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u with hC
  set P : Fin (m + 1) → Fin (m + 1) → A := fun l i =>
    ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * epow E k l i with hP
  have hQ := qComatrix A m E hE u
  have S1 : ∑ i, ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i =
      qdet E u * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr E k := by
    simp only [hC, hQ, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.mul_sum]
    congr 1
    simp only [hP, etr, Finset.mul_sum]
    exact Finset.sum_comm
  have S2 : ∑ i, ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i =
      algebraMap ℂ A ((u - m) ^ (N + 1)) * ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u + algebraMap ℂ A ((-1) ^ N) * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u * epow E (N + 1) j i := by
    have h : ∀ i, ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i =
        ∑ j, C i j * (algebraMap ℂ A ((u - m) ^ (N + 1)) * (if j = i then 1 else 0) +
          algebraMap ℂ A ((-1) ^ N) * epow E (N + 1) j i) := by
      intro i
      calc ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i
          = ∑ j, C i j * ∑ l, Tm E (u - (m : ℂ)) j l * P l i := by
            simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
            exact Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun j _ => congrArg (C i j * ·) (key E (u - (m : ℂ)) N j i)
    simp only [h, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Algebra.commutes]
      simp [hC, ← two_mul, pow_mul]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, ← mul_assoc, ← Algebra.commutes, hC]
  exact S2.symm.trans S1

end GlobalTheory.TracedComatrix
