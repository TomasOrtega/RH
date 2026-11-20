import Mathlib

namespace GlobalTheory.EvalNatCastZero

open Polynomial

/- English proof (translation)
Use `nontriviality R`. Proceed by induction on `n generalizing F m with`. Consider the case `zero`. Establish `h0` using `h 0`. Rewrite `h0`, the goal using `[eq_C_of_natDegree_le_zero hF]`.

Rewrite `h0` using `[eval_C]`. Rewrite using `[h0, C_0]`. Consider the case `succ n ih`. Establish `hroot : F.IsRoot (m : R)` using `by simpa using h 0`. Establish `hfac : (X - C (m : R)) * (F /ₘ (X - C (m : R))) = F` using `mul_divByMonic_eq_iff_isRoot.2 hroot`.

Establish `hdeg : (F /ₘ (X - C (m : R))).natDegree ≤ n`. Rewrite using `[natDegree_divByMonic F (monic_X_sub_C _), natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Establish `hG : F /ₘ (X - C (m : R)) = 0`. Use `ih _ hdeg (m + 1) fun k => ?_` and prove the remaining obligations.

Establish `h1` using `h (k + 1)`. Rewrite `h1` using `[← hfac, eval_mul, eval_sub, eval_X, eval_C]`. Establish `e1 : ((m + (k + 1) : ℕ) : R) - (m : R) = ((k + 1 : ℕ) : R)` using `by push_cast; ring`. Establish `e2 : m + 1 + k = m + (k + 1)` using `by ring`. Rewrite `h1` using `[e1]`.

Rewrite using `[e2]`. Conclude with `(hR (k + 1) (Nat.succ_ne_zero k)).mul_right_eq_zero.1 h1`. Rewrite using `[← hfac, hG, mul_zero]`.
-/
theorem eq_zero_of_eval_natCast_add {R : Type} [CommRing R]
    (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) (n : ℕ) (F : Polynomial R) (hF : F.natDegree ≤ n)
    (m : ℕ) (h : ∀ k : ℕ, Polynomial.eval ((m + k : ℕ) : R) F = 0) : F = 0 := by
  nontriviality R
  induction n generalizing F m with
  | zero =>
    have h0 := h 0
    rw [eq_C_of_natDegree_le_zero hF] at h0 ⊢
    rw [eval_C] at h0
    rw [h0, C_0]
  | succ n ih =>
    have hroot : F.IsRoot (m : R) := by simpa using h 0
    have hfac : (X - C (m : R)) * (F /ₘ (X - C (m : R))) = F :=
      mul_divByMonic_eq_iff_isRoot.2 hroot
    have hdeg : (F /ₘ (X - C (m : R))).natDegree ≤ n := by
      rw [natDegree_divByMonic F (monic_X_sub_C _), natDegree_X_sub_C]
      omega
    have hG : F /ₘ (X - C (m : R)) = 0 := by
      refine ih _ hdeg (m + 1) fun k => ?_
      have h1 := h (k + 1)
      rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at h1
      have e1 : ((m + (k + 1) : ℕ) : R) - (m : R) = ((k + 1 : ℕ) : R) := by push_cast; ring
      have e2 : m + 1 + k = m + (k + 1) := by ring
      rw [e1] at h1
      rw [e2]
      exact (hR (k + 1) (Nat.succ_ne_zero k)).mul_right_eq_zero.1 h1
    rw [← hfac, hG, mul_zero]

end GlobalTheory.EvalNatCastZero
