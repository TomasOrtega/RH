import Mathlib
import GroundTheory.GlobalFields.Artin.LogCharpoly

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Use `set f := M.charpolyRev`. Use `set g := N.charpolyRev`. Establish `hS : (PowerSeries.mk fun k => (M ^ (k + 1)).trace) + (PowerSeries.mk fun k => (N ^ (k + 1)).trace) = 0`. Use extensionality with `k`. Simplify using `[h (k + 1) (Nat.le_add_left 1 k)]`.

Establish `hd : derivative (f * g) = 0`. Apply `Polynomial.coe_injective` to reduce the goal to its premises. Rewrite using `[Polynomial.derivative_mul, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul, GroundTheory.Global.coe_derivative_charpolyRev, GroundTheory.Global.coe_derivative_charpolyRev, Polynomial.coe_zero]`. Combine the equalities or inequalities in the displayed calculation. Establish `h0 : (f * g).coeff 0 = 1`.

Rewrite using `[Polynomial.mul_coeff_zero, Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev, Matrix.eval_charpolyRev, mul_one]`. Use extensionality with `k`. Break down `k with _ | k` into its components or cases. Rewrite using `[h0, Polynomial.coeff_one_zero]`. Establish `hk` using `congrArg (fun r => r.coeff k) hd`.

Simplify using `only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hk`. Establish `hu : IsUnit ((k : R) + 1)`. Establish `: ((k : R) + 1) = algebraMap K R ((k : K) + 1)` using `by simp`. Rewrite using `[this]`. Conclude with `(IsUnit.mk0 _ (by exact_mod_cast Nat.succ_ne_zero k)).map _`.

Rewrite using `[Polynomial.coeff_one, if_neg (Nat.succ_ne_zero k)]`. Conclude with `hu.mul_left_eq_zero.mp hk`.
-/
theorem charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero
    {K R : Type} [Field K] [CharZero K] [CommRing R] [Algebra K R] {p q : ℕ}
    (M : Matrix (Fin p) (Fin p) R) (N : Matrix (Fin q) (Fin q) R)
    (h : ∀ k, 1 ≤ k → (M ^ k).trace + (N ^ k).trace = 0) :
    M.charpolyRev * N.charpolyRev = 1 := by
  set f := M.charpolyRev
  set g := N.charpolyRev
  have hS : (PowerSeries.mk fun k => (M ^ (k + 1)).trace) +
      (PowerSeries.mk fun k => (N ^ (k + 1)).trace) = 0 := by
    ext k
    simp [h (k + 1) (Nat.le_add_left 1 k)]
  have hd : derivative (f * g) = 0 := by
    apply Polynomial.coe_injective
    rw [Polynomial.derivative_mul, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul,
      GroundTheory.Global.coe_derivative_charpolyRev, GroundTheory.Global.coe_derivative_charpolyRev,
      Polynomial.coe_zero]
    calc -(f : PowerSeries R) * PowerSeries.mk (fun k => (M ^ (k + 1)).trace) * (g : PowerSeries R) +
          (f : PowerSeries R) * (-(g : PowerSeries R) * PowerSeries.mk fun k => (N ^ (k + 1)).trace)
        = -((f : PowerSeries R) * (g : PowerSeries R)) *
          ((PowerSeries.mk fun k => (M ^ (k + 1)).trace) +
            (PowerSeries.mk fun k => (N ^ (k + 1)).trace)) := by ring
      _ = 0 := by rw [hS, mul_zero]
  have h0 : (f * g).coeff 0 = 1 := by
    rw [Polynomial.mul_coeff_zero, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev, Matrix.eval_charpolyRev,
      mul_one]
  ext k
  rcases k with _ | k
  · rw [h0, Polynomial.coeff_one_zero]
  · have hk := congrArg (fun r => r.coeff k) hd
    simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hk
    have hu : IsUnit ((k : R) + 1) := by
      have : ((k : R) + 1) = algebraMap K R ((k : K) + 1) := by simp
      rw [this]
      exact (IsUnit.mk0 _ (by exact_mod_cast Nat.succ_ne_zero k)).map _
    rw [Polynomial.coeff_one, if_neg (Nat.succ_ne_zero k)]
    exact hu.mul_left_eq_zero.mp hk

end GlobalTheory
