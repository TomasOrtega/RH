import Mathlib
import GroundTheory.GlobalFields.Artin.LogCharpoly

namespace GlobalTheory

/- English proof (translation)
Break down `k with _ | j` into its components or cases. Simplify using the standard rewrite rules. Establish `h` using `congrArg (PowerSeries.coeff j) (GroundTheory.Global.coe_derivative_charpolyRev M)`. Rewrite `h` using `[Polynomial.coeff_coe, Polynomial.coeff_derivative, neg_mul, map_neg, PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`. Simplify using `only [Prod.swap_prod_mk, PowerSeries.coeff_mk, Polynomial.coeff_coe] at h`.

Establish `e : ∀ i ∈ Finset.range (j + 1), j + 1 - 1 - i = j - i` using `fun i _ => by omega`. Rewrite using `[Finset.sum_congr rfl fun i hi => by rw [e i hi], mul_comm, Nat.cast_succ, h]`. Conclude with `congrArg Neg.neg (Finset.sum_congr rfl fun i _ => mul_comm _ _)`.
-/
theorem natCast_mul_coeff_charpolyRev {R : Type} [CommRing R] {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R) (k : ℕ) :
    (k : R) * M.charpolyRev.coeff k =
      -∑ i ∈ Finset.range k, (M ^ (i + 1)).trace * M.charpolyRev.coeff (k - 1 - i) := by
  rcases k with _ | j
  · simp
  · have h := congrArg (PowerSeries.coeff j) (GroundTheory.Global.coe_derivative_charpolyRev M)
    rw [Polynomial.coeff_coe, Polynomial.coeff_derivative, neg_mul, map_neg,
      PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    simp only [Prod.swap_prod_mk, PowerSeries.coeff_mk, Polynomial.coeff_coe] at h
    have e : ∀ i ∈ Finset.range (j + 1), j + 1 - 1 - i = j - i := fun i _ => by omega
    rw [Finset.sum_congr rfl fun i hi => by rw [e i hi], mul_comm, Nat.cast_succ, h]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun i _ => mul_comm _ _)

end GlobalTheory
