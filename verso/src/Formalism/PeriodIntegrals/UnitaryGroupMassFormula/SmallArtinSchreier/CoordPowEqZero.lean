import Mathlib

namespace PI.UnitaryGroupMassFormula.ASSmall

section Alg

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem coeff_pow_pow (f : Perfection R p) (m n : ℕ) :
    Perfection.coeff R p (m + n) f ^ p ^ n = Perfection.coeff R p m f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, ← map_pow, Perfection.coeff_pow_p, ih]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem coord_pow_eq_zero (f : Perfection R p) {K : ℕ}
    (hK : Perfection.coeff R p 0 f ^ K = 0) (m n : ℕ) (hn : m + K ≤ n) :
    Perfection.coeff R p m f ^ p ^ n = 0 := by
  have h1 := coeff_pow_pow f 0 m
  rw [zero_add] at h1
  obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  rw [pow_add, pow_mul, h1]
  have hd : d < p ^ d := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
  exact pow_eq_zero_of_le (by omega) hK

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem neg_sum_pow_p (s : Finset ℕ) (g : ℕ → R) :
    (-∑ n ∈ s, g n) ^ p = -∑ n ∈ s, g n ^ p := by
  rw [← frobenius_def, map_neg, map_sum]
  simp only [frobenius_def]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem sum_stable (f : Perfection R p) {K : ℕ}
    (hK : Perfection.coeff R p 0 f ^ K = 0) (m j : ℕ) :
    ∑ n ∈ Finset.range (m + K + j), Perfection.coeff R p m f ^ p ^ n
      = ∑ n ∈ Finset.range (m + K), Perfection.coeff R p m f ^ p ^ n := by
  rw [Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range j)
    (fun x _ => coord_pow_eq_zero f hK m (m + K + x) (by omega)),
    add_zero]

noncomputable def sol (f : Perfection R p) (K m : ℕ) : R :=
  -∑ n ∈ Finset.range (m + K), Perfection.coeff R p m f ^ p ^ n

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem sol_succ_pow (f : Perfection R p) {K : ℕ}
    (hK : Perfection.coeff R p 0 f ^ K = 0) (m : ℕ) :
    sol f K (m + 1) ^ p = sol f K m := by
  rw [sol, sol, neg_sum_pow_p, ← sum_stable f hK m 1, show m + 1 + K = m + K + 1 by omega]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← pow_mul, mul_comm, pow_mul, ← map_pow, Perfection.coeff_pow_p]

noncomputable def solPerf (f : Perfection R p) {K : ℕ}
    (hK : Perfection.coeff R p 0 f ^ K = 0) : Perfection R p :=
  ⟨fun m => sol f K m, fun m => sol_succ_pow f hK m⟩

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem solPerf_spec (f : Perfection R p) {K : ℕ}
    (hK : Perfection.coeff R p 0 f ^ K = 0) :
    solPerf f hK ^ p - solPerf f hK = f := by
  ext m
  rw [map_sub, map_pow]
  change sol f K m ^ p - sol f K m = Perfection.coeff R p m f
  rw [sol, neg_sum_pow_p]
  simp_rw [← pow_mul, ← pow_succ]
  have e1 := Finset.sum_range_succ' (fun n => Perfection.coeff R p m f ^ p ^ n) (m + K)
  have e2 := Finset.sum_range_succ (fun n => Perfection.coeff R p m f ^ p ^ n) (m + K)
  have h0 := coord_pow_eq_zero f hK m (m + K) le_rfl
  simp only [pow_zero, pow_one] at e1
  linear_combination e1 - e2 - h0

end Alg

end PI.UnitaryGroupMassFormula.ASSmall
