import Mathlib

namespace KStar.TotallyRealRoots

private def sieveOK (n : ℕ) : Bool :=
  decide (2 ≤ n) && [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31].all (fun d => n == d || n % d != 0)

private def headF (n : ℕ) : ℕ :=
  if sieveOK n then (Nat.log2 (n ^ 256) + 1) * 1000000 / n ^ 2 + 1 else 0

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
private theorem tail_step (m : ℝ) (hm : 1 ≤ m) :
    Real.log (m + 1) / (m + 1) ^ 2 ≤ (Real.log m + 2) / m - (Real.log (m + 1) + 2) / (m + 1) := by
  have hm0 : 0 < m := by linarith
  have hL : 0 ≤ Real.log (m + 1) := Real.log_nonneg (by linarith)
  have h1 : Real.log (m + 1) - Real.log m ≤ 1 / m := by
    rw [← Real.log_div (by linarith) hm0.ne']
    have := Real.log_le_sub_one_of_pos (x := (m + 1) / m) (by positivity)
    have e : (m + 1) / m - 1 = 1 / m := by field_simp; ring
    linarith
  set L := Real.log (m + 1)
  have h2 : (L - 1 / m + 2) / m ≤ (Real.log m + 2) / m := by
    apply div_le_div_of_nonneg_right _ hm0.le
    linarith
  have h3 : (L - 1 / m + 2) / m - (L + 2) / (m + 1) - L / (m + 1) ^ 2
      = L / (m * (m + 1) ^ 2) + (m - 1) / (m ^ 2 * (m + 1)) := by
    field_simp
    ring
  have h4 : 0 ≤ L / (m * (m + 1) ^ 2) := by positivity
  have h5 : 0 ≤ (m - 1) / (m ^ 2 * (m + 1)) := div_nonneg (by linarith) (by positivity)
  linarith

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem tail_sum (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    ∑ n ∈ Finset.Ico (N + 1) (N + 1 + k), Real.log n / (n : ℝ) ^ 2
      ≤ (Real.log N + 2) / N - (Real.log ((N + k : ℕ) : ℝ) + 2) / ((N + k : ℕ) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc (N + 1), Finset.sum_Ico_succ_top (by omega)]
    have h := tail_step ((N + k : ℕ) : ℝ) (by exact_mod_cast (by omega : 1 ≤ N + k))
    have e1 : ((N + 1 + k : ℕ) : ℝ) = ((N + k : ℕ) : ℝ) + 1 := by push_cast; ring
    have e2 : ((N + (k + 1) : ℕ) : ℝ) = ((N + k : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e1, e2]
    linarith

end KStar.TotallyRealRoots
