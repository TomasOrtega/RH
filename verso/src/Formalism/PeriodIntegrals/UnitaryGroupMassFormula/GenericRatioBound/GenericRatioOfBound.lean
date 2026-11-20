import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic

namespace PI.GGRatio

open Finset

/- English proof (translation)
Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[← Finset.sum_range_id, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk]`. Simplify using the standard rewrite rules.
-/
theorem sum_Ico_one_id (k : ℕ) : ∑ i ∈ Ico 1 k, i = k * (k - 1) / 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rw [← Finset.sum_range_id, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk]
  simp

/- English proof (translation)
Rewrite using `[Finset.prod_pow_eq_pow_sum, sum_Ico_one_id]`.
-/
theorem pow_gauss_eq_prod (q : ℝ) (k : ℕ) : q ^ (k * (k - 1) / 2) = ∏ i ∈ Ico 1 k, q ^ i := by
  rw [Finset.prod_pow_eq_pow_sum, sum_Ico_one_id]

/- English proof (translation)
Establish `h1 : Q ≠ 0` using `by linarith`. Establish `h2 : Q - 1 ≠ 0` using `by linarith`. Clear the denominators using the available nonvanishing facts.
-/
theorem inv_one_sub_inv (Q : ℝ) (hQ : 1 < Q) : (1 - Q⁻¹)⁻¹ = Q / (Q - 1) := by
  have h1 : Q ≠ 0 := by linarith
  have h2 : Q - 1 ≠ 0 := by linarith
  field_simp

/- English proof (translation)
Establish `hq1 : (1 : ℝ) < q` using `by exact_mod_cast (by omega : 1 < q)`. Establish `hcast : ((∏ i ∈ Ico 1 k, (q ^ i - 1) : ℕ) : ℝ) = ∏ i ∈ Ico 1 k, ((q : ℝ) ^ i - 1)`. Rewrite using `[Nat.cast_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h1 : 1 ≤ q ^ i` using `Nat.one_le_pow _ _ (by omega)`.

Move the coercions through the operations in `[Nat.cast_sub h1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hprodpos : (0 : ℝ) < ∏ i ∈ Ico 1 k, ((q : ℝ) ^ i - 1)`. Use `Finset.prod_pos fun i hi => ?_` and prove the remaining obligations. Establish `h1 : 1 ≤ i` using `(Finset.mem_Ico.1 hi).1`.

Establish `h2` using `one_lt_pow₀ hq1 (by omega : i ≠ 0)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdle : ∏ i ∈ Ico 1 k, ((q : ℝ) ^ i - 1) ≤ d`. Rewrite using `[← hcast]`. Conclude with `hd` after adjusting the coercions.

Establish `e : ∏ i ∈ Ico 1 k, (1 - ((q : ℝ) ^ i)⁻¹)⁻¹ = (q : ℝ) ^ (k * (k - 1) / 2) / ∏ i ∈ Ico 1 k, ((q : ℝ) ^ i - 1)`. Rewrite using `[pow_gauss_eq_prod, ← Finset.prod_div_distrib]`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `h1 : 1 ≤ i` using `(Finset.mem_Ico.1 hi).1`. Conclude with `inv_one_sub_inv _ (one_lt_pow₀ hq1 (by omega))`.

Rewrite using `[e]`. Use `push_cast`. Conclude with `div_le_div_of_nonneg_left (by positivity) hprodpos hdle`.
-/
theorem ratio_le (q k d : ℕ) (hq : 2 ≤ q) (hd : ∏ i ∈ Ico 1 k, (q ^ i - 1) ≤ d) :
    ((q ^ (k * (k - 1) / 2) : ℕ) : ℝ) / (d : ℝ) ≤ ∏ i ∈ Ico 1 k, (1 - ((q : ℝ) ^ i)⁻¹)⁻¹ := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hcast : ((∏ i ∈ Ico 1 k, (q ^ i - 1) : ℕ) : ℝ) = ∏ i ∈ Ico 1 k, ((q : ℝ) ^ i - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h1 : 1 ≤ q ^ i := Nat.one_le_pow _ _ (by omega)
    push_cast [Nat.cast_sub h1]
    ring
  have hprodpos : (0 : ℝ) < ∏ i ∈ Ico 1 k, ((q : ℝ) ^ i - 1) := by
    refine Finset.prod_pos fun i hi => ?_
    have h1 : 1 ≤ i := (Finset.mem_Ico.1 hi).1
    have h2 := one_lt_pow₀ hq1 (by omega : i ≠ 0)
    linarith
  have hdle : ∏ i ∈ Ico 1 k, ((q : ℝ) ^ i - 1) ≤ d := by
    rw [← hcast]
    exact_mod_cast hd
  have e : ∏ i ∈ Ico 1 k, (1 - ((q : ℝ) ^ i)⁻¹)⁻¹ = (q : ℝ) ^ (k * (k - 1) / 2) / ∏ i ∈ Ico 1 k, ((q : ℝ) ^ i - 1) := by
    rw [pow_gauss_eq_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    have h1 : 1 ≤ i := (Finset.mem_Ico.1 hi).1
    exact inv_one_sub_inv _ (one_lt_pow₀ hq1 (by omega))
  rw [e]
  push_cast
  exact div_le_div_of_nonneg_left (by positivity) hprodpos hdle

open Formalism.L2.SG.GGMirabolic in

/- English proof (translation)
Introduce `hB hU F _ _ k ψ hψ V _ _ _ π hπ hg`. Rewrite using `[hU]`. Conclude with `ratio_le (Fintype.card F) k _ Fintype.one_lt_card (hB F k ψ hψ V π hπ hg)`.
-/
theorem genericRatioOfBound : GenericRatioOfBound := by
  intro hB hU F _ _ k ψ hψ V _ _ _ π hπ hg
  rw [hU]
  exact ratio_le (Fintype.card F) k _ Fintype.one_lt_card (hB F k ψ hψ V π hπ hg)

end PI.GGRatio
