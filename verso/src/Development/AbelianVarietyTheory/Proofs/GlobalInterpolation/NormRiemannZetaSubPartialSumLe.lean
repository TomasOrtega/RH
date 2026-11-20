import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableAtFractInt
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open Set

namespace GlobalTheory.ZetaPartialSum
open GlobalTheory.ZetaHalfPlane

noncomputable def tailInt (s : ℂ) (a : ℝ) : ℂ :=
  ∫ t in Ioi a, ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))

/- English proof (translation)
Establish `h : -(s.re + 1) < -1` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Use `norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt h ha) ?_` and prove the remaining obligations. Rewrite using `[ae_restrict_iff' measurableSet_Ioi]`. Use `Eventually.of_forall fun t ht => ?_` and prove the remaining obligations.

Establish `ht0 : 0 < t` using `lt_trans ha ht`. Rewrite using `[norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]`. Simplify using `only [neg_re, add_re, one_re]`. Conclude with `mul_le_of_le_one_left (by positivity) (norm_fract_le t)`. Use `_ = a ^ (-s.re) / s.re := by`.

Rewrite using `[integral_Ioi_rpow_of_lt h ha, show -(s.re + 1) + 1 = -s.re by ring, neg_div_neg_eq]`.
-/
lemma norm_tailInt_le {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    ‖tailInt s a‖ ≤ a ^ (-s.re) / s.re := by
  have h : -(s.re + 1) < -1 := by linarith
  calc ‖tailInt s a‖ ≤ ∫ t in Ioi a, t ^ (-(s.re + 1)) := by
        refine norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt h ha) ?_
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine Eventually.of_forall fun t ht => ?_
        have ht0 : 0 < t := lt_trans ha ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        simp only [neg_re, add_re, one_re]
        exact mul_le_of_le_one_left (by positivity) (norm_fract_le t)
    _ = a ^ (-s.re) / s.re := by
        rw [integral_Ioi_rpow_of_lt h ha,
          show -(s.re + 1) + 1 = -s.re by ring, neg_div_neg_eq]

/- English proof (translation)
Establish `hM0 : (0 : ℝ) < M` using `by exact_mod_cast hM`. Establish `hs0 : s ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hs`. Establish `hs1' : s - 1 ≠ 0` using `sub_ne_zero.2 hs1`.

Establish `hle : (M : ℝ) ≤ M + 1` using `by linarith`. Establish `hmem : (0 : ℝ) ∉ uIcc (M : ℝ) (M + 1)`. Rewrite using `[uIcc_of_le hle]`. Introduce `h`. Combine the linear relations using `[h.1]`.

Establish `e : ∫ t in Ioc (M : ℝ) (M + 1), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) = ∫ t in (M : ℝ)..(M + 1), ((t : ℂ) ^ (-s) - (M : ℂ) * (t : ℂ) ^ (-(s + 1)))`. Rewrite using `[intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]`. Use `setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_` and prove the remaining obligations. Establish `ht0 : 0 < t` using `lt_trans hM0 ht.1`. Establish `htc : (t : ℂ) ≠ 0` using `ofReal_ne_zero.2 ht0.ne'`.

Establish `e1 : (t : ℂ) ^ (-s) = t * (t : ℂ) ^ (-(s + 1))`. Rewrite using `[show -s = 1 + -(s + 1) by ring, cpow_add _ _ htc, cpow_one]`. Establish `e2 : ⌊t⌋ = (M : ℤ)`. Rewrite using `[Int.floor_eq_iff]`. Conclude with `⟨by simpa using ht.1.le, by simpa using ht.2⟩`.

Establish `e3 : Int.fract t = t - M`. Rewrite using `[Int.fract, e2]`. Simplify using the standard rewrite rules. Rewrite using `[e1, e3]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `i1 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-s)) volume (M : ℝ) (M + 1)` using `intervalIntegral.intervalIntegrable_cpow (Or.inr hmem)`. Establish `i2 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) volume (M : ℝ) (M + 1)` using `intervalIntegral.intervalIntegrable_cpow (Or.inr hmem)`. Establish `n1 : -s ≠ -1` using `fun h => hs1 (neg_injective h)`. Establish `n2 : -(s + 1) ≠ -1` using `fun h => hs0 (by linear_combination -h)`.

Rewrite using `[e, intervalIntegral.integral_sub i1 (i2.const_mul _), intervalIntegral.integral_const_mul, integral_cpow (Or.inr ⟨n1, hmem⟩), integral_cpow (Or.inr ⟨n2, hmem⟩)]`. Use `push_cast`. Establish `hMc : (M : ℂ) ≠ 0` using `by exact_mod_cast hM0.ne'`. Establish `hMc1 : (M : ℂ) + 1 ≠ 0` using `by exact_mod_cast (Nat.succ_ne_zero M)`. Establish `a1 : (M : ℂ) ^ (1 - s) = M * (M : ℂ) ^ (-s)`.

Rewrite using `[sub_eq_add_neg, cpow_add _ _ hMc, cpow_one]`. Establish `a2 : ((M : ℂ) + 1) ^ (1 - s) = (M + 1) * ((M : ℂ) + 1) ^ (-s)`. Rewrite using `[sub_eq_add_neg, cpow_add _ _ hMc1, cpow_one]`. Rewrite using `[show -s + 1 = 1 - s by ring, show -(s + 1) + 1 = -s by ring, a1, a2]`. Establish `hs1'' : 1 - s ≠ 0` using `sub_ne_zero.2 hs1.symm`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma piece {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {M : ℕ} (hM : 1 ≤ M) :
    s * ∫ t in Ioc (M : ℝ) (M + 1), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
      = (M : ℂ) ^ (1 - s) / (s - 1) - ((M : ℂ) + 1) ^ (1 - s) / (s - 1)
        - ((M : ℂ) + 1) ^ (-s) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hle : (M : ℝ) ≤ M + 1 := by linarith
  have hmem : (0 : ℝ) ∉ uIcc (M : ℝ) (M + 1) := by
    rw [uIcc_of_le hle]
    intro h
    linarith [h.1]
  have e : ∫ t in Ioc (M : ℝ) (M + 1), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
      = ∫ t in (M : ℝ)..(M + 1), ((t : ℂ) ^ (-s) - (M : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have ht0 : 0 < t := lt_trans hM0 ht.1
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
    have e1 : (t : ℂ) ^ (-s) = t * (t : ℂ) ^ (-(s + 1)) := by
      rw [show -s = 1 + -(s + 1) by ring, cpow_add _ _ htc, cpow_one]
    have e2 : ⌊t⌋ = (M : ℤ) := by
      rw [Int.floor_eq_iff]
      exact ⟨by simpa using ht.1.le, by simpa using ht.2⟩
    have e3 : Int.fract t = t - M := by
      rw [Int.fract, e2]; simp
    rw [e1, e3]
    push_cast
    ring
  have i1 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-s)) volume (M : ℝ) (M + 1) :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr hmem)
  have i2 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) volume (M : ℝ) (M + 1) :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr hmem)
  have n1 : -s ≠ -1 := fun h => hs1 (neg_injective h)
  have n2 : -(s + 1) ≠ -1 := fun h => hs0 (by linear_combination -h)
  rw [e, intervalIntegral.integral_sub i1 (i2.const_mul _), intervalIntegral.integral_const_mul,
    integral_cpow (Or.inr ⟨n1, hmem⟩), integral_cpow (Or.inr ⟨n2, hmem⟩)]
  push_cast
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hMc1 : (M : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero M)
  have a1 : (M : ℂ) ^ (1 - s) = M * (M : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ hMc, cpow_one]
  have a2 : ((M : ℂ) + 1) ^ (1 - s) = (M + 1) * ((M : ℂ) + 1) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ hMc1, cpow_one]
  rw [show -s + 1 = 1 - s by ring, show -(s + 1) + 1 = -s by ring, a1, a2]
  have hs1'' : 1 - s ≠ 0 := sub_ne_zero.2 hs1.symm
  field_simp
  ring

/- English proof (translation)
Proceed by induction on `M, hM using Nat.le_induction with`. Consider the case `base`. Establish `hs1' : s - 1 ≠ 0` using `sub_ne_zero.2 hs1`. Rewrite using `[zeta_eq hs hs1]`. Simplify using `only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_cpow, tailInt, fractInt]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Consider the case `succ M hM ih`. Establish `hM1 : (1 : ℝ) ≤ M` using `by exact_mod_cast hM`. Establish `hle : (M : ℝ) ≤ M + 1` using `by linarith`.

Establish `hsplit : tailInt s M = (∫ t in Ioc (M : ℝ) (M + 1), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) + tailInt s ((M : ℝ) + 1)`. Unfold `tailInt`. Rewrite using `[← Ioc_union_Ioi_eq_Ioi hle, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]`. Conclude with `(integrableOn_integrand hs).mono_set fun t ht => lt_of_le_of_lt hM1 ht.1`. Conclude with `(integrableOn_integrand hs).mono_set fun t ht => lt_of_le_of_lt (hM1.trans hle) ht`.

Rewrite using `[ih, Finset.sum_Icc_succ_top (by omega), hsplit, mul_add, piece hs hs1 hM]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zeta_eq_sum {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {M : ℕ} (hM : 1 ≤ M) :
    riemannZeta s = ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) + (M : ℂ) ^ (1 - s) / (s - 1)
      - s * tailInt s M := by
  induction M, hM using Nat.le_induction with
  | base =>
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
    rw [zeta_eq hs hs1]
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_cpow, tailInt, fractInt]
    field_simp
    ring
  | succ M hM ih =>
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hle : (M : ℝ) ≤ M + 1 := by linarith
    have hsplit : tailInt s M
        = (∫ t in Ioc (M : ℝ) (M + 1), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
          + tailInt s ((M : ℝ) + 1) := by
      unfold tailInt
      rw [← Ioc_union_Ioi_eq_Ioi hle, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
      · exact (integrableOn_integrand hs).mono_set fun t ht => lt_of_le_of_lt hM1 ht.1
      · exact (integrableOn_integrand hs).mono_set fun t ht =>
          lt_of_le_of_lt (hM1.trans hle) ht
    rw [ih, Finset.sum_Icc_succ_top (by omega), hsplit, mul_add, piece hs hs1 hM]
    push_cast
    ring

/- English proof (translation)
Introduce `s hs hs1 M hM`. Establish `hM0 : (0 : ℝ) < M` using `by exact_mod_cast hM`. Establish `e : riemannZeta s - ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) - (M : ℂ) ^ (1 - s) / (s - 1) = -(s * tailInt s M)`. Rewrite using `[zeta_eq_sum hs hs1 hM]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, norm_neg, norm_mul, div_mul_eq_mul_div, mul_div_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (norm_tailInt_le hs hM0) (norm_nonneg s)`.
-/
theorem norm_zeta_sub_sum_le :
    ∀ s : ℂ, 0 < s.re → s ≠ 1 → ∀ M : ℕ, 1 ≤ M →
      ‖riemannZeta s - ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) - (M : ℂ) ^ (1 - s) / (s - 1)‖
        ≤ ‖s‖ / s.re * (M : ℝ) ^ (-s.re) := by
  intro s hs hs1 M hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have e : riemannZeta s - ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) - (M : ℂ) ^ (1 - s) / (s - 1)
      = -(s * tailInt s M) := by
    rw [zeta_eq_sum hs hs1 hM]; ring
  rw [e, norm_neg, norm_mul, div_mul_eq_mul_div, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_tailInt_le hs hM0) (norm_nonneg s)

end GlobalTheory.ZetaPartialSum
