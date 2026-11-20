import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.SCoefGeTwoOfHc

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [pmat, Pi.smul_apply, Matrix.smul_apply]`. Apply the tactic sequence `split_ifs <;> simp [Complex.real_smul]`.
-/
theorem pmat_smul {ε : Fin n → Bool} (c : ℝ) (z : PCoord ε → ℂ) :
    pmat (c • z) = (c : ℂ) • pmat z := by
  ext a b
  simp only [pmat, Pi.smul_apply, Matrix.smul_apply]
  split_ifs <;> simp [Complex.real_smul]

/- English proof (translation)
Rewrite using `[hs_pmat, hs_pmat, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun ab _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hs_pmat_smul {ε : Fin n → Bool} (c : ℝ) (z : PCoord ε → ℂ) :
    hs (pmat (c • z)) = c ^ 2 * hs (pmat z) := by
  rw [hs_pmat, hs_pmat, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/- English proof (translation)
Establish `e : hs (pmat z) / 2 = ∑ ab, ‖z ab‖ ^ 2` using `by rw [hs_pmat]; ring`. Rewrite using `[e, Qf]`. Use `Finset.sum_le_sum fun ab _ => ?_` and prove the remaining obligations. Establish `hv : ((ab.1.2 : ℕ) : ℝ) + 1 ≤ ((ab.1.1 : ℕ) : ℝ)` using `by exact_mod_cast Fin.lt_def.mp ab.2.1`. Establish `hw : 1 ≤ wab (0 : Fin n → ℝ) ab.1.1 ab.1.2` using `by simp only [wab, Pi.zero_apply]; linarith`.

Conclude with `le_mul_of_one_le_left (by positivity) hw`.
-/
theorem hs_half_le_quadratic {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    hs (pmat z) / 2 ≤ Qf (0 : Fin n → ℝ) z := by
  have e : hs (pmat z) / 2 = ∑ ab, ‖z ab‖ ^ 2 := by rw [hs_pmat]; ring
  rw [e, Qf]
  refine Finset.sum_le_sum fun ab _ => ?_
  have hv : ((ab.1.2 : ℕ) : ℝ) + 1 ≤ ((ab.1.1 : ℕ) : ℝ) := by exact_mod_cast Fin.lt_def.mp ab.2.1
  have hw : 1 ≤ wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 := by simp only [wab, Pi.zero_apply]; linarith
  exact le_mul_of_one_le_left (by positivity) hw

/- English proof (translation)
Establish `hA : Antitone (0 : Fin n → ℝ)` using `fun _ _ _ => le_rfl`. Establish `h1` using `ph_lower hA z h (by norm_num : (1 / 2 : ℝ) ≤ 1)`. Establish `h2` using `hs_half_le_quadratic z`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hs_eighth_le_of_small {ε : Fin n → Bool} (z : PCoord ε → ℂ) (h : rhoP z ≤ 1 / 2) :
    hs (pmat z) / 8 ≤ Ph (0 : Fin n → ℝ) (pmat z) := by
  have hA : Antitone (0 : Fin n → ℝ) := fun _ _ _ => le_rfl
  have h1 := ph_lower hA z h (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have h2 := hs_half_le_quadratic z
  linarith

/- English proof (translation)
Establish `hA : Antitone (0 : Fin n → ℝ)` using `fun _ _ _ => le_rfl`. Establish `hH0 : 0 ≤ hs (pmat z)` using `by rw [hs_pmat]; positivity`. Establish `hP0` using `ph_nonneg hA z`. Break down `Nat.eq_zero_or_pos (q0 ε) with hq | hq` into its components or cases. Establish `e : min (hs (pmat z)) (Real.sqrt (hs (pmat z)) / Real.sqrt (2 * (q0 ε : ℝ))) = 0`.

Rewrite using `[hq]`. Simplify using `[hH0]`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set c := Real.sqrt (2 * (q0 ε : ℝ)) with hc`.

Establish `hq1 : (1 : ℝ) ≤ (q0 ε : ℝ)` using `by exact_mod_cast hq`. Establish `hc0 : 0 < c` using `Real.sqrt_pos.mpr (by linarith)`. Use `set r := Real.sqrt (hs (pmat z)) with hr`. Establish `hrr : r ^ 2 = hs (pmat z)` using `Real.sq_sqrt hH0`. Establish `hr0 : 0 ≤ r` using `Real.sqrt_nonneg _`.

Establish `hrho : rhoP z = c * r` using `rfl`. Distinguish the cases in `hsm : c * r ≤ 1 / 2`. Use `hs_eighth_le_of_small z (by rw [hrho]; exact hsm)` as an intermediate fact. Establish `hm` using `min_le_left (hs (pmat z)) (r / c)`. Use the polynomial consequences of the given equalities and inequalities.

Use `replace hsm := lt_of_not_ge hsm`. Establish `hrp : 0 < r`. Assume the negation of the conclusion as `h0`. Establish `: r = 0` using `le_antisymm (not_lt.mp h0) hr0`. Rewrite `hsm` using `[this, mul_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set t := 2 * c * r with ht`. Establish `ht1 : 1 ≤ t` using `by rw [ht]; linarith`. Establish `ht0 : 0 < t` using `by linarith`. Use `set z' := (1 / t) • z with hz'`.

Establish `hpz : pmat z = (t : ℂ) • pmat z'`. Rewrite using `[hz', pmat_smul, smul_smul, ← Complex.ofReal_mul, mul_one_div_cancel ht0.ne', Complex.ofReal_one, one_smul]`. Establish `hhs : hs (pmat z') = (1 / t) ^ 2 * r ^ 2` using `by rw [hz', hs_pmat_smul, hrr]`. Establish `hsq : Real.sqrt (hs (pmat z')) = 1 / t * r`. Rewrite using `[hhs, ← mul_pow, Real.sqrt_sq (by positivity)]`.

Establish `hrho' : rhoP z' ≤ 1 / 2`. Establish `e2 : rhoP z' = c * Real.sqrt (hs (pmat z'))` using `rfl`. Rewrite using `[e2, hsq, ht]`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsm'` using `hs_eighth_le_of_small z' hrho'`. Establish `hsc` using `ph_scale hA z' ht1`. Rewrite `hsc` using `[← hpz]`. Establish `hm` using `min_le_right (hs (pmat z)) (r / c)`. Establish `key : 1 / 16 * (r / c) ≤ t * (hs (pmat z') / 8)`.

Rewrite using `[hhs, ht]`. Clear the denominators using the available nonvanishing facts. Use the polynomial consequences of the given equalities and inequalities. Use `mul_le_mul_of_nonneg_left hsm' ht0.le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem potential_lower_min {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    1 / 16 * min (hs (pmat z)) (Real.sqrt (hs (pmat z)) / Real.sqrt (2 * (q0 ε : ℝ))) ≤
      Ph (0 : Fin n → ℝ) (pmat z) := by
  have hA : Antitone (0 : Fin n → ℝ) := fun _ _ _ => le_rfl
  have hH0 : 0 ≤ hs (pmat z) := by rw [hs_pmat]; positivity
  have hP0 := ph_nonneg hA z
  rcases Nat.eq_zero_or_pos (q0 ε) with hq | hq
  · have e : min (hs (pmat z)) (Real.sqrt (hs (pmat z)) / Real.sqrt (2 * (q0 ε : ℝ))) = 0 := by
      rw [hq]; simp [hH0]
    rw [e]; linarith
  · set c := Real.sqrt (2 * (q0 ε : ℝ)) with hc
    have hq1 : (1 : ℝ) ≤ (q0 ε : ℝ) := by exact_mod_cast hq
    have hc0 : 0 < c := Real.sqrt_pos.mpr (by linarith)
    set r := Real.sqrt (hs (pmat z)) with hr
    have hrr : r ^ 2 = hs (pmat z) := Real.sq_sqrt hH0
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrho : rhoP z = c * r := rfl
    by_cases hsm : c * r ≤ 1 / 2
    · have := hs_eighth_le_of_small z (by rw [hrho]; exact hsm)
      have hm := min_le_left (hs (pmat z)) (r / c)
      nlinarith
    · replace hsm := lt_of_not_ge hsm
      have hrp : 0 < r := by
        by_contra h0
        have : r = 0 := le_antisymm (not_lt.mp h0) hr0
        rw [this, mul_zero] at hsm; linarith
      set t := 2 * c * r with ht
      have ht1 : 1 ≤ t := by rw [ht]; linarith
      have ht0 : 0 < t := by linarith
      set z' := (1 / t) • z with hz'
      have hpz : pmat z = (t : ℂ) • pmat z' := by
        rw [hz', pmat_smul, smul_smul, ← Complex.ofReal_mul, mul_one_div_cancel ht0.ne',
          Complex.ofReal_one, one_smul]
      have hhs : hs (pmat z') = (1 / t) ^ 2 * r ^ 2 := by rw [hz', hs_pmat_smul, hrr]
      have hsq : Real.sqrt (hs (pmat z')) = 1 / t * r := by
        rw [hhs, ← mul_pow, Real.sqrt_sq (by positivity)]
      have hrho' : rhoP z' ≤ 1 / 2 := by
        have e2 : rhoP z' = c * Real.sqrt (hs (pmat z')) := rfl
        rw [e2, hsq, ht]
        field_simp
        linarith
      have hsm' := hs_eighth_le_of_small z' hrho'
      have hsc := ph_scale hA z' ht1
      rw [← hpz] at hsc
      have hm := min_le_right (hs (pmat z)) (r / c)
      have key : 1 / 16 * (r / c) ≤ t * (hs (pmat z') / 8) := by
        rw [hhs, ht]
        field_simp
        nlinarith
      have := mul_le_mul_of_nonneg_left hsm' ht0.le
      nlinarith

end ReciprocityTheory.ChartRestriction.DS
