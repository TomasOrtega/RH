import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.GaussianSumOfOneSeparatedOfLe

open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

/- English proof (translation)
Introduce `ι h g R0 hR0 hg hh hcard`. Take `⟨t, ht_def⟩ : ∃ t : ℝ, t = R0 ^ 2 / 16` from `⟨_, rfl⟩`. Establish `ht : 0 < t` using `by rw [ht_def]; positivity`. Establish `ht' : 2 * (g : ℝ) + 1 ≤ t` using `by rw [ht_def]; linarith`. Establish `key` using `GlobalTheory.summable_exp_neg_of_card_le (fun i => h i ^ 2 / 16) (t := t) (C := 9 ^ g) (fun i => by`.

Establish `h1` using `hh i`. Establish `h2 : R0 ^ 2 ≤ h i ^ 2` using `by nlinarith`. Rewrite using `[ht_def]`. Use the proof step `linarith)`. Use the proof step `(fun s u htu hs => by`.

Establish `hu0 : 0 < u` using `lt_of_lt_of_le ht htu`. Take `⟨R, hR⟩ : ∃ R : ℝ, R = 4 * Real.sqrt u` from `⟨_, rfl⟩`. Establish `hsq : Real.sqrt u ^ 2 = u` using `Real.sq_sqrt hu0.le`. Establish `hR2 : R ^ 2 = 16 * u` using `by rw [hR, mul_pow, hsq]; norm_num`. Establish `hRnn : 0 ≤ R` using `by rw [hR]; positivity`.

Establish `hle : ∀ x : ℝ, 0 ≤ x → x ^ 2 ≤ 16 * u → x ≤ R` using `fun x hx hx2 => by`. Use the polynomial consequences of the given equalities and inequalities. Establish `hR0R : R0 ≤ R` using `hle R0 hR0.le (by rw [ht_def] at htu; linarith)`. Establish `hsS : ∀ i ∈ s, h i ≤ R` using `fun i hi => by`. Establish `h3` using `hs i hi`.

Conclude with `hle (h i) (hR0.le.trans (hh i)) (by linarith)`. Use `(hcard R hR0R s hsS).trans ?_` and prove the remaining obligations. Establish `hpow : (3 * R / R0) ^ (2 * g) = 9 ^ g * (u / t) ^ g`. Rewrite using `[pow_mul, ← mul_pow]`. Use `congr 1`.

Rewrite using `[div_pow, mul_pow, hR2, ht_def]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hpow]`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises.

Establish `hx : u / t ≤ Real.exp (u / t - 1)`. Use `Real.add_one_le_exp (u / t - 1)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hy : u - t = t * (u / t - 1)` using `by field_simp`. Establish `hy0 : 0 ≤ u / t - 1`.

Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_le]`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises.

Rewrite using `[hy]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right ht' hy0])`. Establish `e : ∀ i, -(h i) ^ 2 / 16 = -(h i ^ 2 / 16)` using `fun i => by ring`. Simplify using `only [e]`. Use `⟨key.1, key.2.trans_eq ?_⟩` and prove the remaining obligations.

Rewrite using `[ht_def, neg_div]`.
-/
theorem gaussTail_of_card_le : Ext.GaussianTailBound := by
  intro ι h g R0 hR0 hg hh hcard
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = R0 ^ 2 / 16 := ⟨_, rfl⟩
  have ht : 0 < t := by rw [ht_def]; positivity
  have ht' : 2 * (g : ℝ) + 1 ≤ t := by rw [ht_def]; linarith

  have key := GlobalTheory.summable_exp_neg_of_card_le (fun i => h i ^ 2 / 16) (t := t) (C := 9 ^ g)
    (fun i => by
      have h1 := hh i
      have h2 : R0 ^ 2 ≤ h i ^ 2 := by nlinarith
      rw [ht_def]
      linarith)
    (fun s u htu hs => by
      have hu0 : 0 < u := lt_of_lt_of_le ht htu
      obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 4 * Real.sqrt u := ⟨_, rfl⟩
      have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
      have hR2 : R ^ 2 = 16 * u := by rw [hR, mul_pow, hsq]; norm_num
      have hRnn : 0 ≤ R := by rw [hR]; positivity

      have hle : ∀ x : ℝ, 0 ≤ x → x ^ 2 ≤ 16 * u → x ≤ R := fun x hx hx2 => by
        nlinarith
      have hR0R : R0 ≤ R := hle R0 hR0.le (by rw [ht_def] at htu; linarith)
      have hsS : ∀ i ∈ s, h i ≤ R := fun i hi => by
        have h3 := hs i hi
        exact hle (h i) (hR0.le.trans (hh i)) (by linarith)
      refine (hcard R hR0R s hsS).trans ?_
      have hpow : (3 * R / R0) ^ (2 * g) = 9 ^ g * (u / t) ^ g := by
        rw [pow_mul, ← mul_pow]
        congr 1
        rw [div_pow, mul_pow, hR2, ht_def]
        field_simp
        ring
      rw [hpow]
      apply mul_le_mul_of_nonneg_left _ (by positivity)

      have hx : u / t ≤ Real.exp (u / t - 1) := by
        have := Real.add_one_le_exp (u / t - 1)
        linarith
      have hy : u - t = t * (u / t - 1) := by field_simp
      have hy0 : 0 ≤ u / t - 1 := by
        by_contra hc
        rw [not_le] at hc
        nlinarith
      calc (u / t) ^ g ≤ Real.exp (u / t - 1) ^ g := by gcongr
        _ = Real.exp (g * (u / t - 1)) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp ((u - t) / 2) := by
          apply Real.exp_le_exp.mpr
          rw [hy]
          nlinarith [mul_le_mul_of_nonneg_right ht' hy0])
  have e : ∀ i, -(h i) ^ 2 / 16 = -(h i ^ 2 / 16) := fun i => by ring
  simp only [e]
  refine ⟨key.1, key.2.trans_eq ?_⟩
  rw [ht_def, neg_div]

end GlobalTheory
