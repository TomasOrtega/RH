import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.CotangentSumStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Complex ComplexConjugate
open scoped Real

/- English proof (translation)
Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem CotangentSum.pair_identity (w w' N : ℂ) (h1 : w + N ≠ 0) (h2 : w - N ≠ 0)
    (h3 : w' + N ≠ 0) (h4 : w' - N ≠ 0) (h5 : w - w' ≠ 0) :
    ((w + N) * (w' + N))⁻¹ + ((w - N) * (w' - N))⁻¹ =
      (w - w')⁻¹ * ((1 / (w' - N) + 1 / (w' + N)) - (1 / (w - N) + 1 / (w + N))) := by
  field_simp
  ring

/- English proof (translation)
Introduce `a u ha`. Establish `hne : ∀ x : ℂ, x.im ≠ 0 → x ≠ 0` using `fun x hx h => hx (by simp [h])`. Establish `hmem : ∀ x : ℂ, x.im ≠ 0 → x ∈ Complex.integerComplement`. Introduce and unpack `x hx ⟨n, hn⟩`. Apply `hx` to reduce the goal to its premises.

Rewrite using `[← hn]`. Simplify using the standard rewrite rules. Establish `ha0 : (a : ℝ) ≠ 0` using `ha.ne'`. Use `set w : ℂ := (u : ℂ) + (a : ℂ) * I with hw`. Use `set w' : ℂ := (u : ℂ) - (a : ℂ) * I with hw'`.

Establish `hwim : w.im = a` using `by simp [hw]`. Establish `hw'im : w'.im = -a` using `by simp [hw']`. Establish `hconj : conj w = w'`. Rewrite using `[hw, hw', map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hdiff : w - w' = 2 * (a : ℂ) * I` using `by rw [hw, hw']; ring`. Establish `hdiff0 : w - w' ≠ 0`. Rewrite using `[hdiff]`. Conclude with `mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr ha0)) I_ne_zero`. Set `F : ℤ → ℂ` to `fun n => ((w + n) * (w' + n))⁻¹`.

Establish `hF : ∀ n : ℤ, ((((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-1 : ℝ) : ℝ) = F n`. Introduce `n`. Establish `e : (w + n) * (w' + n) = ((n : ℂ) + u) ^ 2 + (a : ℂ) ^ 2`. Rewrite using `[hw, hw']`. Take the linear combination `(-(a : ℂ) ^ 2) * I_sq`.

Simplify using `only [F, e, Real.rpow_neg_one]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hsum : Summable F`. Establish `h` using `(EisensteinSeries.linear_inv_isBigO_right 1 w').mul (EisensteinSeries.linear_inv_isBigO_right 1 w)`.

Use `EisensteinSeries.summable_inv_of_isBigO_rpow_inv (f := fun n : ℤ => (w + n) * (w' + n)) (a := 2) (by norm_num) ?_` and prove the remaining obligations. Simplify using `[pow_two, mul_inv] using! h`. Establish `h1` using `tsum_nat_add_neg hsum`. Establish `h2` using `(hsum.nat_add_neg).tsum_eq_zero_add`. Establish `hterm : ∀ n : ℕ, F ((n + 1 : ℕ) : ℤ) + F (-((n + 1 : ℕ) : ℤ)) = (w - w')⁻¹ * (cotTerm w' n - cotTerm w n)`.

Introduce `n`. Establish `hN : ∀ x : ℂ, x.im ≠ 0 → x + ((n : ℂ) + 1) ≠ 0 ∧ x - ((n : ℂ) + 1) ≠ 0`. Introduce `x hx`. Apply the tactic sequence `refine ⟨hne _ ?_, hne _ ?_⟩ <;> simpa using hx`. Use `CotangentSum.pair_identity w w' ((n : ℂ) + 1) (hN w (by rw [hwim]; exact ha0)).1 (hN w (by rw [hwim]; exact ha0)).2 (hN w' (by rw [hw'im]; exact neg_ne_zero.mpr ha0)).1 (hN w' (by rw [hw'im]; exact neg_ne_zero.mpr ha0)).2 hdiff0` as an intermediate fact.

Simplify using `only [F, cotTerm]`. Use `push_cast`. Simplify using `only [← sub_eq_add_neg]`. Rewrite using `[← this]`. Establish `hw_mem : w ∈ Complex.integerComplement` using `hmem w (by rw [hwim]; exact ha0)`.

Establish `hw'_mem : w' ∈ Complex.integerComplement` using `hmem w' (by rw [hw'im]; exact neg_ne_zero.mpr ha0)`. Establish `h3 : ∑' n : ℕ, (F ((n + 1 : ℕ) : ℤ) + F (-((n + 1 : ℕ) : ℤ))) = (w - w')⁻¹ * ((π * cot (π * w') - 1 / w') - (π * cot (π * w) - 1 / w))`. Rewrite using `[tsum_congr hterm, tsum_mul_left, Summable.tsum_sub (summable_cotTerm hw'_mem) (summable_cotTerm hw_mem), cot_series_rep' hw'_mem, cot_series_rep' hw_mem]`. Establish `hF0 : F 0 = (w - w')⁻¹ * (1 / w' - 1 / w)`. Simplify using `only [F, Int.cast_zero, add_zero]`.

Use `hne w (by rw [hwim]; exact ha0)` as an intermediate fact. Use `hne w' (by rw [hw'im]; exact neg_ne_zero.mpr ha0)` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Establish `hS : ∑' n : ℤ, F n = (w - w')⁻¹ * (π * cot (π * w') - π * cot (π * w))`. Establish `h2' : ∑' n : ℕ, (F n + F (-n)) = (F 0 + F 0) + ∑' n : ℕ, (F ((n + 1 : ℕ) : ℤ) + F (-((n + 1 : ℕ) : ℤ)))`.

Rewrite using `[h2]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[h2', h3]`. Rewrite `h1` using `[hF0]`. Take the linear combination `-h1`.

Establish `hwH : 0 < w.im` using `by rw [hwim]; exact ha`. Establish `hq` using `pi_mul_cot_pi_q_exp ⟨w, hwH⟩`. Simplify using `only at hq`. Use `set q : ℂ := Complex.exp (2 * π * I * w) with hqdef`. Establish `hqn : ‖q‖ < 1` using `UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨w, hwH⟩`.

Establish `hgeo : ∑' n : ℕ, q ^ n = 1 + ∑' k : ℕ, q ^ (k + 1)`. Rewrite using `[(summable_geometric_of_norm_lt_one hqn).tsum_eq_zero_add]`. Simplify using the standard rewrite rules. Use `set T : ℂ := ∑' k : ℕ, q ^ (k + 1) with hT`. Establish `hcot' : π * cot (π * w') = conj (π * cot (π * w))`.

Rewrite using `[map_mul, conj_ofReal, ← cot_conj, map_mul, conj_ofReal, hconj]`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[Complex.ofReal_tsum, tsum_congr hF, hS, hcot', hq, hgeo]`. Establish `hTc : T + conj T = 2 * (T.re : ℂ)` using `by rw [Complex.add_conj]; push_cast; ring`. Simplify using `only [map_sub, map_mul, map_add, conj_ofReal, conj_I, map_one, map_ofNat]`.

Rewrite using `[hdiff]`. Establish `hI : I ≠ 0` using `I_ne_zero`. Establish `ha' : (a : ℂ) ≠ 0` using `ofReal_ne_zero.mpr ha0`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `2 * hTc`.
-/
theorem CotangentSum.proof : CotangentSum.Statement := by
  intro a u ha
  have hne : ∀ x : ℂ, x.im ≠ 0 → x ≠ 0 := fun x hx h => hx (by simp [h])
  have hmem : ∀ x : ℂ, x.im ≠ 0 → x ∈ Complex.integerComplement := by
    rintro x hx ⟨n, hn⟩
    apply hx
    rw [← hn]
    simp
  have ha0 : (a : ℝ) ≠ 0 := ha.ne'
  set w : ℂ := (u : ℂ) + (a : ℂ) * I with hw
  set w' : ℂ := (u : ℂ) - (a : ℂ) * I with hw'
  have hwim : w.im = a := by simp [hw]
  have hw'im : w'.im = -a := by simp [hw']
  have hconj : conj w = w' := by
    rw [hw, hw', map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
    ring
  have hdiff : w - w' = 2 * (a : ℂ) * I := by rw [hw, hw']; ring
  have hdiff0 : w - w' ≠ 0 := by
    rw [hdiff]; exact mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr ha0)) I_ne_zero

  let F : ℤ → ℂ := fun n => ((w + n) * (w' + n))⁻¹
  have hF : ∀ n : ℤ, ((((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-1 : ℝ) : ℝ) = F n := by
    intro n
    have e : (w + n) * (w' + n) = ((n : ℂ) + u) ^ 2 + (a : ℂ) ^ 2 := by
      rw [hw, hw']
      linear_combination (-(a : ℂ) ^ 2) * I_sq
    simp only [F, e, Real.rpow_neg_one]
    push_cast
    rfl
  have hsum : Summable F := by
    have h := (EisensteinSeries.linear_inv_isBigO_right 1 w').mul
      (EisensteinSeries.linear_inv_isBigO_right 1 w)
    refine EisensteinSeries.summable_inv_of_isBigO_rpow_inv (f := fun n : ℤ => (w + n) * (w' + n))
      (a := 2) (by norm_num) ?_
    simpa [pow_two, mul_inv] using! h

  have h1 := tsum_nat_add_neg hsum
  have h2 := (hsum.nat_add_neg).tsum_eq_zero_add
  have hterm : ∀ n : ℕ, F ((n + 1 : ℕ) : ℤ) + F (-((n + 1 : ℕ) : ℤ)) =
      (w - w')⁻¹ * (cotTerm w' n - cotTerm w n) := by
    intro n
    have hN : ∀ x : ℂ, x.im ≠ 0 → x + ((n : ℂ) + 1) ≠ 0 ∧ x - ((n : ℂ) + 1) ≠ 0 := by
      intro x hx
      refine ⟨hne _ ?_, hne _ ?_⟩ <;> simpa using hx
    have := CotangentSum.pair_identity w w' ((n : ℂ) + 1)
      (hN w (by rw [hwim]; exact ha0)).1 (hN w (by rw [hwim]; exact ha0)).2
      (hN w' (by rw [hw'im]; exact neg_ne_zero.mpr ha0)).1
      (hN w' (by rw [hw'im]; exact neg_ne_zero.mpr ha0)).2 hdiff0
    simp only [F, cotTerm]
    push_cast
    simp only [← sub_eq_add_neg]
    rw [← this]
  have hw_mem : w ∈ Complex.integerComplement := hmem w (by rw [hwim]; exact ha0)
  have hw'_mem : w' ∈ Complex.integerComplement :=
    hmem w' (by rw [hw'im]; exact neg_ne_zero.mpr ha0)
  have h3 : ∑' n : ℕ, (F ((n + 1 : ℕ) : ℤ) + F (-((n + 1 : ℕ) : ℤ))) =
      (w - w')⁻¹ * ((π * cot (π * w') - 1 / w') - (π * cot (π * w) - 1 / w)) := by
    rw [tsum_congr hterm, tsum_mul_left,
      Summable.tsum_sub (summable_cotTerm hw'_mem) (summable_cotTerm hw_mem),
      cot_series_rep' hw'_mem, cot_series_rep' hw_mem]
  have hF0 : F 0 = (w - w')⁻¹ * (1 / w' - 1 / w) := by
    simp only [F, Int.cast_zero, add_zero]
    have := hne w (by rw [hwim]; exact ha0)
    have := hne w' (by rw [hw'im]; exact neg_ne_zero.mpr ha0)
    field_simp
  have hS : ∑' n : ℤ, F n = (w - w')⁻¹ * (π * cot (π * w') - π * cot (π * w)) := by
    have h2' : ∑' n : ℕ, (F n + F (-n)) =
        (F 0 + F 0) + ∑' n : ℕ, (F ((n + 1 : ℕ) : ℤ) + F (-((n + 1 : ℕ) : ℤ))) := by
      rw [h2]; simp
    rw [h2', h3] at h1
    rw [hF0] at h1
    linear_combination -h1

  have hwH : 0 < w.im := by rw [hwim]; exact ha
  have hq := pi_mul_cot_pi_q_exp ⟨w, hwH⟩
  simp only at hq
  set q : ℂ := Complex.exp (2 * π * I * w) with hqdef
  have hqn : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨w, hwH⟩
  have hgeo : ∑' n : ℕ, q ^ n = 1 + ∑' k : ℕ, q ^ (k + 1) := by
    rw [(summable_geometric_of_norm_lt_one hqn).tsum_eq_zero_add]; simp
  set T : ℂ := ∑' k : ℕ, q ^ (k + 1) with hT
  have hcot' : π * cot (π * w') = conj (π * cot (π * w)) := by
    rw [map_mul, conj_ofReal, ← cot_conj, map_mul, conj_ofReal, hconj]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, tsum_congr hF, hS, hcot', hq, hgeo]
  have hTc : T + conj T = 2 * (T.re : ℂ) := by rw [Complex.add_conj]; push_cast; ring
  simp only [map_sub, map_mul, map_add, conj_ofReal, conj_I, map_one, map_ofNat]
  rw [hdiff]
  have hI : I ≠ 0 := I_ne_zero
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha0
  push_cast
  field_simp
  linear_combination 2 * hTc
