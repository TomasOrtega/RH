import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.NetSize

/- English proof (translation)
Use `Real.log_two_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_two_lt_d9; linarith

/- English proof (translation)
Establish `h2 : 0 < Real.log 2` using `Real.log_pos (by norm_num)`. Use `Real.pi_pos` as an intermediate fact. Unfold `epStar`. Conclude with `lt_min one_pos (by positivity)`.
-/
lemma eps_pos {M f w k : ℝ} (hM : 1 ≤ M) (hf : 1 ≤ f) (hw : 0 < w) (hk : 0 < k) :
    0 < epStar M f w k := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have := Real.pi_pos
  unfold epStar
  exact lt_min one_pos (by positivity)

/- English proof (translation)
Establish `hl2 : 0 < Real.log 2` using `Real.log_pos (by norm_num)`. Establish `hpi` using `Real.pi_gt_three`. Establish `hl1` using `log_two_le_one`. Unfold `epStar`. Break down `le_total 1 (Real.pi / (M * (f * w + 2) * k * Real.log 2)) with h | h` into its components or cases.

Rewrite using `[min_eq_left h, Real.log_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[min_eq_right h]`. Establish `hf0 : 0 < f` using `by linarith`. Establish `hM0 : 0 < M` using `by linarith`.

Establish `hfw : f * w ≤ Real.exp (5 * L)`. Rewrite using `[← Real.log_le_iff_le_exp (by positivity), Real.log_mul hf0.ne' hw.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `he : 1 ≤ Real.exp (5 * L)` using `Real.one_le_exp (by linarith)`. Establish `hA : Real.log (f * w + 2) ≤ 7 * L`.

Establish `h5 : f * w + 2 ≤ 2 ^ 2 * Real.exp (5 * L)` using `by linarith`. Establish `h6` using `Real.log_le_log (by positivity) h5`. Rewrite `h6` using `[Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_exp]`. Move the coercions through the operations in `at h6`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hB : Real.log (Real.log 2) ≤ Real.log Real.pi` using `Real.log_le_log hl2 (by linarith)`. Rewrite using `[Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hl2.ne', Real.log_mul (by positivity) hk.ne', Real.log_mul hM0.ne' (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma neg_log_eps_le {M f w k L : ℝ} (hM : 1 ≤ M) (hf : 1 ≤ f) (hw : 0 < w) (hk : 0 < k)
    (hL : 1 ≤ L) (h1 : Real.log f ≤ 2 * L) (h2 : Real.log M ≤ 30 * L)
    (h3 : Real.log w ≤ 3 * L) (h4 : Real.log k ≤ 4 * L) :
    -Real.log (epStar M f w k) ≤ 41 * L := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi := Real.pi_gt_three
  have hl1 := log_two_le_one
  unfold epStar
  rcases le_total 1 (Real.pi / (M * (f * w + 2) * k * Real.log 2)) with h | h
  · rw [min_eq_left h, Real.log_one]; linarith
  · rw [min_eq_right h]
    have hf0 : 0 < f := by linarith
    have hM0 : 0 < M := by linarith
    have hfw : f * w ≤ Real.exp (5 * L) := by
      rw [← Real.log_le_iff_le_exp (by positivity), Real.log_mul hf0.ne' hw.ne']
      linarith
    have he : 1 ≤ Real.exp (5 * L) := Real.one_le_exp (by linarith)
    have hA : Real.log (f * w + 2) ≤ 7 * L := by
      have h5 : f * w + 2 ≤ 2 ^ 2 * Real.exp (5 * L) := by linarith
      have h6 := Real.log_le_log (by positivity) h5
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_exp] at h6
      push_cast at h6
      linarith
    have hB : Real.log (Real.log 2) ≤ Real.log Real.pi :=
      Real.log_le_log hl2 (by linarith)
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hl2.ne',
      Real.log_mul (by positivity) hk.ne', Real.log_mul hM0.ne' (by positivity)]
    linarith

/- English proof (translation)
Introduce `f r L M w k0 dE s NA NC g hf hr hL hM hw hk hd hs hNA hNC hg lf lr lM lw lk ld ls lA lC lg`. Establish `he` using `eps_pos hM hf hw hk`. Establish `hle` using `neg_log_eps_le hM hf hw hk hL lf lM lw lk`. Establish `hl1` using `log_two_le_one`. Establish `hl2 : 0 < Real.log 2` using `Real.log_pos (by norm_num)`.

Use `set ε := epStar M f w k0`. Establish `hf0 : 0 < f` using `by linarith`. Establish `hr0 : 0 < r` using `by linarith`. Establish `hL0 : 0 < L` using `by linarith`. Establish `hd0 : 0 < dE` using `by linarith`.

Establish `hNA0 : 0 < NA` using `by linarith`. Establish `hNC0 : 0 < NC` using `by linarith`. Establish `hg0 : 0 < g` using `by linarith`. Establish `hfL : L ≤ f * L` using `le_mul_of_one_le_left hL0.le hf`. Use `set B := max 1 ((2 * f * r) ^ 4 * dE ^ 2 / (4 * ε)) with hBdef`.

Establish `hB1 : 1 ≤ B` using `le_max_left _ _`. Establish `hB0 : 0 < B` using `by linarith`. Establish `h4 : 0 ≤ Real.log 4` using `Real.log_nonneg (by norm_num)`. Establish `hB : Real.log B ≤ 65 * (f * L)`. Break down `le_total 1 ((2 * f * r) ^ 4 * dE ^ 2 / (4 * ε)) with h | h` into its components or cases.

Rewrite using `[hBdef, max_eq_right h, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity) …`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hBdef, max_eq_left h, Real.log_one]`. Check the signs of the components of the expression.

Establish `h3 : Real.log 3 ≤ 2`. Use `Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith` as an intermediate fact. Establish `T1 : Real.log (3 * NA * NC * g * r * B ^ 2) ≤ 223 * (f * L)`. Rewrite using `[Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h6 : Real.log 6000 ≤ 13`. Establish `h` using `Real.log_le_log (show (0:ℝ) < 6000 by norm_num) (show (6000:ℝ) ≤ 2 ^ 13 by norm_num)`. Rewrite `h` using `[Real.log_pow]`. Move the coercions through the operations in `at h`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `T2 : Real.log (6 * r ^ 2 / (1 / (1000 * r ^ 2 * (1 + s)))) ≤ 20 * (f * L)`. Establish `e : 6 * r ^ 2 / (1 / (1000 * r ^ 2 * (1 + s))) = 6000 * r ^ 4 * (1 + s)` using `by field_simp; ring`. Rewrite using `[e, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `T3 : Real.log (r * B) ≤ 66 * (f * L)`. Rewrite using `[Real.log_mul (by positivity) (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `T4 : Real.log 16 ≤ 4`.

Establish `: (16:ℝ) = 2 ^ 4` using `by norm_num`. Rewrite using `[this, Real.log_pow]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr23 : r ^ 2 ≤ r ^ 3` using `pow_le_pow_right₀ hr (by norm_num)`.

Establish `hP : f * r ^ 3 * (f * L) ≤ (f * r * L) ^ 3`. Establish `h1 : 1 ≤ f * L ^ 2` using `one_le_mul_of_one_le_of_one_le hf (one_le_pow₀ hL)`. Combine the equalities or inequalities in the displayed calculation. Establish `hQ : f * r ^ 2 * (f * L) ≤ f * r ^ 3 * (f * L)` using `by gcongr`. Establish `hone : 1 ≤ (f * r * L) ^ 3` using `one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hr) hL)`.

Establish `U1` using `mul_le_mul_of_nonneg_left T1 (show 0 ≤ 2 * f * r ^ 2 by positivity)`. Establish `U2` using `mul_le_mul_of_nonneg_left T2 (show 0 ≤ 2 * f * r ^ 2 by positivity)`. Establish `U3` using `mul_le_mul_of_nonneg_left T3 (show 0 ≤ 2 * f * r ^ 3 by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem net_size_cubic : ∀ (f r L M w k0 dE s NA NC g : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ L → 1 ≤ M → 0 < w → 0 < k0 → 1 ≤ dE → 0 ≤ s → 1 ≤ NA → 1 ≤ NC → 1 ≤ g → Real.log f ≤ 2 * L → Real.log r ≤ L → Real.log M ≤ 30 * L → Real.log w ≤ 3 * L → Real.log k0 ≤ 4 * L → Real.log dE ≤ 4 * f * L → Real.log (1 + s) ≤ 3 * L → Real.log NA ≤ 30 * f * L → Real.log NC ≤ 30 * f * L → Real.log g ≤ 30 * f * L → 2 * f * r ^ 2 * Real.log (3 * NA * NC * g * r * (max 1 ((2 * f * r) ^ 4 * dE ^ 2 / (4 * epStar M f w k0))) ^ 2) + (2 * f * r ^ 2 * Real.log (6 * r ^ 2 / (1 / (1000 * r ^ 2 * (1 + s)))) + 2 * f * r ^ 3 * Real.log (r * max 1 ((2 * f * r) ^ 4 * dE ^ 2 / (4 * epStar M f w k0)))) + Real.log 16 ≤ 1000 * (f * r * L) ^ 3 := by
  intro f r L M w k0 dE s NA NC g hf hr hL hM hw hk hd hs hNA hNC hg lf lr lM lw lk ld ls lA lC lg
  have he := eps_pos hM hf hw hk
  have hle := neg_log_eps_le hM hf hw hk hL lf lM lw lk
  have hl1 := log_two_le_one
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set ε := epStar M f w k0
  have hf0 : 0 < f := by linarith
  have hr0 : 0 < r := by linarith
  have hL0 : 0 < L := by linarith
  have hd0 : 0 < dE := by linarith
  have hNA0 : 0 < NA := by linarith
  have hNC0 : 0 < NC := by linarith
  have hg0 : 0 < g := by linarith
  have hfL : L ≤ f * L := le_mul_of_one_le_left hL0.le hf
  set B := max 1 ((2 * f * r) ^ 4 * dE ^ 2 / (4 * ε)) with hBdef
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 < B := by linarith
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hB : Real.log B ≤ 65 * (f * L) := by
    rcases le_total 1 ((2 * f * r) ^ 4 * dE ^ 2 / (4 * ε)) with h | h
    · rw [hBdef, max_eq_right h, Real.log_div (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
      push_cast
      linarith
    · rw [hBdef, max_eq_left h, Real.log_one]; positivity
  have h3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
  have T1 : Real.log (3 * NA * NC * g * r * B ^ 2) ≤ 223 * (f * L) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    linarith
  have h6 : Real.log 6000 ≤ 13 := by
    have h := Real.log_le_log (show (0:ℝ) < 6000 by norm_num) (show (6000:ℝ) ≤ 2 ^ 13 by norm_num)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have T2 : Real.log (6 * r ^ 2 / (1 / (1000 * r ^ 2 * (1 + s)))) ≤ 20 * (f * L) := by
    have e : 6 * r ^ 2 / (1 / (1000 * r ^ 2 * (1 + s))) = 6000 * r ^ 4 * (1 + s) := by
      field_simp; ring
    rw [e, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    linarith
  have T3 : Real.log (r * B) ≤ 66 * (f * L) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    linarith
  have T4 : Real.log 16 ≤ 4 := by
    have : (16:ℝ) = 2 ^ 4 := by norm_num
    rw [this, Real.log_pow]; push_cast; linarith
  have hr23 : r ^ 2 ≤ r ^ 3 := pow_le_pow_right₀ hr (by norm_num)
  have hP : f * r ^ 3 * (f * L) ≤ (f * r * L) ^ 3 := by
    have h1 : 1 ≤ f * L ^ 2 := one_le_mul_of_one_le_of_one_le hf (one_le_pow₀ hL)
    calc f * r ^ 3 * (f * L) ≤ f * r ^ 3 * (f * L) * (f * L ^ 2) :=
          le_mul_of_one_le_right (by positivity) h1
      _ = (f * r * L) ^ 3 := by ring
  have hQ : f * r ^ 2 * (f * L) ≤ f * r ^ 3 * (f * L) := by gcongr
  have hone : 1 ≤ (f * r * L) ^ 3 :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hr) hL)
  have U1 := mul_le_mul_of_nonneg_left T1 (show 0 ≤ 2 * f * r ^ 2 by positivity)
  have U2 := mul_le_mul_of_nonneg_left T2 (show 0 ≤ 2 * f * r ^ 2 by positivity)
  have U3 := mul_le_mul_of_nonneg_left T3 (show 0 ≤ 2 * f * r ^ 3 by positivity)
  linarith

end GlobalTheory.NetSize
