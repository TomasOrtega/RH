import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.I2

open Real

/- English proof (translation)
Establish `hπ1 : (3.14 : ℝ) < π` using `Real.pi_gt_d2`. Establish `hπ2 : π < 3.15` using `Real.pi_lt_d2`. Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hc0 : (0 : ℝ) ≤ c` using `Nat.cast_nonneg c`. Establish `hS0 : 0 ≤ Real.sqrt (q * (c + 1))` using `Real.sqrt_nonneg _`.

Establish `hS2 : Real.sqrt (q * (c + 1)) ^ 2 = q * (c + 1)` using `Real.sq_sqrt (by positivity)`. Establish `hA : 0 ≤ 2 * π * r * U` using `by positivity`. Establish `h1 : 2 * π * r * U + 5 * (r * Real.sqrt (q * (c + 1))) ≤ c`. Establish `e : r * (2 * π * U + 5 * Real.sqrt (q * (c + 1))) = 2 * π * r * U + 5 * (r * Real.sqrt (q * (c + 1)))` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `ha0 : 0 ≤ r * Real.sqrt (q * (c + 1))` using `mul_nonneg hr0 hS0`. Establish `ha : r * Real.sqrt (q * (c + 1)) ≤ c / 5` using `by linarith`. Establish `hX : (q * r ^ 2) * (c + 1) = (r * Real.sqrt (q * (c + 1))) ^ 2`. Rewrite using `[mul_pow, hS2]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hX0 : 0 ≤ q * r ^ 2` using `by positivity`. Establish `hXa : q * r ^ 2 ≤ (r * Real.sqrt (q * (c + 1))) / 5`. Establish `h2 : (q * r ^ 2) * (c + 1) ≤ (r * Real.sqrt (q * (c + 1))) / 5 * (c + 1)`. Rewrite using `[hX]`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `le_of_mul_le_mul_right h2 (by positivity)`. Establish `ht0 : 0 ≤ q * y ^ 2` using `by positivity`. Establish `hP0 : 0 ≤ r * q * y` using `by positivity`. Establish `hPsq : (r * q * y) ^ 2 = (q * r ^ 2) * (q * y ^ 2)` using `by ring`. Establish `hP : 2 * (r * q * y) ≤ 20 * (q * r ^ 2) + (q * y ^ 2) / 20`.

Use polynomial arithmetic with `[sq_nonneg (20 * (q * r ^ 2) - (q * y ^ 2) / 20)]`. Establish `F1 : π * (q * r ^ 2) ≤ 3.15 * (q * r ^ 2)` using `mul_le_mul_of_nonneg_right hπ2.le hX0`. Establish `F2 : π * (2 * (r * q * y)) ≤ π * (20 * (q * r ^ 2) + (q * y ^ 2) / 20)` using `mul_le_mul_of_nonneg_left hP Real.pi_pos.le`. Establish `F3 : π * (q * y ^ 2) ≤ 3.15 * (q * y ^ 2)` using `mul_le_mul_of_nonneg_right hπ2.le ht0`. Establish `F3' : 3.14 * (q * y ^ 2) ≤ π * (q * y ^ 2)` using `mul_le_mul_of_nonneg_right hπ1.le ht0`.

Establish `F4 : π * (q / 2) * y ^ 2 ≤ π * (q - M1) * y ^ 2`. Establish `: (q : ℝ) / 2 ≤ q - M1` using `by linarith`. Establish `hy2` using `sq_nonneg y`. Use `mul_le_mul_of_nonneg_left this Real.pi_pos.le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear relations using `[F1, F2, F3, F3', F4, h1, hXa, ha, ht, hA]`.
-/
theorem ct_expo_num (q c : ℕ) (hq : 1 ≤ q) {U y M1 r : ℝ} (hU : 0 ≤ U) (hy : 0 ≤ y)
    (hM : M1 ≤ q / 2) (hr0 : 0 ≤ r) (hr : r * (2 * π * U + 5 * Real.sqrt (q * (c + 1))) ≤ c)
    (ht : 28 * (c : ℝ) ≤ q * y ^ 2) :
    q * π * r ^ 2 / 2 + 2 * π * r * (U + q * y) - π * (q - M1) * y ^ 2 ≤
      1.07 * c - 1.33 * (q * y ^ 2) := by
  have hπ1 : (3.14 : ℝ) < π := Real.pi_gt_d2
  have hπ2 : π < 3.15 := Real.pi_lt_d2
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hS0 : 0 ≤ Real.sqrt (q * (c + 1)) := Real.sqrt_nonneg _
  have hS2 : Real.sqrt (q * (c + 1)) ^ 2 = q * (c + 1) := Real.sq_sqrt (by positivity)
  have hA : 0 ≤ 2 * π * r * U := by positivity
  have h1 : 2 * π * r * U + 5 * (r * Real.sqrt (q * (c + 1))) ≤ c := by
    have e : r * (2 * π * U + 5 * Real.sqrt (q * (c + 1))) =
        2 * π * r * U + 5 * (r * Real.sqrt (q * (c + 1))) := by ring
    linarith
  have ha0 : 0 ≤ r * Real.sqrt (q * (c + 1)) := mul_nonneg hr0 hS0
  have ha : r * Real.sqrt (q * (c + 1)) ≤ c / 5 := by linarith
  have hX : (q * r ^ 2) * (c + 1) = (r * Real.sqrt (q * (c + 1))) ^ 2 := by
    rw [mul_pow, hS2]; ring
  have hX0 : 0 ≤ q * r ^ 2 := by positivity
  have hXa : q * r ^ 2 ≤ (r * Real.sqrt (q * (c + 1))) / 5 := by
    have h2 : (q * r ^ 2) * (c + 1) ≤ (r * Real.sqrt (q * (c + 1))) / 5 * (c + 1) := by
      rw [hX]; nlinarith
    exact le_of_mul_le_mul_right h2 (by positivity)
  have ht0 : 0 ≤ q * y ^ 2 := by positivity
  have hP0 : 0 ≤ r * q * y := by positivity
  have hPsq : (r * q * y) ^ 2 = (q * r ^ 2) * (q * y ^ 2) := by ring
  have hP : 2 * (r * q * y) ≤ 20 * (q * r ^ 2) + (q * y ^ 2) / 20 := by
    nlinarith [sq_nonneg (20 * (q * r ^ 2) - (q * y ^ 2) / 20)]
  have F1 : π * (q * r ^ 2) ≤ 3.15 * (q * r ^ 2) := mul_le_mul_of_nonneg_right hπ2.le hX0
  have F2 : π * (2 * (r * q * y)) ≤ π * (20 * (q * r ^ 2) + (q * y ^ 2) / 20) :=
    mul_le_mul_of_nonneg_left hP Real.pi_pos.le
  have F3 : π * (q * y ^ 2) ≤ 3.15 * (q * y ^ 2) := mul_le_mul_of_nonneg_right hπ2.le ht0
  have F3' : 3.14 * (q * y ^ 2) ≤ π * (q * y ^ 2) := mul_le_mul_of_nonneg_right hπ1.le ht0
  have F4 : π * (q / 2) * y ^ 2 ≤ π * (q - M1) * y ^ 2 := by
    have : (q : ℝ) / 2 ≤ q - M1 := by linarith
    have hy2 := sq_nonneg y
    have := mul_le_mul_of_nonneg_left this Real.pi_pos.le
    nlinarith
  linarith [F1, F2, F3, F3', F4, h1, hXa, ha, ht, hA]

/- English proof (translation)
Establish `hc0 : (0 : ℝ) ≤ c` using `Nat.cast_nonneg c`. Break down `Nat.eq_zero_or_pos c with hc | hc` into its components or cases. Substitute `hc` using the available equality. Simplify using `only [Nat.cast_zero, zero_mul, zero_add, pow_zero] at hC5 ⊢`. Conclude with `Real.one_le_exp (by linarith)`.

Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hc1 : (1 : ℝ) ≤ c` using `by exact_mod_cast hc`. Establish `hqc1 : (1 : ℝ) ≤ q * c` using `by nlinarith`. Establish `hL0 : 0 ≤ Real.log (q * c)` using `Real.log_nonneg hqc1`. Establish `hS : 0 < Real.sqrt (q * (c + 1))` using `Real.sqrt_pos.mpr (by positivity)`.

Establish `hB : 0 < 6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))` using `by positivity`. Establish `hlogB : Real.log (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) = Real.log 6.5 + 1.07 + Real.log (q * (c + 1)) / 2`. Rewrite using `[Real.log_mul (by positivity) hS.ne', Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, Real.log_sqrt (by positivity)]`. Establish `h65 : Real.log 6.5 ≤ 3 * Real.log 2`. Establish `e : Real.log 8 = 3 * Real.log 2`.

Rewrite using `[show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num`. Rewrite using `[← e]`. Conclude with `Real.log_le_log (by norm_num) (by norm_num)`. Establish `h2` using `Real.log_two_lt_d9`. Establish `hqc : Real.log (q * (c + 1)) ≤ Real.log 2 + Real.log (q * c)`.

Rewrite using `[← Real.log_mul (by norm_num) (by positivity)]`. Conclude with `Real.log_le_log (by positivity) (by nlinarith)`. Establish `key : Real.log (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ≤ 0.56 * (7 + Real.log (q * c))`. Rewrite using `[hlogB]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[← Real.exp_log hB, ← Real.exp_nat_mul]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use `mul_le_mul_of_nonneg_left key hc0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ct_base_num (q c : ℕ) (hq : 1 ≤ q) {t0 : ℝ}
    (hC5 : 4 * (c : ℝ) * (7 + Real.log (q * c)) ≤ t0) :
    (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c ≤ Real.exp (0.14 * t0) := by
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero] at hC5 ⊢
    exact Real.one_le_exp (by linarith)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hqc1 : (1 : ℝ) ≤ q * c := by nlinarith
  have hL0 : 0 ≤ Real.log (q * c) := Real.log_nonneg hqc1
  have hS : 0 < Real.sqrt (q * (c + 1)) := Real.sqrt_pos.mpr (by positivity)
  have hB : 0 < 6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1)) := by positivity
  have hlogB : Real.log (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) =
      Real.log 6.5 + 1.07 + Real.log (q * (c + 1)) / 2 := by
    rw [Real.log_mul (by positivity) hS.ne', Real.log_mul (by norm_num) (Real.exp_pos _).ne',
      Real.log_exp, Real.log_sqrt (by positivity)]
  have h65 : Real.log 6.5 ≤ 3 * Real.log 2 := by
    have e : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    rw [← e]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h2 := Real.log_two_lt_d9
  have hqc : Real.log (q * (c + 1)) ≤ Real.log 2 + Real.log (q * c) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have key : Real.log (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ≤
      0.56 * (7 + Real.log (q * c)) := by
    rw [hlogB]; linarith
  rw [← Real.exp_log hB, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_left key hc0
  linarith

/- English proof (translation)
Establish `hsq : Real.sqrt Bsq ≤ 3.4642 * 2.263 ^ gA`. Establish `hm : 12 * (5.12 : ℝ) ^ gB ≤ (3.4642 * 2.263 ^ gA) ^ 2`. Rewrite using `[mul_pow, ← pow_mul, mul_comm gA 2, pow_mul]`. Apply `mul_le_mul (by norm_num) _ (by positivity) (by norm_num)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Establish `h3 : (2.263 : ℝ) ^ gA * Real.exp (-(0.19 * t0)) ≤ 2 ^ gA`. Establish `hl : Real.log 2.263 * 100 ≤ Real.log 2 * 119`. Establish `h` using `Real.log_le_log (by positivity) (show (2.263 : ℝ) ^ 100 ≤ 2 ^ 119 by norm_num)`. Rewrite `h` using `[Real.log_pow, Real.log_pow]`.

Move the coercions through the operations in `at h`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg0 : (0 : ℝ) ≤ gA` using `Nat.cast_nonneg gA`. Establish `hm` using `mul_le_mul_of_nonneg_left hl hg0`. Rewrite using `[← Real.exp_log (show (0 : ℝ) < 2.263 by norm_num), ← Real.exp_nat_mul, ← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul, ← Real.exp_add]`.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : (3 : ℝ) ^ dK ≤ 4.3 ^ dst` using `(pow_le_pow_left₀ (by norm_num) (by norm_num) dK).trans (pow_le_pow_right₀ (by norm_num) hdK)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ct_B_num (gA gB dK dst : ℕ) {t0 Bsq : ℝ} (hBsq0 : 0 ≤ Bsq) (hBsq : Bsq ≤ 12 * (5.12 : ℝ) ^ gB)
    (hgB : gB ≤ gA) (hdK : dK ≤ dst) (hC6 : (gA : ℝ) * Real.log 2 ≤ t0) :
    Real.sqrt Bsq * (2 * 3 ^ dK) * Real.exp (-(0.19 * t0)) ≤ 7 * 2 ^ gA * (4.3 : ℝ) ^ dst := by
  have hsq : Real.sqrt Bsq ≤ 3.4642 * 2.263 ^ gA := by
    have hm : 12 * (5.12 : ℝ) ^ gB ≤ (3.4642 * 2.263 ^ gA) ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm gA 2, pow_mul]
      apply mul_le_mul (by norm_num) _ (by positivity) (by norm_num)
      calc (5.12 : ℝ) ^ gB ≤ (2.263 ^ 2) ^ gB := pow_le_pow_left₀ (by norm_num) (by norm_num) gB
        _ ≤ (2.263 ^ 2) ^ gA := pow_le_pow_right₀ (by norm_num) hgB
    calc Real.sqrt Bsq ≤ Real.sqrt ((3.4642 * 2.263 ^ gA) ^ 2) := Real.sqrt_le_sqrt (hBsq.trans hm)
      _ = 3.4642 * 2.263 ^ gA := Real.sqrt_sq (by positivity)
  have h3 : (2.263 : ℝ) ^ gA * Real.exp (-(0.19 * t0)) ≤ 2 ^ gA := by
    have hl : Real.log 2.263 * 100 ≤ Real.log 2 * 119 := by
      have h := Real.log_le_log (by positivity) (show (2.263 : ℝ) ^ 100 ≤ 2 ^ 119 by norm_num)
      rw [Real.log_pow, Real.log_pow] at h
      push_cast at h
      linarith
    have hg0 : (0 : ℝ) ≤ gA := Nat.cast_nonneg gA
    have hm := mul_le_mul_of_nonneg_left hl hg0
    rw [← Real.exp_log (show (0 : ℝ) < 2.263 by norm_num), ← Real.exp_nat_mul,
      ← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have h4 : (3 : ℝ) ^ dK ≤ 4.3 ^ dst :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num) dK).trans (pow_le_pow_right₀ (by norm_num) hdK)
  calc Real.sqrt Bsq * (2 * 3 ^ dK) * Real.exp (-(0.19 * t0))
      ≤ (3.4642 * 2.263 ^ gA) * (2 * 4.3 ^ dst) * Real.exp (-(0.19 * t0)) := by gcongr
    _ = 6.9284 * ((2.263 : ℝ) ^ gA * Real.exp (-(0.19 * t0))) * 4.3 ^ dst := by ring
    _ ≤ 6.9284 * 2 ^ gA * 4.3 ^ dst := by gcongr
    _ ≤ 7 * 2 ^ gA * (4.3 : ℝ) ^ dst := by gcongr; norm_num

/- English proof (translation)
Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hc0 : (0 : ℝ) ≤ c` using `Nat.cast_nonneg c`. Establish `hS1 : 1 ≤ Real.sqrt (q * (c + 1))` using `Real.one_le_sqrt.mpr (by nlinarith)`. Establish `hn0 : 0 ≤ n` using `by linarith`. Establish `hbase : 2 * π * U + 5 * Real.sqrt (q * (c + 1)) ≤ 6.5 * Real.sqrt (q * (c + 1)) * n`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hpow : (2 * π * U + 5 * Real.sqrt (q * (c + 1))) ^ c ≤ (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * Real.exp (-(1.07 * c)) * n ^ c`. Establish `e : (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * Real.exp (-(1.07 * c)) = (6.5 * Real.sqrt (q * (c + 1))) ^ c`. Rewrite using `[mul_comm (6.5 : ℝ) (Real.exp 1.07), mul_assoc, mul_pow, ← Real.exp_nat_mul, mul_comm, ← mul_assoc, ← Real.exp_add]`. Put the polynomial expressions in normal form.

Simplify using the standard rewrite rules. Rewrite using `[e, ← mul_pow]`. Conclude with `pow_le_pow_left₀ (by positivity) hbase c`. Establish `hbn` using `ct_base_num q c hq hC5`. Establish `hX0 : 0 ≤ Real.sqrt Bsq * (2 * 3 ^ dK)` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Establish `: Real.exp (-(1.07 * c)) * Real.exp (1.07 * c) = 1`. Rewrite using `[← Real.exp_add]`. Simplify using the standard rewrite rules. Take the linear combination `((6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * n ^ c * (Real.sqrt Bsq * (2 * 3 ^ dK)) * Real.exp (-(1.33 * t0))) * this`.

Use `_ ≤ Real.exp (0.14 * t0) * n ^ c * (Real.sqrt Bsq * (2 * 3 ^ dK)) * Real.exp (-(1.33 * t0)) := by gcongr`. Use `_ = (Real.sqrt Bsq * (2 * 3 ^ dK) * Real.exp (-(0.19 * t0))) * Real.exp (-t0) * n ^ c := by`. Establish `: Real.exp (0.14 * t0) * Real.exp (-(1.33 * t0)) = Real.exp (-(0.19 * t0)) * Real.exp (-t0)`. Rewrite using `[← Real.exp_add, ← Real.exp_add]`. Put the polynomial expressions in normal form.

Take the linear combination `(n ^ c * (Real.sqrt Bsq * (2 * 3 ^ dK))) * this`. Use `_ ≤ 7 * 2 ^ gA * (4.3 : ℝ) ^ dst * Real.exp (-t0) * n ^ c := by gcongr`.
-/
theorem jet_product_le (q c dK gA dst : ℕ) (hq : 1 ≤ q) {n U t0 Bsq : ℝ} (hn : 1 ≤ n) (hU0 : 0 ≤ U)
    (hU : 2 * π * U ≤ 1.5 * n) (hC5 : 4 * (c : ℝ) * (7 + Real.log (q * c)) ≤ t0)
    (hB : Real.sqrt Bsq * (2 * 3 ^ dK) * Real.exp (-(0.19 * t0)) ≤ 7 * 2 ^ gA * (4.3 : ℝ) ^ dst) :
    (2 * π * U + 5 * Real.sqrt (q * (c + 1))) ^ c *
        (Real.sqrt Bsq * Real.exp (1.07 * c) * (2 * 3 ^ dK * Real.exp (-(1.33 * t0)))) ≤
      7 * 2 ^ gA * (4.3 : ℝ) ^ dst * Real.exp (-t0) * n ^ c := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hS1 : 1 ≤ Real.sqrt (q * (c + 1)) := Real.one_le_sqrt.mpr (by nlinarith)
  have hn0 : 0 ≤ n := by linarith
  have hbase : 2 * π * U + 5 * Real.sqrt (q * (c + 1)) ≤ 6.5 * Real.sqrt (q * (c + 1)) * n := by
    nlinarith
  have hpow : (2 * π * U + 5 * Real.sqrt (q * (c + 1))) ^ c ≤
      (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * Real.exp (-(1.07 * c)) * n ^ c := by
    have e : (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * Real.exp (-(1.07 * c)) =
        (6.5 * Real.sqrt (q * (c + 1))) ^ c := by
      rw [mul_comm (6.5 : ℝ) (Real.exp 1.07), mul_assoc, mul_pow, ← Real.exp_nat_mul, mul_comm,
        ← mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    rw [e, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase c
  have hbn := ct_base_num q c hq hC5
  have hX0 : 0 ≤ Real.sqrt Bsq * (2 * 3 ^ dK) := by positivity
  calc (2 * π * U + 5 * Real.sqrt (q * (c + 1))) ^ c *
        (Real.sqrt Bsq * Real.exp (1.07 * c) * (2 * 3 ^ dK * Real.exp (-(1.33 * t0))))
      ≤ (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * Real.exp (-(1.07 * c)) * n ^ c *
        (Real.sqrt Bsq * Real.exp (1.07 * c) * (2 * 3 ^ dK * Real.exp (-(1.33 * t0)))) := by
        gcongr
    _ = (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * n ^ c *
        (Real.sqrt Bsq * (2 * 3 ^ dK)) * Real.exp (-(1.33 * t0)) := by
        have : Real.exp (-(1.07 * c)) * Real.exp (1.07 * c) = 1 := by
          rw [← Real.exp_add]; simp
        linear_combination ((6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * n ^ c *
          (Real.sqrt Bsq * (2 * 3 ^ dK)) * Real.exp (-(1.33 * t0))) * this
    _ ≤ Real.exp (0.14 * t0) * n ^ c * (Real.sqrt Bsq * (2 * 3 ^ dK)) * Real.exp (-(1.33 * t0)) := by
        gcongr
    _ = (Real.sqrt Bsq * (2 * 3 ^ dK) * Real.exp (-(0.19 * t0))) * Real.exp (-t0) * n ^ c := by
        have : Real.exp (0.14 * t0) * Real.exp (-(1.33 * t0)) =
            Real.exp (-(0.19 * t0)) * Real.exp (-t0) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        linear_combination (n ^ c * (Real.sqrt Bsq * (2 * 3 ^ dK))) * this
    _ ≤ 7 * 2 ^ gA * (4.3 : ℝ) ^ dst * Real.exp (-t0) * n ^ c := by gcongr

end ReciprocityTheory.ChartRestriction.G.I2
