import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensSt

open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

/- English proof (translation)
Establish `h` using `isLittleO_log_rpow_rpow_atTop (7 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)`. Establish `hb` using `h.bound (show (0 : ℝ) < 1 / (|c| + 1) by positivity)`. Establish `hn` using `tendsto_natCast_atTop_atTop.eventually hb`. Take `⟨q₀, hq₀⟩` from `Filter.eventually_atTop.mp (hn.and (Filter.eventually_ge_atTop 1))`. Use `⟨q₀, fun q hq => ?_⟩` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `hq₀ q hq`. Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast h2`. Establish `hlog : 0 ≤ Real.log q` using `Real.log_nonneg hq1`. Rewrite `h1` using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog _), abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]`. Establish `e7 : Real.log q ^ (7 : ℝ) = Real.log q ^ 7`.

Conclude with `Real.rpow_natCast (Real.log q) 7` after adjusting the coercions. Rewrite `h1` using `[e7, ← Real.sqrt_eq_rpow]`. Establish `hs : 0 ≤ Real.sqrt q` using `Real.sqrt_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc]`.

Apply `mul_le_of_le_one_left hs` to reduce the goal to its premises. Rewrite using `[mul_one_div, div_le_one (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_pow_seven_le_sqrt (c : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → c * Real.log q ^ 7 ≤ Real.sqrt q := by
  have h := isLittleO_log_rpow_rpow_atTop (7 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
  have hb := h.bound (show (0 : ℝ) < 1 / (|c| + 1) by positivity)
  have hn := tendsto_natCast_atTop_atTop.eventually hb
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.mp (hn.and (Filter.eventually_ge_atTop 1))
  refine ⟨q₀, fun q hq => ?_⟩
  obtain ⟨h1, h2⟩ := hq₀ q hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h2
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog _),
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)] at h1
  have e7 : Real.log q ^ (7 : ℝ) = Real.log q ^ 7 := by
    exact_mod_cast Real.rpow_natCast (Real.log q) 7
  rw [e7, ← Real.sqrt_eq_rpow] at h1
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  calc c * Real.log q ^ 7 ≤ |c| * Real.log q ^ 7 :=
        mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
    _ ≤ |c| * (1 / (|c| + 1) * Real.sqrt q) := by gcongr
    _ ≤ Real.sqrt q := by
        rw [← mul_assoc]
        apply mul_le_of_le_one_left hs
        rw [mul_one_div, div_le_one (by positivity)]
        linarith

/- English proof (translation)
Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_log_of_three_le' {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/- English proof (translation)
Establish `hpow : 2 ^ Nat.log 2 q ≤ q` using `Nat.pow_log_le_self 2 (by omega)`. Establish `h1 : ((2 : ℝ) ^ Nat.log 2 q) ≤ q` using `by exact_mod_cast hpow`. Establish `h2 : (Nat.log 2 q : ℝ) * Real.log 2 ≤ Real.log q`. Rewrite using `[← Real.log_pow]`. Conclude with `Real.log_le_log (by positivity) h1`.

Establish `hl2` using `Real.log_two_gt_d9`. Establish `hlq : 1 ≤ Real.log q` using `one_le_log_of_three_le' (by exact_mod_cast hq)`. Establish `hn0 : (0 : ℝ) ≤ Nat.log 2 q` using `Nat.cast_nonneg _`. Establish `h3 : 0.6931471803 * (Nat.log 2 q : ℝ) ≤ Real.log q` using `by nlinarith`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dyadic_index_le_log (q : ℕ) (hq : 3 ≤ q) :
    ((8 * (Nat.log 2 q + 1) : ℕ) : ℝ) + 1 ≤ 25 * Real.log q := by
  have hpow : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have h1 : ((2 : ℝ) ^ Nat.log 2 q) ≤ q := by exact_mod_cast hpow
  have h2 : (Nat.log 2 q : ℝ) * Real.log 2 ≤ Real.log q := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h1
  have hl2 := Real.log_two_gt_d9
  have hlq : 1 ≤ Real.log q := one_le_log_of_three_le' (by exact_mod_cast hq)
  have hn0 : (0 : ℝ) ≤ Nat.log 2 q := Nat.cast_nonneg _
  have h3 : 0.6931471803 * (Nat.log 2 q : ℝ) ≤ Real.log q := by nlinarith
  push_cast
  linarith

/- English proof (translation)
Establish `hpow : 2 ^ Nat.log 2 q ≤ q` using `Nat.pow_log_le_self 2 (by omega)`. Generalize the expression as in `Nat.log 2 q = n at hpow ⊢`. Establish `h8 : 2 ^ (8 * (n + 1)) = 256 * (2 ^ n) ^ 8`. Rewrite using `[show 8 * (n + 1) = n * 8 + 8 by ring, pow_add, pow_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h9 : (2 ^ n) ^ 8 ≤ q ^ 8` using `Nat.pow_le_pow_left hpow 8`. Rewrite using `[h8]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dyadic_size_le_pow_twelve (q : ℕ) (hq : 512 ≤ q) :
    2 * (q ^ 3 * 2 ^ (8 * (Nat.log 2 q + 1))) ≤ q ^ 12 := by
  have hpow : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  generalize Nat.log 2 q = n at hpow ⊢
  have h8 : 2 ^ (8 * (n + 1)) = 256 * (2 ^ n) ^ 8 := by
    rw [show 8 * (n + 1) = n * 8 + 8 by ring, pow_add, pow_mul]
    ring
  have h9 : (2 ^ n) ^ 8 ≤ q ^ 8 := Nat.pow_le_pow_left hpow 8
  rw [h8]
  calc 2 * (q ^ 3 * (256 * (2 ^ n) ^ 8)) ≤ 2 * (q ^ 3 * (256 * q ^ 8)) := by gcongr
    _ = 512 * q ^ 11 := by ring
    _ ≤ q * q ^ 11 := by gcongr
    _ = q ^ 12 := by ring

/- English proof (translation)
Establish `hL : 0 < Lq` using `by linarith`. Establish `hlK : 0 ≤ l ^ 3 * K` using `by positivity`. Establish `step1 : 2 * u * l ^ 3 * K ≤ 2 * (1 / (q * s)) * l ^ 3 * K`. Use `mul_le_mul_of_nonneg_right hu hlK` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `step2 : 2 * (1 / (q * s)) * l ^ 3 * K ≤ 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (16 * q)` using `by gcongr`. Establish `step3 : 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (16 * q) = 70304 * Lq ^ 3 / s`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hJL : (c / (25 * Lq * Lq)) ^ 2 / 2 ≤ (c / (J * Lq)) ^ 2 / 2` using `by gcongr`.

Establish `hc' : 87880000 * Lq ^ 7 ≤ s * c ^ 2`. Rewrite `hc` using `[div_mul_eq_mul_div, div_le_iff₀ (by positivity)]`. Conclude with `hc`. Establish `step4 : 70304 * Lq ^ 3 / s ≤ (c / (25 * Lq * Lq)) ^ 2 / 2`. Establish `e : (c / (25 * Lq * Lq)) ^ 2 / 2 = c ^ 2 / (1250 * Lq ^ 4)`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, div_le_div_iff₀ hs (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem first_small_condition (u l K J q s Lq c : ℝ) (hq : 0 < q) (hs : 0 < s) (hc0 : 0 < c)
    (hu : u ≤ 1 / (q * s)) (hl0 : 0 ≤ l) (hl : l ≤ 13 * Lq) (hK0 : 0 ≤ K) (hK : K ≤ 16 * q)
    (hJ0 : 0 < J) (hJ : J ≤ 25 * Lq) (hc : 87880000 / c ^ 2 * Lq ^ 7 ≤ s) :
    2 * u * l ^ 3 * K ≤ (c / (J * Lq)) ^ 2 / 2 := by
  have hL : 0 < Lq := by linarith
  have hlK : 0 ≤ l ^ 3 * K := by positivity
  have step1 : 2 * u * l ^ 3 * K ≤ 2 * (1 / (q * s)) * l ^ 3 * K := by
    have := mul_le_mul_of_nonneg_right hu hlK
    nlinarith
  have step2 : 2 * (1 / (q * s)) * l ^ 3 * K ≤ 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (16 * q) := by
    gcongr
  have step3 : 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (16 * q) = 70304 * Lq ^ 3 / s := by
    field_simp
    ring
  have hJL : (c / (25 * Lq * Lq)) ^ 2 / 2 ≤ (c / (J * Lq)) ^ 2 / 2 := by
    gcongr
  have hc' : 87880000 * Lq ^ 7 ≤ s * c ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hc
    exact hc
  have step4 : 70304 * Lq ^ 3 / s ≤ (c / (25 * Lq * Lq)) ^ 2 / 2 := by
    have e : (c / (25 * Lq * Lq)) ^ 2 / 2 = c ^ 2 / (1250 * Lq ^ 4) := by
      field_simp
      ring
    rw [e, div_le_div_iff₀ hs (by positivity)]
    nlinarith
  linarith

/- English proof (translation)
Establish `hq' : (1 : ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hq3 : (1 : ℝ) ≤ (q : ℝ) ^ 3` using `one_le_pow₀ hq'`. Establish `hU' : (q : ℝ) ^ 3 ≤ U` using `by exact_mod_cast hU`. Establish `h1 : (U : ℝ) ^ (1 - 2 * σ) ≤ (U : ℝ) ^ (-(1 / 2) : ℝ)` using `Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)`. Establish `h2 : (U : ℝ) ^ (-(1 / 2) : ℝ) ≤ ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ)` using `Real.rpow_le_rpow_of_nonpos (by positivity) hU' (by norm_num)`.

Establish `h3 : ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) = 1 / ((q : ℝ) * Real.sqrt q)`. Rewrite using `[Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]`. Use `congr 1`. Rewrite using `[show (q : ℝ) ^ 3 = (q : ℝ) ^ 2 * q by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rpow_neg_exponent_bound (q U : ℕ) (σ : ℝ) (hq : 1 ≤ q) (hσ : 3 / 4 ≤ σ) (hU : q ^ 3 ≤ U) :
    (U : ℝ) ^ (1 - 2 * σ) ≤ 1 / ((q : ℝ) * Real.sqrt q) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq3 : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ hq'
  have hU' : (q : ℝ) ^ 3 ≤ U := by exact_mod_cast hU
  have h1 : (U : ℝ) ^ (1 - 2 * σ) ≤ (U : ℝ) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : (U : ℝ) ^ (-(1 / 2) : ℝ) ≤ ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hU' (by norm_num)
  have h3 : ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) = 1 / ((q : ℝ) * Real.sqrt q) := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
    congr 1
    rw [show (q : ℝ) ^ 3 = (q : ℝ) ^ 2 * q by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  linarith

/- English proof (translation)
Establish `he : 0 ≤ 2 - 2 * σ` using `by linarith`. Establish `hq0 : (0 : ℝ) ≤ q` using `Nat.cast_nonneg q`. Establish `hUq : (U : ℝ) ≤ (q : ℝ) ^ 12` using `by exact_mod_cast hU`. Establish `s1 : (U : ℝ) ^ (2 - 2 * σ) ≤ ((q : ℝ) ^ 12) ^ (2 - 2 * σ)` using `Real.rpow_le_rpow (Nat.cast_nonneg _) hUq he`. Establish `s2 : ((q : ℝ) ^ 12) ^ (2 - 2 * σ) ≤ ((2 * x) ^ 12) ^ (2 - 2 * σ)`.

Apply `Real.rpow_le_rpow (by positivity) _ he` to reduce the goal to its premises. Use `gcongr`. Establish `s3 : ((2 * x) ^ 12) ^ (2 - 2 * σ) = (2 : ℝ) ^ (24 * (1 - σ)) * x ^ (24 * (1 - σ))`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hx.le]`. Rewrite using `[show ((12 : ℕ) : ℝ) * (2 - 2 * σ) = 24 * (1 - σ) by push_cast; ring]`.

Establish `s4 : (2 : ℝ) ^ (24 * (1 - σ)) ≤ 64`. Combine the equalities or inequalities in the displayed calculation. Establish `hx' : 0 ≤ x ^ (24 * (1 - σ))` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← s3]`.

Conclude with `s1.trans s2`. Use `_ ≤ 64 * x ^ (24 * (1 - σ)) := by gcongr`.
-/
theorem rpow_pos_exponent_bound (q U : ℕ) (x σ : ℝ) (hx : 0 < x) (hqx : (q : ℝ) ≤ 2 * x) (hσ : 3 / 4 ≤ σ)
    (hσ1 : σ ≤ 1) (hU : U ≤ q ^ 12) : (U : ℝ) ^ (2 - 2 * σ) ≤ 64 * x ^ (24 * (1 - σ)) := by
  have he : 0 ≤ 2 - 2 * σ := by linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hUq : (U : ℝ) ≤ (q : ℝ) ^ 12 := by exact_mod_cast hU
  have s1 : (U : ℝ) ^ (2 - 2 * σ) ≤ ((q : ℝ) ^ 12) ^ (2 - 2 * σ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hUq he
  have s2 : ((q : ℝ) ^ 12) ^ (2 - 2 * σ) ≤ ((2 * x) ^ 12) ^ (2 - 2 * σ) := by
    apply Real.rpow_le_rpow (by positivity) _ he
    gcongr
  have s3 : ((2 * x) ^ 12) ^ (2 - 2 * σ) = (2 : ℝ) ^ (24 * (1 - σ)) * x ^ (24 * (1 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hx.le]
    rw [show ((12 : ℕ) : ℝ) * (2 - 2 * σ) = 24 * (1 - σ) by push_cast; ring]
  have s4 : (2 : ℝ) ^ (24 * (1 - σ)) ≤ 64 := by
    calc (2 : ℝ) ^ (24 * (1 - σ)) ≤ (2 : ℝ) ^ ((6 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = 64 := by rw [Real.rpow_natCast]; norm_num
  have hx' : 0 ≤ x ^ (24 * (1 - σ)) := by positivity
  calc (U : ℝ) ^ (2 - 2 * σ) ≤ (2 : ℝ) ^ (24 * (1 - σ)) * x ^ (24 * (1 - σ)) := by
        rw [← s3]; exact s1.trans s2
    _ ≤ 64 * x ^ (24 * (1 - σ)) := by gcongr

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
