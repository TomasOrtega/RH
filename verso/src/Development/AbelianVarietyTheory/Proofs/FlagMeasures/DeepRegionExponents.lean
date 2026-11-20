import Mathlib

open Matrix Finset Real

namespace GlobalTheory

/- English proof (translation)
Establish `hX0 : 0 < X` using `by linarith`. Take `⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = X ^ q` from `⟨_, rfl⟩`. Establish `hXY : X ≤ Y`. Rewrite using `[hYdef]; simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ X) hq`. Establish `hY16 : 16 ≤ Y` using `le_trans hX hXY`.

Establish `hY0 : 0 < Y` using `by linarith`. Establish `hτY : τ * Y ^ 11 ≤ 1`. Establish `h1 : X⁻¹ ^ (11 * q) * Y ^ 11 = 1`. Rewrite using `[hYdef, ← pow_mul, inv_pow, mul_comm q 11]`. Conclude with `inv_mul_cancel₀ (by positivity)`.

Combine the equalities or inequalities in the displayed calculation. Establish `hA : Y ^ 96 * τ ^ 12 * Y ^ 36 ≤ 1`. Establish `e : Y ^ 96 * τ ^ 12 * Y ^ 36 = (τ * Y ^ 11) ^ 12` using `by ring`. Rewrite using `[e]`. Conclude with `pow_le_one₀ (by positivity) hτY`.

Establish `hB : be * n * g ^ 2 * X ≤ Y ^ 10`. Combine the equalities or inequalities in the displayed calculation. Establish `hC0 : 0 ≤ (Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X)` using `by positivity`. Establish `hC : (Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X) * 16 ^ 26 ≤ 1`. Combine the equalities or inequalities in the displayed calculation.

Establish `hE : Real.exp 1 < 3` using `lt_trans Real.exp_one_lt_d9 (by norm_num)`. Establish `hE' : 1 / 3 ≤ Real.exp (-1)`. Establish `h` using `one_div_le_one_div_of_le (Real.exp_pos 1) hE.le`. Rewrite using `[Real.exp_neg, ← one_div]` and apply the resulting hypothesis. Establish `hXq : X ^ (96 * q) = Y ^ 96` using `by rw [hYdef, ← pow_mul, mul_comm]`.

Establish `hτ0 : τ ≠ 0` using `hτ.ne'`. Establish `e : Y ^ 96 * (2 * τ) ^ 16 * (6 * be * Real.exp 1 * (289 * n / τ ^ 4)) * g ^ 2 * X = (2 ^ 16 * 6 * 289) * Real.exp 1 * ((Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X))`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hXq, e]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem deep_exponent_core (X τ be n g : ℝ) (q : ℕ) (hX : 16 ≤ X) (hq : 1 ≤ q) (hτ : 0 < τ)
    (hτX : τ ≤ X⁻¹ ^ (11 * q)) (hbe0 : 0 ≤ be) (hbe : be ≤ X ^ 6) (hn0 : 0 ≤ n) (hn : n ≤ X)
    (hg0 : 0 ≤ g) (hg : g ≤ X) :
    (X ^ (96 * q) * (2 * τ) ^ 16) * ((6 * be) * Real.exp 1 * (289 * n / τ ^ 4)) * g ^ 2 * X
      ≤ Real.exp (-1) := by
  have hX0 : 0 < X := by linarith
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = X ^ q := ⟨_, rfl⟩
  have hXY : X ≤ Y := by
    rw [hYdef]; simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ X) hq
  have hY16 : 16 ≤ Y := le_trans hX hXY
  have hY0 : 0 < Y := by linarith
  have hτY : τ * Y ^ 11 ≤ 1 := by
    have h1 : X⁻¹ ^ (11 * q) * Y ^ 11 = 1 := by
      rw [hYdef, ← pow_mul, inv_pow, mul_comm q 11]
      exact inv_mul_cancel₀ (by positivity)
    calc τ * Y ^ 11 ≤ X⁻¹ ^ (11 * q) * Y ^ 11 := by gcongr
      _ = 1 := h1
  have hA : Y ^ 96 * τ ^ 12 * Y ^ 36 ≤ 1 := by
    have e : Y ^ 96 * τ ^ 12 * Y ^ 36 = (τ * Y ^ 11) ^ 12 := by ring
    rw [e]
    exact pow_le_one₀ (by positivity) hτY
  have hB : be * n * g ^ 2 * X ≤ Y ^ 10 :=
    calc be * n * g ^ 2 * X ≤ X ^ 6 * X * X ^ 2 * X := by gcongr
      _ = X ^ 10 := by ring
      _ ≤ Y ^ 10 := by gcongr
  have hC0 : 0 ≤ (Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X) := by positivity
  have hC : (Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X) * 16 ^ 26 ≤ 1 :=
    calc (Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X) * 16 ^ 26
        ≤ (Y ^ 96 * τ ^ 12) * Y ^ 10 * Y ^ 26 := by gcongr
      _ = Y ^ 96 * τ ^ 12 * Y ^ 36 := by ring
      _ ≤ 1 := hA
  have hE : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hE' : 1 / 3 ≤ Real.exp (-1) := by
    have h := one_div_le_one_div_of_le (Real.exp_pos 1) hE.le
    rwa [Real.exp_neg, ← one_div]
  have hXq : X ^ (96 * q) = Y ^ 96 := by rw [hYdef, ← pow_mul, mul_comm]
  have hτ0 : τ ≠ 0 := hτ.ne'
  have e : Y ^ 96 * (2 * τ) ^ 16 * (6 * be * Real.exp 1 * (289 * n / τ ^ 4)) * g ^ 2 * X
      = (2 ^ 16 * 6 * 289) * Real.exp 1 * ((Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X)) := by
    field_simp
  rw [hXq, e]
  calc (2 ^ 16 * 6 * 289) * Real.exp 1 * ((Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X))
      ≤ (2 ^ 16 * 6 * 289) * 3 * ((Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE.le (by norm_num)) hC0
    _ ≤ 1 / 3 := by norm_num at hC ⊢; linarith
    _ ≤ Real.exp (-1) := hE'

/- English proof (translation)
Introduce `n f q rd g b τ hn hf hq hqn hrd hb hg hτ hτP N rh be`. Establish `hN : N = n ^ 2 * f` using `rfl`. Establish `hrh : rh = (n : ℝ) ^ 2 * Real.sqrt f * g * rd * (2 * τ) ^ ((1 : ℝ) / q) / 4` using `rfl`. Establish `hbe : be = Real.sqrt n * b ^ 2 + 1.5 * (n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ)` using `rfl`. Use `clear_value N rh be`.

Generalize the expression as in `hPdef : ((n : ℝ) * f * rd * g * b) = P at hτP ⊢`. Establish `hn8 : (8 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hf1 : (1 : ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hqn' : (q : ℝ) ≤ n`. Establish `h : q ≤ n` using `le_trans (by nlinarith) hqn`.

Conclude with `h` after adjusting the coercions. Establish `hq0 : q ≠ 0` using `by omega`. Establish `hNr : (N : ℝ) = (n : ℝ) ^ 2 * f` using `by rw [hN]; push_cast; ring`. Establish `hn0 : (0 : ℝ) ≤ n` using `by linarith`. Establish `hf0 : (0 : ℝ) ≤ f` using `by linarith`.

Establish `hrd0 : 0 ≤ rd` using `by linarith`. Establish `hg0 : 0 ≤ g` using `by linarith`. Establish `hb0 : 0 ≤ b` using `by linarith`. Establish `hnf : (n : ℝ) ≤ n * f` using `le_mul_of_one_le_right hn0 hf1`. Establish `hnfr : (n : ℝ) * f ≤ n * f * rd` using `le_mul_of_one_le_right (by positivity) hrd`.

Establish `hnfrg : (n : ℝ) * f * rd ≤ n * f * rd * g` using `le_mul_of_one_le_right (by positivity) hg`. Establish `hmP : (n : ℝ) * f * rd * g ≤ P`. Rewrite using `[← hPdef]; exact le_mul_of_one_le_right (by positivity) (by linarith)`. Establish `hP16 : (16 : ℝ) ≤ P`. Rewrite using `[← hPdef]`.

Combine the linear relations using `[mul_le_mul (by linarith : (8 : ℝ) ≤ n * f * rd * g) hb (by norm_num) (by positivity)]`. Establish `hP0 : 0 ≤ P` using `by linarith`. Establish `hnP : (n : ℝ) ≤ P` using `by linarith`. Establish `hnfP : (n : ℝ) * f ≤ P` using `by linarith`. Establish `hgP : g ≤ P`.

Establish `h : g ≤ n * f * rd * g` using `le_mul_of_one_le_left hg0 (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbP : b ≤ P`. Rewrite using `[← hPdef]; exact le_mul_of_one_le_left hb0 (by linarith)`. Establish `hnbP : (n : ℝ) * b ≤ P`.

Rewrite using `[← hPdef]; exact mul_le_mul_of_nonneg_right (by linarith) hb0`. Establish `hnmP : (n : ℝ) * (n * f * rd * g) ≤ P ^ 2`. Rewrite using `[sq]; exact mul_le_mul hnP hmP (by positivity) hP0`. Establish `hs2 : Real.sqrt n ^ 2 = n` using `Real.sq_sqrt hn0`. Establish `hs1 : 1 ≤ Real.sqrt n`.

Rewrite using `[show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)`. Establish `hsn : Real.sqrt n ≤ n`. Combine the equalities or inequalities in the displayed calculation. Establish `hfs : Real.sqrt f * Real.sqrt f = f` using `Real.mul_self_sqrt hf0`. Establish `hf1s : 1 ≤ Real.sqrt f`.

Rewrite using `[show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hf1`. Establish `hsf : Real.sqrt f ≤ f`. Combine the equalities or inequalities in the displayed calculation. Establish `h32 : (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ 2`. Rewrite using `[← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)`.

Establish `hcast : ((8 * q * N + N : ℕ) : ℝ) ≤ 9 * (n : ℝ) ^ 3 * f`. Use `push_cast`. Rewrite using `[hNr]`. Combine the linear relations using `[mul_nonneg (sub_nonneg.2 hqn') (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f), mul_nonneg (by linarith : (0 : ℝ) ≤ n - 1) (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f)]`. Establish `t1 : Real.sqrt n * b ^ 2 ≤ P ^ 2`.

Combine the equalities or inequalities in the displayed calculation. Establish `t2 : (n : ℝ) ^ 2 ≤ P ^ 2` using `pow_le_pow_left₀ hn0 hnP 2`. Establish `t3 : (n : ℝ) ^ 3 * f ≤ P ^ 3`. Combine the equalities or inequalities in the displayed calculation. Establish `hP23 : P ^ 2 ≤ P ^ 3` using `pow_le_pow_right₀ (by linarith) (by norm_num)`.

Establish `hbe0 : 0 ≤ be` using `by rw [hbe]; positivity`. Establish `hbeP : be ≤ 30 * P ^ 3` using `by rw [hbe]; linarith`. Establish `hP3 : (30 : ℝ) ≤ P ^ 3`. Establish `h` using `pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) hP16 3`. Evaluate the numerical expressions using `at h`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbe6 : be ≤ P ^ 6` using `by linarith [mul_le_mul_of_nonneg_right hP3 (by positivity : (0 : ℝ) ≤ P ^ 3)]`. Establish `hK : (n : ℝ) ^ 2 * f * g * rd * be / 2 ≤ P ^ 6`. Establish `e : (n : ℝ) ^ 2 * f * g * rd * be / 2 = (n * (n * f * rd * g)) * be / 2` using `by ring`. Rewrite using `[e]`.

Establish `h : (n * (n * f * rd * g)) * be ≤ P ^ 2 * (30 * P ^ 3)` using `mul_le_mul hnmP hbeP hbe0 (by positivity)`. Combine the linear relations using `[mul_nonneg (pow_nonneg hP0 5) (by linarith : (0 : ℝ) ≤ P - 15)]`. Establish `hsq : ((2 * τ) ^ ((1 : ℝ) / q)) ^ q = 2 * τ`. Rewrite using `[one_div]; exact Real.rpow_inv_natCast_pow (by positivity) hq0`. Take `⟨s, hsdef⟩ : ∃ s : ℝ, s = (2 * τ) ^ ((1 : ℝ) / q)` from `⟨_, rfl⟩`.

Rewrite `hsq`, `hrh` using `[← hsdef]`. Establish `hs0 : 0 ≤ s` using `by rw [hsdef]; positivity`. Establish `hτP' : τ * P ^ (11 * q) ≤ 1`. Establish `h1 : P⁻¹ ^ (11 * q) * P ^ (11 * q) = 1`. Rewrite using `[inv_pow]; exact inv_mul_cancel₀ (by positivity)`.

Combine the equalities or inequalities in the displayed calculation. Establish `hu : (s * P ^ 11) ^ q ≤ 2 ^ q`. Combine the equalities or inequalities in the displayed calculation. Establish `hsP : s * P ^ 11 ≤ 2` using `(pow_le_pow_iff_left₀ (by positivity) (by norm_num) hq0).1 hu`. Establish `hrh0 : 0 ≤ rh` using `by rw [hrh]; positivity`.

Prove the components needed by the constructor for the conclusion. Establish `hP211 : P ^ 2 ≤ P ^ 11` using `pow_le_pow_right₀ (by linarith) (by norm_num)`. Establish `hA1 : (n : ℝ) ^ 2 * Real.sqrt f * g * rd ≤ P ^ 2`. Combine the equalities or inequalities in the displayed calculation. Establish `h : (n : ℝ) ^ 2 * Real.sqrt f * g * rd * s ≤ P ^ 11 * s`.

Combine the equalities or inequalities in the displayed calculation. Establish `hl` using `Real.log_two_gt_d9`. Rewrite using `[hrh]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hAeq : 2 * rh * Real.sqrt f * be = ((n : ℝ) ^ 2 * f * g * rd * be / 2) * s`.

Rewrite using `[hrh]`. Take the linear combination `((n : ℝ) ^ 2 * g * rd * s * be / 2) * hfs`. Establish `hA16 : (2 * rh * Real.sqrt f * be) ^ (16 * q) ≤ P ^ (96 * q) * (2 * τ) ^ 16`. Rewrite using `[hAeq]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_pow, ← pow_mul, show 6 * (16 * q) = 96 * q by ring, show 16 * q = q * 16 by ring, pow_mul s q 16, hsq]`. Establish `hW` using `deep_exponent_core P τ be n g q hP16 hq hτ hτP hbe0 hbe6 hn0 hnP hg0 hgP`. Establish `hsq17 : (17 * Real.sqrt n / τ ^ 2) ^ 2 = 289 * (n : ℝ) / τ ^ 4`. Rewrite using `[div_pow, mul_pow, hs2, ← pow_mul]`. Evaluate the numerical expressions.

Establish `hexp : Real.exp f ≤ Real.exp 1 ^ N`. Rewrite using `[← Real.exp_nat_mul]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Rewrite using `[hNr]`. Establish `h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2` using `le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) (by linarith : (1 : ℝ) ≤ n) 2)`.

Combine the linear relations using `[mul_le_mul_of_nonneg_right h1 hf0]`. Establish `e1 : (2 * rh * Real.sqrt f * be) ^ (2 * (8 * q * N)) = ((2 * rh * Real.sqrt f * be) ^ (16 * q)) ^ N`. Rewrite using `[← pow_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : (17 * Real.sqrt n / τ ^ 2) ^ (2 * N) = (289 * (n : ℝ) / τ ^ 4) ^ N`. Rewrite using `[pow_mul, hsq17]`. Establish `e3 : g ^ (2 * N) = (g ^ 2) ^ N` using `pow_mul g 2 N`. Rewrite using `[e1, e2, e3]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [mul_pow]`. Use `_ ≤ Real.exp (-1) ^ N := pow_le_pow_left₀ (by positivity) hW N`. Use `_ = Real.exp (-(N : ℝ)) := by`. Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem deep_region_exponents : ∀ (n f q : ℕ) (rd g b : ℝ) (τ : ℝ), 8 ≤ n → 1 ≤ f → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ rd → 2 ≤ b → 1 ≤ g → 0 < τ → τ ≤ ((n : ℝ) * f * rd * g * b)⁻¹ ^ (11 * q) → let N : ℕ := n ^ 2 * f; let rh : ℝ := (n : ℝ) ^ 2 * Real.sqrt f * g * rd * (2 * τ) ^ ((1 : ℝ) / q) / 4; let be : ℝ := Real.sqrt n * b ^ 2 + 1.5 * (n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ); rh ≤ Real.log 2 ∧ (2 * rh * Real.sqrt f * be) ^ (2 * (8 * q * N)) * ((6 * be) ^ N * Real.exp f * (17 * Real.sqrt n / τ ^ 2) ^ (2 * N)) * g ^ (2 * N) * ((n : ℝ) * f * rd * g * b) ^ N ≤ Real.exp (-(N : ℝ)) := by
  intro n f q rd g b τ hn hf hq hqn hrd hb hg hτ hτP N rh be
  have hN : N = n ^ 2 * f := rfl
  have hrh : rh = (n : ℝ) ^ 2 * Real.sqrt f * g * rd * (2 * τ) ^ ((1 : ℝ) / q) / 4 := rfl
  have hbe : be = Real.sqrt n * b ^ 2 + 1.5 * (n : ℝ) ^ ((3 : ℝ) / 2)
      + 3 * ((8 * q * N + N : ℕ) : ℝ) := rfl
  clear_value N rh be
  generalize hPdef : ((n : ℝ) * f * rd * g * b) = P at hτP ⊢
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hqn' : (q : ℝ) ≤ n := by
    have h : q ≤ n := le_trans (by nlinarith) hqn
    exact_mod_cast h
  have hq0 : q ≠ 0 := by omega
  have hNr : (N : ℝ) = (n : ℝ) ^ 2 * f := by rw [hN]; push_cast; ring
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hf0 : (0 : ℝ) ≤ f := by linarith
  have hrd0 : 0 ≤ rd := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hnf : (n : ℝ) ≤ n * f := le_mul_of_one_le_right hn0 hf1
  have hnfr : (n : ℝ) * f ≤ n * f * rd := le_mul_of_one_le_right (by positivity) hrd
  have hnfrg : (n : ℝ) * f * rd ≤ n * f * rd * g := le_mul_of_one_le_right (by positivity) hg
  have hmP : (n : ℝ) * f * rd * g ≤ P := by
    rw [← hPdef]; exact le_mul_of_one_le_right (by positivity) (by linarith)
  have hP16 : (16 : ℝ) ≤ P := by
    rw [← hPdef]
    linarith [mul_le_mul (by linarith : (8 : ℝ) ≤ n * f * rd * g) hb (by norm_num) (by positivity)]
  have hP0 : 0 ≤ P := by linarith
  have hnP : (n : ℝ) ≤ P := by linarith
  have hnfP : (n : ℝ) * f ≤ P := by linarith
  have hgP : g ≤ P := by
    have h : g ≤ n * f * rd * g := le_mul_of_one_le_left hg0 (by linarith)
    linarith
  have hbP : b ≤ P := by
    rw [← hPdef]; exact le_mul_of_one_le_left hb0 (by linarith)
  have hnbP : (n : ℝ) * b ≤ P := by
    rw [← hPdef]; exact mul_le_mul_of_nonneg_right (by linarith) hb0
  have hnmP : (n : ℝ) * (n * f * rd * g) ≤ P ^ 2 := by
    rw [sq]; exact mul_le_mul hnP hmP (by positivity) hP0
  have hs2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0
  have hs1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hsn : Real.sqrt n ≤ n :=
    calc Real.sqrt n = Real.sqrt n * 1 := by ring
      _ ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left hs1 (Real.sqrt_nonneg n)
      _ = n := Real.mul_self_sqrt hn0
  have hfs : Real.sqrt f * Real.sqrt f = f := Real.mul_self_sqrt hf0
  have hf1s : 1 ≤ Real.sqrt f := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hf1
  have hsf : Real.sqrt f ≤ f :=
    calc Real.sqrt f = Real.sqrt f * 1 := by ring
      _ ≤ Real.sqrt f * Real.sqrt f := mul_le_mul_of_nonneg_left hf1s (Real.sqrt_nonneg f)
      _ = f := hfs
  have h32 : (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ 2 := by
    rw [← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hcast : ((8 * q * N + N : ℕ) : ℝ) ≤ 9 * (n : ℝ) ^ 3 * f := by
    push_cast
    rw [hNr]
    linarith [mul_nonneg (sub_nonneg.2 hqn') (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f),
      mul_nonneg (by linarith : (0 : ℝ) ≤ n - 1) (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f)]
  have t1 : Real.sqrt n * b ^ 2 ≤ P ^ 2 :=
    calc Real.sqrt n * b ^ 2 ≤ n * b ^ 2 := by gcongr
      _ = (n * b) * b := by ring
      _ ≤ P * P := mul_le_mul hnbP hbP hb0 hP0
      _ = P ^ 2 := by ring
  have t2 : (n : ℝ) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ hn0 hnP 2
  have t3 : (n : ℝ) ^ 3 * f ≤ P ^ 3 :=
    calc (n : ℝ) ^ 3 * f = n * n * (n * f) := by ring
      _ ≤ P * P * P := by gcongr
      _ = P ^ 3 := by ring
  have hP23 : P ^ 2 ≤ P ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hbe0 : 0 ≤ be := by rw [hbe]; positivity
  have hbeP : be ≤ 30 * P ^ 3 := by rw [hbe]; linarith
  have hP3 : (30 : ℝ) ≤ P ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) hP16 3
    norm_num at h; linarith
  have hbe6 : be ≤ P ^ 6 := by linarith [mul_le_mul_of_nonneg_right hP3 (by positivity : (0 : ℝ) ≤ P ^ 3)]
  have hK : (n : ℝ) ^ 2 * f * g * rd * be / 2 ≤ P ^ 6 := by
    have e : (n : ℝ) ^ 2 * f * g * rd * be / 2 = (n * (n * f * rd * g)) * be / 2 := by ring
    rw [e]
    have h : (n * (n * f * rd * g)) * be ≤ P ^ 2 * (30 * P ^ 3) :=
      mul_le_mul hnmP hbeP hbe0 (by positivity)
    linarith [mul_nonneg (pow_nonneg hP0 5) (by linarith : (0 : ℝ) ≤ P - 15)]
  have hsq : ((2 * τ) ^ ((1 : ℝ) / q)) ^ q = 2 * τ := by
    rw [one_div]; exact Real.rpow_inv_natCast_pow (by positivity) hq0
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (2 * τ) ^ ((1 : ℝ) / q) := ⟨_, rfl⟩
  rw [← hsdef] at hsq hrh
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hτP' : τ * P ^ (11 * q) ≤ 1 := by
    have h1 : P⁻¹ ^ (11 * q) * P ^ (11 * q) = 1 := by
      rw [inv_pow]; exact inv_mul_cancel₀ (by positivity)
    calc τ * P ^ (11 * q) ≤ P⁻¹ ^ (11 * q) * P ^ (11 * q) := by gcongr
      _ = 1 := h1
  have hu : (s * P ^ 11) ^ q ≤ 2 ^ q :=
    calc (s * P ^ 11) ^ q = s ^ q * P ^ (11 * q) := by rw [mul_pow, ← pow_mul]
      _ = 2 * (τ * P ^ (11 * q)) := by rw [hsq]; ring
      _ ≤ 2 * 1 := by gcongr
      _ = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
  have hsP : s * P ^ 11 ≤ 2 := (pow_le_pow_iff_left₀ (by positivity) (by norm_num) hq0).1 hu
  have hrh0 : 0 ≤ rh := by rw [hrh]; positivity
  constructor
  · have hP211 : P ^ 2 ≤ P ^ 11 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hA1 : (n : ℝ) ^ 2 * Real.sqrt f * g * rd ≤ P ^ 2 :=
      calc (n : ℝ) ^ 2 * Real.sqrt f * g * rd ≤ (n : ℝ) ^ 2 * f * g * rd := by gcongr
        _ = n * (n * f * rd * g) := by ring
        _ ≤ P ^ 2 := hnmP
    have h : (n : ℝ) ^ 2 * Real.sqrt f * g * rd * s ≤ P ^ 11 * s :=
      calc (n : ℝ) ^ 2 * Real.sqrt f * g * rd * s ≤ P ^ 2 * s := mul_le_mul_of_nonneg_right hA1 hs0
        _ ≤ P ^ 11 * s := mul_le_mul_of_nonneg_right hP211 hs0
    have hl := Real.log_two_gt_d9
    rw [hrh]
    linarith
  · have hAeq : 2 * rh * Real.sqrt f * be = ((n : ℝ) ^ 2 * f * g * rd * be / 2) * s := by
      rw [hrh]; linear_combination ((n : ℝ) ^ 2 * g * rd * s * be / 2) * hfs
    have hA16 : (2 * rh * Real.sqrt f * be) ^ (16 * q) ≤ P ^ (96 * q) * (2 * τ) ^ 16 := by
      rw [hAeq]
      calc (((n : ℝ) ^ 2 * f * g * rd * be / 2) * s) ^ (16 * q) ≤ (P ^ 6 * s) ^ (16 * q) :=
            pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hK hs0) _
        _ = P ^ (96 * q) * (2 * τ) ^ 16 := by
          rw [mul_pow, ← pow_mul, show 6 * (16 * q) = 96 * q by ring,
            show 16 * q = q * 16 by ring, pow_mul s q 16, hsq]
    have hW := deep_exponent_core P τ be n g q hP16 hq hτ hτP hbe0 hbe6 hn0 hnP hg0 hgP
    have hsq17 : (17 * Real.sqrt n / τ ^ 2) ^ 2 = 289 * (n : ℝ) / τ ^ 4 := by
      rw [div_pow, mul_pow, hs2, ← pow_mul]; norm_num
    have hexp : Real.exp f ≤ Real.exp 1 ^ N := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      rw [hNr]
      have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 :=
        le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) (by linarith : (1 : ℝ) ≤ n) 2)
      linarith [mul_le_mul_of_nonneg_right h1 hf0]
    have e1 : (2 * rh * Real.sqrt f * be) ^ (2 * (8 * q * N))
        = ((2 * rh * Real.sqrt f * be) ^ (16 * q)) ^ N := by
      rw [← pow_mul]; congr 1; ring
    have e2 : (17 * Real.sqrt n / τ ^ 2) ^ (2 * N) = (289 * (n : ℝ) / τ ^ 4) ^ N := by
      rw [pow_mul, hsq17]
    have e3 : g ^ (2 * N) = (g ^ 2) ^ N := pow_mul g 2 N
    rw [e1, e2, e3]
    calc ((2 * rh * Real.sqrt f * be) ^ (16 * q)) ^ N
          * ((6 * be) ^ N * Real.exp f * (289 * (n : ℝ) / τ ^ 4) ^ N) * (g ^ 2) ^ N * P ^ N
        ≤ (P ^ (96 * q) * (2 * τ) ^ 16) ^ N
          * ((6 * be) ^ N * Real.exp 1 ^ N * (289 * (n : ℝ) / τ ^ 4) ^ N) * (g ^ 2) ^ N * P ^ N := by
          gcongr
      _ = ((P ^ (96 * q) * (2 * τ) ^ 16) * ((6 * be) * Real.exp 1 * (289 * (n : ℝ) / τ ^ 4))
            * g ^ 2 * P) ^ N := by
          simp only [mul_pow]
      _ ≤ Real.exp (-1) ^ N := pow_le_pow_left₀ (by positivity) hW N
      _ = Real.exp (-(N : ℝ)) := by
          rw [← Real.exp_nat_mul]; congr 1; ring

end GlobalTheory
