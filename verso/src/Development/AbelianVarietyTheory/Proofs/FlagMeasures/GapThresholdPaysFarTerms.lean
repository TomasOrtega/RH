import Mathlib

open Matrix Finset Real

namespace GlobalTheory

/- English proof (translation)
Establish `hs : 0 < Real.sqrt x` using `Real.sqrt_pos.2 (by linarith)`. Establish `hx2 : Real.sqrt x ^ 2 = x` using `Real.sq_sqrt (by linarith)`. Establish `h1 : Real.log (Real.sqrt x / 2) ≤ Real.sqrt x / 2 - 1` using `Real.log_le_sub_one_of_pos (by positivity)`. Establish `h2 : Real.log (Real.sqrt x / 2) = Real.log (Real.sqrt x) - Real.log 2` using `Real.log_div hs.ne' (by norm_num)`. Establish `h3 : Real.log x = 2 * Real.log (Real.sqrt x)` using `by conv_lhs => rw [← hx2]`.

Rewrite using `[Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h4` using `Real.log_two_lt_d9`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem log_le_sqrt_of_one_le (x : ℝ) (hx : 1 ≤ x) :
    Real.log x ≤ Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have h1 : Real.log (Real.sqrt x / 2) ≤ Real.sqrt x / 2 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log (Real.sqrt x / 2) = Real.log (Real.sqrt x) - Real.log 2 :=
    Real.log_div hs.ne' (by norm_num)
  have h3 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    conv_lhs => rw [← hx2]
    rw [Real.log_pow]
    push_cast
    ring
  have h4 := Real.log_two_lt_d9
  linarith

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `Cg n f q rd g b h t hCg hn hf hq hqn hrd hlogf hb hg1 hgb hh ht1 _ht2 ep`. Establish `hep : ep = 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)` using `rfl`. Use `clear_value ep`. Establish `hnR : (3 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hfR : (1 : ℝ) ≤ f` using `by exact_mod_cast hf`.

Establish `hqnR : (q : ℝ) ^ 2 ≤ n` using `by exact_mod_cast hqn`. Establish `hn0 : (n : ℝ) ≠ 0` using `by positivity`. Establish `hf0 : (f : ℝ) ≠ 0` using `by positivity`. Establish `hnpos : (0 : ℝ) < n` using `by linarith`. Establish `hfpos : (0 : ℝ) < f` using `by linarith`.

Use `set s := Real.sqrt (n : ℝ) with hs_def`. Establish `hs2 : s ^ 2 = n` using `Real.sq_sqrt (by linarith)`. Establish `hs1 : 1 ≤ s` using `Real.one_le_sqrt.2 (by linarith)`. Establish `hsn : s ≤ n` using `by nlinarith`. Establish `hqs : (q : ℝ) ≤ s` using `(Real.le_sqrt (by positivity) (by linarith)).2 hqnR`.

Use `set ℓ := Real.log (b * rd) with hℓ_def`. Establish `hbrd : 2 ≤ b * rd` using `le_trans hb (le_mul_of_one_le_right (by linarith) hrd)`. Establish `hℓ : 0.69 ≤ ℓ`. Establish `e1` using `Real.log_le_log (by norm_num) hbrd`. Establish `e2` using `Real.log_two_gt_d9`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogb : Real.log b ≤ ℓ` using `Real.log_le_log (by linarith) (le_mul_of_one_le_right (by linarith) hrd)`. Establish `hlogb0 : 0 ≤ Real.log b` using `Real.log_nonneg (by linarith)`. Establish `hKl : 2.76 ≤ (Cg + 4) * ℓ` using `by nlinarith [mul_nonneg hCg (by linarith : (0 : ℝ) ≤ ℓ)]`. Establish `hX : 50 * (Cg + 4) * (n : ℝ) ^ 3 * f * ℓ ≤ h * ep ^ 2 / 16`.

Establish `e : 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * ℓ * ep ^ 2 / 16 = 50 * (Cg + 4) * (n : ℝ) ^ 3 * f * ℓ`. Rewrite using `[hep]`. Clear the denominators using the available nonvanishing facts. Evaluate the numerical expressions. Rewrite using `[← e]`.

Use `mul_le_mul_of_nonneg_right hh (sq_nonneg ep)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn3f : 1 ≤ (n : ℝ) ^ 3 * f`. Conclude with `one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) hfR`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `e : 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * ℓ * ep = 800000000 * ((Cg + 4) * ℓ) * ((n : ℝ) ^ 11 * f ^ 3)`. Rewrite using `[hep]`. Clear the denominators using the available nonvanishing facts. Evaluate the numerical expressions. Establish `hep0 : 0 ≤ ep` using `by rw [hep]; positivity`.

Establish `h1` using `mul_le_mul_of_nonneg_right hh hep0`. Establish `hn11 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 11` using `pow_le_pow_right₀ (by linarith) (by norm_num)`. Establish `hf3 : (1 : ℝ) ≤ (f : ℝ) ^ 3` using `one_le_pow₀ hfR`. Establish `hP : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 11 * f ^ 3` using `le_trans hn11 (le_mul_of_one_le_right (by positivity) hf3)`. Establish `h2 : 2.76 * (n : ℝ) ^ 2 ≤ ((Cg + 4) * ℓ) * ((n : ℝ) ^ 11 * f ^ 3)` using `mul_le_mul hKl hP (by positivity) (by linarith)`.

Establish `hz : (0 : ℝ) ≤ (n : ℝ) ^ 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : 2.76 * 1 ≤ ((Cg + 4) * ℓ) * ((n : ℝ) ^ 3 * f)` using `mul_le_mul hKl hn3f (by norm_num) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set X := h * ep ^ 2 / 16 with hX_def set M := (n : ℝ) * f * rd * g * b with hM_def`.

Establish `hgpos : 0 < g` using `by linarith`. Establish `hMpos : 0 < M`. Establish `: (0 : ℝ) < rd` using `by linarith`. Establish `: (0 : ℝ) < b` using `by linarith`. Check the signs of the components of the expression.

Use `set Lb := s + s + Cg * ℓ + ℓ with hLb_def`. Establish `hLb0 : 0 ≤ Lb`. Establish `: 0 ≤ Cg * ℓ` using `mul_nonneg hCg (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnexp : (n : ℝ) ≤ Real.exp s`.

Combine the equalities or inequalities in the displayed calculation. Establish `hfexp : (f : ℝ) ≤ Real.exp s`. Combine the equalities or inequalities in the displayed calculation. Establish `hgexp : g ≤ Real.exp (Cg * ℓ)`. Combine the equalities or inequalities in the displayed calculation.

Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Use `mul_le_mul_of_nonneg_right hlogb hCg` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbrdexp : b * rd = Real.exp ℓ` using `(Real.exp_log (by linarith)).symm`. Establish `hMle : M ≤ Real.exp Lb`.

Establish `e1 : M = (n : ℝ) * f * g * (b * rd)` using `by rw [hM_def]; ring`. Establish `e2 : Real.exp Lb = Real.exp s * Real.exp s * Real.exp (Cg * ℓ) * Real.exp ℓ`. Rewrite using `[hLb_def, Real.exp_add, Real.exp_add, Real.exp_add]`. Rewrite using `[e1, e2, hbrdexp]`. Establish `a1 : (n : ℝ) * f ≤ Real.exp s * Real.exp s` using `mul_le_mul hnexp hfexp (by positivity) (by positivity)`.

Establish `a2 : (n : ℝ) * f * g ≤ Real.exp s * Real.exp s * Real.exp (Cg * ℓ)` using `mul_le_mul a1 hgexp (by linarith) (by positivity)`. Conclude with `mul_le_mul_of_nonneg_right a2 (by positivity)`. Establish `htpos : 0 < t` using `lt_of_lt_of_le (pow_pos (inv_pos.2 hMpos) _) ht1`. Establish `hinvt : t⁻¹ ≤ Real.exp (11 * s * Lb)`. Rewrite `ht1` using `[inv_pow]`.

Establish `a1 : t⁻¹ ≤ M ^ (11 * q)` using `inv_le_of_inv_le₀ (pow_pos hMpos _) ht1`. Establish `a2 : M ^ (11 * q) ≤ Real.exp Lb ^ (11 * q)` using `pow_le_pow_left₀ hMpos.le hMle _`. Establish `a3 : Real.exp Lb ^ (11 * q) = Real.exp (((11 * q : ℕ) : ℝ) * Lb)` using `(Real.exp_nat_mul Lb (11 * q)).symm`. Establish `a4 : ((11 * q : ℕ) : ℝ) * Lb ≤ 11 * s * Lb`. Use `push_cast`.

Establish `: 11 * (q : ℝ) ≤ 11 * s` using `by linarith`. Conclude with `mul_le_mul_of_nonneg_right this hLb0`. Combine the equalities or inequalities in the displayed calculation. Establish `hA : 3 * s / t ^ 2 ≤ Real.exp (2 + s + 22 * s * Lb)`. Establish `e1 : 3 * s / t ^ 2 = 3 * s * (t⁻¹) ^ 2` using `by rw [div_eq_mul_inv, inv_pow]`.

Establish `e2 : Real.exp (2 + s + 22 * s * Lb) = Real.exp 2 * Real.exp s * (Real.exp (11 * s * Lb)) ^ 2`. Rewrite using `[sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2]`.

Establish `b1 : (3 : ℝ) ≤ Real.exp 2`. Use `Real.add_one_le_exp 2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `b2 : s ≤ Real.exp s`. Use `Real.add_one_le_exp s` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `b3 : (t⁻¹) ^ 2 ≤ (Real.exp (11 * s * Lb)) ^ 2` using `pow_le_pow_left₀ (by positivity) hinvt 2`. Establish `b4 : 3 * s ≤ Real.exp 2 * Real.exp s` using `mul_le_mul b1 b2 (by linarith) (by positivity)`. Conclude with `mul_le_mul b4 b3 (by positivity) (by positivity)`. Establish `hpow : (3 * s / t ^ 2) ^ (2 * (n ^ 2 * f)) ≤ Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb))`.

Rewrite using `[Real.exp_nat_mul]`. Conclude with `pow_le_pow_left₀ (by positivity) hA _`. Establish `hsmall : 2 * (f : ℝ) * 3 ^ f ≤ Real.exp (4 * f)`. Establish `c1 : 2 * (f : ℝ) ≤ Real.exp (2 * f)`. Use `Real.add_one_le_exp (2 * (f : ℝ))` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `c2 : (3 : ℝ) ^ f ≤ Real.exp (f * 2)`. Rewrite using `[Real.exp_nat_mul]`. Establish `: (3 : ℝ) ≤ Real.exp 2`. Use `Real.add_one_le_exp 2` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `pow_le_pow_left₀ (by norm_num) this f`. Establish `e : Real.exp (4 * f) = Real.exp (2 * f) * Real.exp (f * 2)`. Rewrite using `[← Real.exp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_le_mul c1 c2 (by positivity) (by positivity)`. Establish `hexp : ((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb) + (4 * f + -X) ≤ -((n : ℝ) ^ 2 * f)`. Use `push_cast`.

Establish `hP0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f` using `by positivity`. Establish `hKl0 : 0 ≤ (Cg + 1) * ℓ` using `mul_nonneg (by linarith) (by linarith)`. Establish `k1 : (n : ℝ) ^ 2 * f * s * ((Cg + 1) * ℓ) ≤ (n : ℝ) ^ 2 * f * n * ((Cg + 1) * ℓ)` using `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsn hP0) hKl0`. Establish `k2 : (n : ℝ) ^ 2 * f * s ≤ (n : ℝ) ^ 2 * f * n` using `mul_le_mul_of_nonneg_left hsn hP0`. Establish `k3 : (f : ℝ) ≤ (n : ℝ) ^ 2 * f` using `le_mul_of_one_le_left hfpos.le (one_le_pow₀ (by linarith))`.

Establish `k4 : (n : ℝ) ^ 2 * f * 3 ≤ (n : ℝ) ^ 2 * f * n` using `mul_le_mul_of_nonneg_left hnR hP0`. Establish `k5 : (n : ℝ) ^ 2 * f * n * 107 ≤ (n : ℝ) ^ 2 * f * n * (156 * ℓ)` using `mul_le_mul_of_nonneg_left (by linarith) (by positivity)`. Establish `k6 : 0 ≤ (n : ℝ) ^ 2 * f * n * (Cg * ℓ)` using `mul_nonneg (by positivity) (mul_nonneg hCg (by linarith))`. Establish `k7 : (n : ℝ) ^ 2 * f * s ^ 2 = (n : ℝ) ^ 2 * f * n` using `by rw [hs2]`. Establish `k8 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f * n` using `by positivity`.

Rewrite using `[hLb_def]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul hpow (mul_le_mul_of_nonneg_right hsmall (by positivity)) (by positivity) (by positivity)` to reduce the goal to its premises. Use `_ = Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb) + (4 * f + -X)) := by`.

Rewrite using `[Real.exp_add, Real.exp_add]`. Use `_ ≤ Real.exp (-((n : ℝ) ^ 2 * f)) := Real.exp_le_exp.2 hexp`.
-/
theorem gap_threshold_pays_far_terms : ∀ (Cg : ℝ) (n f q : ℕ) (rd g b : ℝ) (h t : ℝ), 0 ≤ Cg → 3 ≤ n → 1 ≤ f → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ rd → Real.log f ≤ Real.sqrt n → 2 ≤ b → 1 ≤ g → g ≤ b ^ Cg → 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * Real.log (b * rd) ≤ h → ((n : ℝ) * f * rd * g * b)⁻¹ ^ (11 * q) ≤ t → t ≤ 1 / 2 → let ep : ℝ := 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2); 64 * (n : ℝ) ^ 2 ≤ h * ep ∧ 1 ≤ h * ep ^ 2 / 16 ∧ (3 * Real.sqrt n / t ^ 2) ^ (2 * (n ^ 2 * f)) * (2 * f * 3 ^ f * Real.exp (-(h * ep ^ 2 / 16))) ≤ Real.exp (-((n : ℝ) ^ 2 * f)) := by
  intro Cg n f q rd g b h t hCg hn hf hq hqn hrd hlogf hb hg1 hgb hh ht1 _ht2 ep
  have hep : ep = 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) := rfl
  clear_value ep
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hqnR : (q : ℝ) ^ 2 ≤ n := by exact_mod_cast hqn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hf0 : (f : ℝ) ≠ 0 := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hfpos : (0 : ℝ) < f := by linarith
  set s := Real.sqrt (n : ℝ) with hs_def
  have hs2 : s ^ 2 = n := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by linarith)
  have hsn : s ≤ n := by nlinarith
  have hqs : (q : ℝ) ≤ s := (Real.le_sqrt (by positivity) (by linarith)).2 hqnR
  set ℓ := Real.log (b * rd) with hℓ_def
  have hbrd : 2 ≤ b * rd := le_trans hb (le_mul_of_one_le_right (by linarith) hrd)
  have hℓ : 0.69 ≤ ℓ := by
    have e1 := Real.log_le_log (by norm_num) hbrd
    have e2 := Real.log_two_gt_d9
    linarith
  have hlogb : Real.log b ≤ ℓ := Real.log_le_log (by linarith) (le_mul_of_one_le_right (by linarith) hrd)
  have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hKl : 2.76 ≤ (Cg + 4) * ℓ := by nlinarith [mul_nonneg hCg (by linarith : (0 : ℝ) ≤ ℓ)]

  have hX : 50 * (Cg + 4) * (n : ℝ) ^ 3 * f * ℓ ≤ h * ep ^ 2 / 16 := by
    have e : 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * ℓ * ep ^ 2 / 16
        = 50 * (Cg + 4) * (n : ℝ) ^ 3 * f * ℓ := by
      rw [hep]
      field_simp
      norm_num
    rw [← e]
    have := mul_le_mul_of_nonneg_right hh (sq_nonneg ep)
    linarith
  have hn3f : 1 ≤ (n : ℝ) ^ 3 * f := by
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) hfR
  refine ⟨?_, ?_, ?_⟩
  · have e : 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * ℓ * ep
        = 800000000 * ((Cg + 4) * ℓ) * ((n : ℝ) ^ 11 * f ^ 3) := by
      rw [hep]
      field_simp
      norm_num
    have hep0 : 0 ≤ ep := by rw [hep]; positivity
    have h1 := mul_le_mul_of_nonneg_right hh hep0
    have hn11 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 11 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hf3 : (1 : ℝ) ≤ (f : ℝ) ^ 3 := one_le_pow₀ hfR
    have hP : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 11 * f ^ 3 :=
      le_trans hn11 (le_mul_of_one_le_right (by positivity) hf3)
    have h2 : 2.76 * (n : ℝ) ^ 2 ≤ ((Cg + 4) * ℓ) * ((n : ℝ) ^ 11 * f ^ 3) :=
      mul_le_mul hKl hP (by positivity) (by linarith)
    have hz : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    linarith
  · have h2 : 2.76 * 1 ≤ ((Cg + 4) * ℓ) * ((n : ℝ) ^ 3 * f) :=
      mul_le_mul hKl hn3f (by norm_num) (by linarith)
    linarith
  · set X := h * ep ^ 2 / 16 with hX_def
    set M := (n : ℝ) * f * rd * g * b with hM_def
    have hgpos : 0 < g := by linarith
    have hMpos : 0 < M := by
      have : (0 : ℝ) < rd := by linarith
      have : (0 : ℝ) < b := by linarith
      positivity
    set Lb := s + s + Cg * ℓ + ℓ with hLb_def
    have hLb0 : 0 ≤ Lb := by
      have : 0 ≤ Cg * ℓ := mul_nonneg hCg (by linarith)
      linarith

    have hnexp : (n : ℝ) ≤ Real.exp s := by
      calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
        _ ≤ Real.exp s := Real.exp_le_exp.2 (log_le_sqrt_of_one_le _ (by linarith))
    have hfexp : (f : ℝ) ≤ Real.exp s := by
      calc (f : ℝ) = Real.exp (Real.log f) := (Real.exp_log hfpos).symm
        _ ≤ Real.exp s := Real.exp_le_exp.2 hlogf
    have hgexp : g ≤ Real.exp (Cg * ℓ) := by
      calc g ≤ b ^ Cg := hgb
        _ = Real.exp (Real.log b * Cg) := Real.rpow_def_of_pos (by linarith) Cg
        _ ≤ Real.exp (Cg * ℓ) := by
          apply Real.exp_le_exp.2
          have := mul_le_mul_of_nonneg_right hlogb hCg
          linarith
    have hbrdexp : b * rd = Real.exp ℓ := (Real.exp_log (by linarith)).symm
    have hMle : M ≤ Real.exp Lb := by
      have e1 : M = (n : ℝ) * f * g * (b * rd) := by rw [hM_def]; ring
      have e2 : Real.exp Lb = Real.exp s * Real.exp s * Real.exp (Cg * ℓ) * Real.exp ℓ := by
        rw [hLb_def, Real.exp_add, Real.exp_add, Real.exp_add]
      rw [e1, e2, hbrdexp]
      have a1 : (n : ℝ) * f ≤ Real.exp s * Real.exp s :=
        mul_le_mul hnexp hfexp (by positivity) (by positivity)
      have a2 : (n : ℝ) * f * g ≤ Real.exp s * Real.exp s * Real.exp (Cg * ℓ) :=
        mul_le_mul a1 hgexp (by linarith) (by positivity)
      exact mul_le_mul_of_nonneg_right a2 (by positivity)

    have htpos : 0 < t := lt_of_lt_of_le (pow_pos (inv_pos.2 hMpos) _) ht1
    have hinvt : t⁻¹ ≤ Real.exp (11 * s * Lb) := by
      rw [inv_pow] at ht1
      have a1 : t⁻¹ ≤ M ^ (11 * q) := inv_le_of_inv_le₀ (pow_pos hMpos _) ht1
      have a2 : M ^ (11 * q) ≤ Real.exp Lb ^ (11 * q) := pow_le_pow_left₀ hMpos.le hMle _
      have a3 : Real.exp Lb ^ (11 * q) = Real.exp (((11 * q : ℕ) : ℝ) * Lb) :=
        (Real.exp_nat_mul Lb (11 * q)).symm
      have a4 : ((11 * q : ℕ) : ℝ) * Lb ≤ 11 * s * Lb := by
        push_cast
        have : 11 * (q : ℝ) ≤ 11 * s := by linarith
        exact mul_le_mul_of_nonneg_right this hLb0
      calc t⁻¹ ≤ M ^ (11 * q) := a1
        _ ≤ Real.exp Lb ^ (11 * q) := a2
        _ = Real.exp (((11 * q : ℕ) : ℝ) * Lb) := a3
        _ ≤ Real.exp (11 * s * Lb) := Real.exp_le_exp.2 a4

    have hA : 3 * s / t ^ 2 ≤ Real.exp (2 + s + 22 * s * Lb) := by
      have e1 : 3 * s / t ^ 2 = 3 * s * (t⁻¹) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
      have e2 : Real.exp (2 + s + 22 * s * Lb)
          = Real.exp 2 * Real.exp s * (Real.exp (11 * s * Lb)) ^ 2 := by
        rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [e1, e2]
      have b1 : (3 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp 2
        linarith
      have b2 : s ≤ Real.exp s := by
        have := Real.add_one_le_exp s
        linarith
      have b3 : (t⁻¹) ^ 2 ≤ (Real.exp (11 * s * Lb)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hinvt 2
      have b4 : 3 * s ≤ Real.exp 2 * Real.exp s :=
        mul_le_mul b1 b2 (by linarith) (by positivity)
      exact mul_le_mul b4 b3 (by positivity) (by positivity)
    have hpow : (3 * s / t ^ 2) ^ (2 * (n ^ 2 * f))
        ≤ Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb)) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by positivity) hA _

    have hsmall : 2 * (f : ℝ) * 3 ^ f ≤ Real.exp (4 * f) := by
      have c1 : 2 * (f : ℝ) ≤ Real.exp (2 * f) := by
        have := Real.add_one_le_exp (2 * (f : ℝ))
        linarith
      have c2 : (3 : ℝ) ^ f ≤ Real.exp (f * 2) := by
        rw [Real.exp_nat_mul]
        have : (3 : ℝ) ≤ Real.exp 2 := by
          have := Real.add_one_le_exp 2
          linarith
        exact pow_le_pow_left₀ (by norm_num) this f
      have e : Real.exp (4 * f) = Real.exp (2 * f) * Real.exp (f * 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [e]
      exact mul_le_mul c1 c2 (by positivity) (by positivity)

    have hexp : ((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb) + (4 * f + -X)
        ≤ -((n : ℝ) ^ 2 * f) := by
      push_cast
      have hP0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f := by positivity
      have hKl0 : 0 ≤ (Cg + 1) * ℓ := mul_nonneg (by linarith) (by linarith)
      have k1 : (n : ℝ) ^ 2 * f * s * ((Cg + 1) * ℓ) ≤ (n : ℝ) ^ 2 * f * n * ((Cg + 1) * ℓ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsn hP0) hKl0
      have k2 : (n : ℝ) ^ 2 * f * s ≤ (n : ℝ) ^ 2 * f * n := mul_le_mul_of_nonneg_left hsn hP0
      have k3 : (f : ℝ) ≤ (n : ℝ) ^ 2 * f :=
        le_mul_of_one_le_left hfpos.le (one_le_pow₀ (by linarith))
      have k4 : (n : ℝ) ^ 2 * f * 3 ≤ (n : ℝ) ^ 2 * f * n := mul_le_mul_of_nonneg_left hnR hP0
      have k5 : (n : ℝ) ^ 2 * f * n * 107 ≤ (n : ℝ) ^ 2 * f * n * (156 * ℓ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have k6 : 0 ≤ (n : ℝ) ^ 2 * f * n * (Cg * ℓ) :=
        mul_nonneg (by positivity) (mul_nonneg hCg (by linarith))
      have k7 : (n : ℝ) ^ 2 * f * s ^ 2 = (n : ℝ) ^ 2 * f * n := by rw [hs2]
      have k8 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f * n := by positivity
      rw [hLb_def]
      linarith
    calc (3 * s / t ^ 2) ^ (2 * (n ^ 2 * f)) * (2 * f * 3 ^ f * Real.exp (-X))
        ≤ Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb))
            * (Real.exp (4 * f) * Real.exp (-X)) := by
          apply mul_le_mul hpow (mul_le_mul_of_nonneg_right hsmall (by positivity))
            (by positivity) (by positivity)
      _ = Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb) + (4 * f + -X)) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (-((n : ℝ) ^ 2 * f)) := Real.exp_le_exp.2 hexp

end GlobalTheory
