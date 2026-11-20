import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

/- English proof (translation)
Introduce `eps K C heps`. Use `set N : ℝ := Real.log 2 + |C| + |K| + 1 with hN`. Use `set D : ℝ := 9 + 2 * |C| with hD`. Use `set T : ℝ := 2 * (D + Real.log N + 1) with hTdef`. Establish `hl2 : 0 < Real.log 2` using `Real.log_pos (by norm_num)`.

Establish `hN1 : 1 ≤ N`. Use `abs_nonneg C` as an intermediate fact. Use `abs_nonneg K` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogN : 0 ≤ Real.log N` using `Real.log_nonneg hN1`.

Establish `hD0 : 9 ≤ D`. Use `abs_nonneg C` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT : 0 ≤ T` using `by linarith`. Use `⟨max 1 (T ^ (5 / eps)), fun x hx u hu hlog => ?_⟩` and prove the remaining obligations.

Establish `hx1 : 1 ≤ x` using `le_trans (le_max_left _ _) hx`. Establish `hxpos : 0 < x` using `by linarith`. Use `set a := x ^ (eps / 4) with ha`. Use `set b := x ^ (4 * eps / 5) with hb`. Use `set s := x ^ (eps / 5) with hs`.

Establish `hab : a ≤ b` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `hb1 : 1 ≤ b` using `Real.one_le_rpow hx1 (by positivity)`. Establish `ha0 : 0 ≤ a` using `by positivity`. Establish `hc : x ^ eps = b * s`. Rewrite using `[hb, hs, ← Real.rpow_add hxpos]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hsT : T ≤ s`. Establish `h1 : T = (T ^ (5 / eps)) ^ (eps / 5)`. Rewrite using `[← Real.rpow_mul hT]`.

Establish `: 5 / eps * (eps / 5) = 1` using `by field_simp`. Rewrite using `[this, Real.rpow_one]`. Rewrite using `[h1, hs]`. Conclude with `Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hx) (by positivity)`. Establish `hlogu : 0 ≤ Real.log u` using `Real.log_nonneg hu`.

Establish `hupos : 0 < u` using `by linarith`. Establish `huC : u ^ C ≤ Real.exp (D * b)`. Rewrite using `[Real.rpow_def_of_pos hupos]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `e1 : Real.log u * C ≤ Real.log u * |C|` using `mul_le_mul_of_nonneg_left (le_abs_self C) hlogu`.

Establish `e2 : Real.log u * |C| ≤ (2 * a) * |C|` using `mul_le_mul_of_nonneg_right hlog (abs_nonneg C)`. Establish `e3 : (2 * a) * |C| ≤ (2 * b) * |C|` using `mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg C)`. Establish `e4 : (2 * b) * |C| ≤ D * b`. Rewrite using `[hD]`. Use polynomial arithmetic with `[abs_nonneg C]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hK : K * Real.exp (8 * a) ≤ |K| * Real.exp (D * b)`. Establish `: K * Real.exp (8 * a) ≤ |K| * Real.exp (8 * a)` using `mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le`. Establish `h2 : Real.exp (8 * a) ≤ Real.exp (D * b)` using `Real.exp_le_exp.mpr (by nlinarith)`. Establish `h3` using `mul_le_mul_of_nonneg_left h2 (abs_nonneg K)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hE : Real.exp b ≤ Real.exp (D * b)` using `Real.exp_le_exp.mpr (by nlinarith)`. Establish `hCE : C * Real.exp b ≤ |C| * Real.exp (D * b)`. Establish `: C * Real.exp b ≤ |C| * Real.exp b` using `mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le`. Establish `h3` using `mul_le_mul_of_nonneg_left hE (abs_nonneg C)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL2 : Real.exp b * Real.log 2 ≤ Real.exp (D * b) * Real.log 2` using `mul_le_mul_of_nonneg_right hE hl2.le`. Establish `hsum : Real.exp b * Real.log 2 + K * Real.exp (8 * a) + (u ^ C + C * Real.exp b) ≤ N * Real.exp (D * b)`. Rewrite using `[hN]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hfin : N * Real.exp (D * b) ≤ Real.exp (x ^ eps / 2)`. Rewrite using `[← Real.exp_log (by linarith : (0:ℝ) < N), ← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Rewrite using `[hc]`. Establish `: b * (D + Real.log N + 1) ≤ b * s / 2`.

Use `mul_le_mul_of_nonneg_left hsT (by linarith : (0:ℝ) ≤ b)` as an intermediate fact. Rewrite `this` using `[hTdef]`. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities. Rewrite `hfin` using `[Real.exp_half]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.error_terms_le_sqrt_exp_rpow :
    ∀ eps K C : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ u : ℝ, 1 ≤ u → Real.log u ≤ 2 * x ^ (eps / 4) →
      Real.exp (x ^ (4 * eps / 5)) * Real.log 2 + K * Real.exp (8 * x ^ (eps / 4)) + (u ^ C + C * Real.exp (x ^ (4 * eps / 5))) ≤
        Real.sqrt (Real.exp (x ^ eps)) := by
  intro eps K C heps
  set N : ℝ := Real.log 2 + |C| + |K| + 1 with hN
  set D : ℝ := 9 + 2 * |C| with hD
  set T : ℝ := 2 * (D + Real.log N + 1) with hTdef
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN1 : 1 ≤ N := by
    have := abs_nonneg C
    have := abs_nonneg K
    linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hD0 : 9 ≤ D := by
    have := abs_nonneg C
    linarith
  have hT : 0 ≤ T := by linarith
  refine ⟨max 1 (T ^ (5 / eps)), fun x hx u hu hlog => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : 0 < x := by linarith
  set a := x ^ (eps / 4) with ha
  set b := x ^ (4 * eps / 5) with hb
  set s := x ^ (eps / 5) with hs
  have hab : a ≤ b := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hb1 : 1 ≤ b := Real.one_le_rpow hx1 (by positivity)
  have ha0 : 0 ≤ a := by positivity
  have hc : x ^ eps = b * s := by
    rw [hb, hs, ← Real.rpow_add hxpos]
    congr 1
    ring
  have hsT : T ≤ s := by
    have h1 : T = (T ^ (5 / eps)) ^ (eps / 5) := by
      rw [← Real.rpow_mul hT]
      have : 5 / eps * (eps / 5) = 1 := by field_simp
      rw [this, Real.rpow_one]
    rw [h1, hs]
    exact Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hx) (by positivity)
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hupos : 0 < u := by linarith
  have huC : u ^ C ≤ Real.exp (D * b) := by
    rw [Real.rpow_def_of_pos hupos]
    apply Real.exp_le_exp.mpr
    have e1 : Real.log u * C ≤ Real.log u * |C| :=
      mul_le_mul_of_nonneg_left (le_abs_self C) hlogu
    have e2 : Real.log u * |C| ≤ (2 * a) * |C| :=
      mul_le_mul_of_nonneg_right hlog (abs_nonneg C)
    have e3 : (2 * a) * |C| ≤ (2 * b) * |C| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg C)
    have e4 : (2 * b) * |C| ≤ D * b := by
      rw [hD]
      nlinarith [abs_nonneg C]
    linarith
  have hK : K * Real.exp (8 * a) ≤ |K| * Real.exp (D * b) := by
    have : K * Real.exp (8 * a) ≤ |K| * Real.exp (8 * a) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le
    have h2 : Real.exp (8 * a) ≤ Real.exp (D * b) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (abs_nonneg K)
    linarith
  have hE : Real.exp b ≤ Real.exp (D * b) := Real.exp_le_exp.mpr (by nlinarith)
  have hCE : C * Real.exp b ≤ |C| * Real.exp (D * b) := by
    have : C * Real.exp b ≤ |C| * Real.exp b :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    have h3 := mul_le_mul_of_nonneg_left hE (abs_nonneg C)
    linarith
  have hL2 : Real.exp b * Real.log 2 ≤ Real.exp (D * b) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hE hl2.le
  have hsum : Real.exp b * Real.log 2 + K * Real.exp (8 * a) + (u ^ C + C * Real.exp b)
      ≤ N * Real.exp (D * b) := by
    rw [hN]
    nlinarith
  have hfin : N * Real.exp (D * b) ≤ Real.exp (x ^ eps / 2) := by
    rw [← Real.exp_log (by linarith : (0:ℝ) < N), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hc]
    have : b * (D + Real.log N + 1) ≤ b * s / 2 := by
      have := mul_le_mul_of_nonneg_left hsT (by linarith : (0:ℝ) ≤ b)
      rw [hTdef] at this
      linarith
    nlinarith
  rw [Real.exp_half] at hfin
  linarith
