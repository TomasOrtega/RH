import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

/- English proof (translation)
Establish `hb : 0 < eps / 7` using `by positivity`. Establish `hab : 0 < eps / 6 - eps / 7` using `by linarith`. Establish `h612 : 0 ≤ Real.log 612` using `Real.log_nonneg (by norm_num)`. Use `set K : ℝ := 1 + Real.log 612 + 3 * |C| / (eps / 7) with hK`. Establish `hK0 : 0 ≤ K` using `by positivity`.

Use `filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), Filter.eventually_ge_atTop (K ^ (1 / (eps / 6 - eps / 7)))] with x hx1 hxK`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hlog : 0 ≤ Real.log x` using `Real.log_nonneg hx1`. Establish `hxb : 1 ≤ x ^ (eps / 7)` using `Real.one_le_rpow hx1 hb.le`. Establish `hl : Real.log x ≤ x ^ (eps / 7) / (eps / 7)` using `Real.log_le_rpow_div hx0.le hb`.

Establish `hd : K ≤ x ^ (eps / 6 - eps / 7)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_mul hK0, one_div_mul_cancel hab.ne', Real.rpow_one]`. Use `_ ≤ x ^ (eps / 6 - eps / 7) := Real.rpow_le_rpow (Real.rpow_nonneg hK0 _) hxK hab.le`. Establish `hsplit : x ^ (eps / 6) = x ^ (eps / 6 - eps / 7) * x ^ (eps / 7)`.

Rewrite using `[← Real.rpow_add hx0]`. Put the polynomial expressions in normal form. Establish `hpow : (x ^ C) ^ 3 = Real.exp (3 * (Real.log x * C))`. Rewrite using `[Real.rpow_def_of_pos hx0, ← Real.exp_nat_mul]`. Evaluate the numerical expressions.

Rewrite using `[hpow, show (612 : ℝ) = Real.exp (Real.log 612) from (Real.exp_log (by norm_num)).symm, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]`. Establish `hC1 : Real.log x * C ≤ Real.log x * |C|` using `mul_le_mul_of_nonneg_left (le_abs_self C) hlog`. Establish `hC2 : Real.log x * |C| ≤ x ^ (eps / 7) / (eps / 7) * |C|` using `mul_le_mul_of_nonneg_right hl (abs_nonneg C)`. Establish `hKx : K * x ^ (eps / 7) ≤ x ^ (eps / 6)`. Rewrite using `[hsplit]; exact mul_le_mul_of_nonneg_right hd (by positivity)`.

Establish `hl612 : Real.log 612 ≤ Real.log 612 * x ^ (eps / 7)` using `le_mul_of_one_le_right h612 hxb`. Establish `h3 : 3 * (Real.log x * C) ≤ 3 * |C| / (eps / 7) * x ^ (eps / 7)`. Combine the equalities or inequalities in the displayed calculation. Establish `h4 : (1 + Real.log 612 + 3 * |C| / (eps / 7)) * x ^ (eps / 7) = x ^ (eps / 7) + Real.log 612 * x ^ (eps / 7) + 3 * |C| / (eps / 7) * x ^ (eps / 7)` using `by ring`. Rewrite `hKx` using `[hK, h4]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem badBound_tail (eps C : ℝ) (he : 0 < eps) :
    ∀ᶠ x : ℝ in Filter.atTop,
      612 * (x ^ C) ^ 3 * Real.exp (-(x ^ (eps / 6))) ≤ Real.exp (-(x ^ (eps / 7))) := by
  have hb : 0 < eps / 7 := by positivity
  have hab : 0 < eps / 6 - eps / 7 := by linarith
  have h612 : 0 ≤ Real.log 612 := Real.log_nonneg (by norm_num)
  set K : ℝ := 1 + Real.log 612 + 3 * |C| / (eps / 7) with hK
  have hK0 : 0 ≤ K := by positivity
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (K ^ (1 / (eps / 6 - eps / 7)))] with x hx1 hxK
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxb : 1 ≤ x ^ (eps / 7) := Real.one_le_rpow hx1 hb.le
  have hl : Real.log x ≤ x ^ (eps / 7) / (eps / 7) := Real.log_le_rpow_div hx0.le hb
  have hd : K ≤ x ^ (eps / 6 - eps / 7) := by
    calc K = (K ^ (1 / (eps / 6 - eps / 7))) ^ (eps / 6 - eps / 7) := by
          rw [← Real.rpow_mul hK0, one_div_mul_cancel hab.ne', Real.rpow_one]
      _ ≤ x ^ (eps / 6 - eps / 7) := Real.rpow_le_rpow (Real.rpow_nonneg hK0 _) hxK hab.le
  have hsplit : x ^ (eps / 6) = x ^ (eps / 6 - eps / 7) * x ^ (eps / 7) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hpow : (x ^ C) ^ 3 = Real.exp (3 * (Real.log x * C)) := by
    rw [Real.rpow_def_of_pos hx0, ← Real.exp_nat_mul]; norm_num
  rw [hpow, show (612 : ℝ) = Real.exp (Real.log 612) from (Real.exp_log (by norm_num)).symm,
    ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hC1 : Real.log x * C ≤ Real.log x * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) hlog
  have hC2 : Real.log x * |C| ≤ x ^ (eps / 7) / (eps / 7) * |C| :=
    mul_le_mul_of_nonneg_right hl (abs_nonneg C)
  have hKx : K * x ^ (eps / 7) ≤ x ^ (eps / 6) := by
    rw [hsplit]; exact mul_le_mul_of_nonneg_right hd (by positivity)
  have hl612 : Real.log 612 ≤ Real.log 612 * x ^ (eps / 7) := le_mul_of_one_le_right h612 hxb
  have h3 : 3 * (Real.log x * C) ≤ 3 * |C| / (eps / 7) * x ^ (eps / 7) := by
    calc 3 * (Real.log x * C) ≤ 3 * (x ^ (eps / 7) / (eps / 7) * |C|) := by linarith
      _ = 3 * |C| / (eps / 7) * x ^ (eps / 7) := by ring
  have h4 : (1 + Real.log 612 + 3 * |C| / (eps / 7)) * x ^ (eps / 7) =
      x ^ (eps / 7) + Real.log 612 * x ^ (eps / 7) + 3 * |C| / (eps / 7) * x ^ (eps / 7) := by ring
  rw [hK, h4] at hKx
  linarith

/- English proof (translation)
Establish `hg0 : 0 < g` using `lt_of_lt_of_le (Real.exp_pos _) hg`. Use `set q := g ^ (1 / 4 : ℝ) with hqdef`. Establish `hq0 : 0 < q` using `Real.rpow_pos_of_pos hg0 _`. Establish `h1 : Real.log g ≤ g ^ (1 / 4 : ℝ) / (1 / 4)` using `Real.log_le_rpow_div hg0.le (by norm_num)`. Establish `hs : Real.sqrt g = q * q`.

Rewrite using `[hqdef, ← Real.rpow_add hg0, Real.sqrt_eq_rpow]`. Evaluate the numerical expressions. Establish `hq : Real.exp u ≤ q`. Establish `: Real.exp u = (Real.exp (4 * u)) ^ (1 / 4 : ℝ)`. Rewrite using `[← Real.exp_mul]`.

Put the polynomial expressions in normal form. Rewrite using `[this]; exact Real.rpow_le_rpow (Real.exp_pos _).le hg (by norm_num)`. Establish `hone : 1 ≤ Real.exp (-u) * q`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hs, div_le_iff₀ (by positivity)]`.

Establish `h1' : Real.log g ≤ 4 * q` using `by rw [← hqdef] at h1; linarith`. Use polynomial arithmetic with `[hq0, hone]`.
-/
theorem log_div_sqrt_le_four_exp {g u : ℝ} (hg : Real.exp (4 * u) ≤ g) :
    Real.log g / Real.sqrt g ≤ 4 * Real.exp (-u) := by
  have hg0 : 0 < g := lt_of_lt_of_le (Real.exp_pos _) hg
  set q := g ^ (1 / 4 : ℝ) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hg0 _
  have h1 : Real.log g ≤ g ^ (1 / 4 : ℝ) / (1 / 4) := Real.log_le_rpow_div hg0.le (by norm_num)
  have hs : Real.sqrt g = q * q := by
    rw [hqdef, ← Real.rpow_add hg0, Real.sqrt_eq_rpow]; norm_num
  have hq : Real.exp u ≤ q := by
    have : Real.exp u = (Real.exp (4 * u)) ^ (1 / 4 : ℝ) := by
      rw [← Real.exp_mul]; ring_nf
    rw [this]; exact Real.rpow_le_rpow (Real.exp_pos _).le hg (by norm_num)
  have hone : 1 ≤ Real.exp (-u) * q := by
    calc (1 : ℝ) = Real.exp (-u) * Real.exp u := by rw [← Real.exp_add]; simp
      _ ≤ Real.exp (-u) * q := mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
  rw [hs, div_le_iff₀ (by positivity)]
  have h1' : Real.log g ≤ 4 * q := by rw [← hqdef] at h1; linarith
  nlinarith [hq0, hone]

/- English proof (translation)
Introduce `eps C he he1`. Take `⟨X1, hX1⟩` from `Filter.eventually_atTop.1 (badBound_tail eps C he)`. Use `⟨max (max X1 8) (max (20 * |C| + 1) ((100000 : ℝ) ^ (1 / eps))), ?_⟩` and prove the remaining obligations. Introduce `x hx g f m N q hg hf1 hf2 hm1 hm2 hN1 hN2 hq`. Establish `hxX1 : X1 ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`.

Establish `hx8 : 8 ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `hxC : 20 * |C| + 1 ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`. Establish `hxN : (100000 : ℝ) ^ (1 / eps) ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hx1 : 1 ≤ x` using `by linarith`.

Establish `hx1' : 1 < x` using `by linarith`. Establish `hNbig : 100000 ≤ N`. Establish `e : (100000 : ℝ) = ((100000 : ℝ) ^ (1 / eps)) ^ eps`. Rewrite using `[← Real.rpow_mul (by norm_num), one_div_mul_cancel he.ne', Real.rpow_one]`. Establish `h2 : ((100000 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps` using `Real.rpow_le_rpow (by positivity) hxN he.le`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hTail` using `hX1 x hxX1`. Establish `hCe : eps ≤ C` using `(Real.rpow_le_rpow_left_iff hx1').1 (le_trans hN1 hN2)`. Establish `hC0 : 0 ≤ C` using `by linarith`. Use `set P := x ^ C with hP`.

Use `set E := Real.exp (-(x ^ (eps / 6))) with hE`. Establish `hE0 : 0 < E` using `Real.exp_pos _`. Establish `hN0 : 0 < N` using `by linarith`. Establish `hP1 : 1 ≤ P` using `Real.one_le_rpow hx1 hC0`. Establish `hx2 : x ^ (2 : ℝ) = x * x` using `by rw [Real.rpow_two, sq]`.

Rewrite `hf1` using `[hx2]`. Establish `hf0 : 0 ≤ f` using `le_trans (by positivity) hf1`. Establish `he6 : x ^ (eps / 6) ≤ x ^ eps` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `he6h : x ^ (eps / 6) ≤ x ^ (1 / 2 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `hsq : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x` using `by rw [← Real.rpow_add hx0]; norm_num`.

Establish `hs0 : 0 ≤ x ^ (1 / 2 : ℝ)` using `by positivity`. Establish `hsx : x ^ (1 / 2 : ℝ) ≤ x`. Establish `h` using `Real.rpow_le_rpow_of_exponent_le hx1 (show (1 / 2 : ℝ) ≤ 1 by norm_num)`. Rewrite `h` using `[Real.rpow_one]`. Then use the resulting hypothesis. Establish `hxe1 : 1 ≤ x ^ eps` using `Real.one_le_rpow hx1 he.le`.

Establish `hg8 : Real.exp 8 ≤ g` using `le_trans (Real.exp_le_exp.2 (by linarith)) hg`. Establish `hg2 : 2 ≤ g` using `by have := Real.add_one_le_exp 8; linarith`. Establish `hg0 : 0 < g` using `by linarith`. Establish `hEg : 1 ≤ E * g`. Combine the equalities or inequalities in the displayed calculation.

Establish `hginv : 1 / g ≤ E` using `by rw [div_le_iff₀ hg0]; linarith`. Establish `hT2 : Real.log g / Real.sqrt g ≤ 4 * E`. Establish `h` using `log_div_sqrt_le_four_exp (u := 2 * x ^ eps) (g := g) (by rw [show 4 * (2 * x ^ eps) = 8 * x ^ eps by ring]; exact hg)`. Use `h.trans ?_` and prove the remaining obligations. Rewrite using `[hE]`.

Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLg : 0 ≤ Real.log g / Real.sqrt g` using `div_nonneg (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _)`. Establish `hq0 : 0 < q` using `lt_of_lt_of_le (Real.exp_pos _) hq`. Establish `hEq : 1 ≤ E * q`.

Combine the equalities or inequalities in the displayed calculation. Establish `hqinv : 1 / (4 * q) ≤ E / 4`. Rewrite using `[div_le_div_iff₀ (by positivity) (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogN : 1 + Real.log N ≤ N` using `by linarith [Real.log_le_sub_one_of_pos hN0]`.

Establish `hlogN0 : 0 ≤ Real.log N` using `Real.log_nonneg (by linarith)`. Establish `hT3b : (1 + Real.log N) / (g - 1) ≤ 2 * N * E`. Rewrite using `[div_le_iff₀ (by linarith)]`. Establish `h1` using `mul_nonneg (mul_nonneg hN0.le hE0.le) (show 0 ≤ g - 2 by linarith)`. Establish `h2 : N * 1 ≤ N * (E * g)` using `mul_le_mul_of_nonneg_left hEg hN0.le`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT4 : (7 / 8 : ℝ) ^ f ≤ E`. Rewrite using `[Real.rpow_def_of_pos (by norm_num), hE, Real.exp_le_exp]`. Establish `hl78 : Real.log (7 / 8) ≤ -(1 / 8)`. Use `Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 8 by norm_num); linarith` as an intermediate fact.

Establish `h1 : Real.log (7 / 8) * f ≤ -(1 / 8) * f` using `mul_le_mul_of_nonneg_right hl78 hf0`. Establish `h2 : 8 * x ≤ x * x` using `mul_le_mul_of_nonneg_right hx8 hx0.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT5 : Real.exp (-(f / (10 * Real.log N))) ≤ E`. Establish `hlN0 : 0 < Real.log N` using `Real.log_pos (by linarith)`.

Rewrite using `[hE, Real.exp_le_exp, neg_le_neg_iff, le_div_iff₀ (by linarith)]`. Establish `hlN : Real.log N ≤ C * Real.log x`. Rewrite using `[← Real.log_rpow hx0]`. Conclude with `Real.log_le_log hN0 hN2`. Establish `hlx : Real.log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2)` using `Real.log_le_rpow_div hx0.le (by norm_num)`.

Establish `h1 : x ^ (eps / 6) * (10 * Real.log N) ≤ x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2))))`. Apply `mul_le_mul he6h _ (by linarith) hs0` to reduce the goal to its premises. Establish `: C * Real.log x ≤ C * (x ^ (1 / 2 : ℝ) / (1 / 2))` using `mul_le_mul_of_nonneg_left hlx hC0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2)))) = 20 * C * x`.

Combine the equalities or inequalities in the displayed calculation. Establish `h3 : 20 * C * x ≤ x * x`. Establish `: 20 * C ≤ x` using `by have := le_abs_self C; linarith`. Conclude with `mul_le_mul_of_nonneg_right this hx0.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hgm1 : 0 < g - 1` using `by linarith`. Unfold `badBound`. Use `⟨hNbig, ?_, ?_⟩` and prove the remaining obligations. Establish `t1 : 0 ≤ 3 * f / g` using `div_nonneg (by linarith) hg0.le`. Establish `t2 : 0 ≤ 23 * f * Real.log g / Real.sqrt g` using `div_nonneg (mul_nonneg (by linarith) (Real.log_nonneg (by linarith))) (Real.sqrt_nonneg _)`.

Establish `t3 : 0 ≤ 2 * f * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1))` using `mul_nonneg (mul_nonneg (by linarith) hm1) (add_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg (by linarith) hgm1.le))`. Establish `t4 : 0 ≤ N / 2 * (7 / 8 : ℝ) ^ f` using `mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) _)`. Establish `t5 : 0 ≤ Real.exp (-(f / (10 * Real.log N)))` using `(Real.exp_pos _).le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `b1 : 3 * f / g ≤ 3 * P * E`.

Combine the equalities or inequalities in the displayed calculation. Establish `b2 : 23 * f * Real.log g / Real.sqrt g ≤ 92 * P * E`. Combine the equalities or inequalities in the displayed calculation. Establish `b3 : 2 * f * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) ≤ 2 * P * P * (E / 4 + 2 * P * E)`. Establish `hfm : 2 * f * m ≤ 2 * P * P` using `mul_le_mul (by linarith) hm2 hm1 (by linarith)`.

Establish `hsum : 1 / (4 * q) + (1 + Real.log N) / (g - 1) ≤ E / 4 + 2 * P * E`. Establish `: 2 * N * E ≤ 2 * P * E` using `mul_le_mul_of_nonneg_right (by linarith) hE0.le`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `mul_le_mul hfm hsum (add_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg (by linarith) hgm1.le)) (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))`. Establish `b4 : N / 2 * (7 / 8 : ℝ) ^ f ≤ P / 2 * E` using `mul_le_mul (by linarith) hT4 (Real.rpow_nonneg (by norm_num) _) (by linarith)`.

Establish `hP0 : 0 ≤ P` using `by linarith`. Establish `hPP : P ≤ P * P` using `le_mul_of_one_le_right hP0 hP1`. Establish `hPPP : P * P ≤ P ^ 3`. Rewrite using `[show P ^ 3 = P * P * P by ring]`. Conclude with `le_mul_of_one_le_right (mul_nonneg hP0 hP0) hP1`.

Establish `c1 : P * E ≤ P ^ 3 * E` using `mul_le_mul_of_nonneg_right (hPP.trans hPPP) hE0.le`. Establish `c2 : P * P * E ≤ P ^ 3 * E` using `mul_le_mul_of_nonneg_right hPPP hE0.le`. Establish `c3 : E ≤ P ^ 3 * E` using `le_mul_of_one_le_left hE0.le (hP1.trans (hPP.trans hPPP))`. Establish `hnn : 0 ≤ P ^ 3 * E` using `mul_nonneg (pow_nonneg hP0 3) hE0.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem badBound_numbers : ∀ eps C : ℝ, 0 < eps → eps ≤ 1 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (g f m N q : ℝ), Real.exp (8 * x ^ eps) ≤ g → x ^ (2 : ℝ) ≤ f → f ≤ x ^ C → 0 ≤ m → m ≤ x ^ C → x ^ eps ≤ N → N ≤ x ^ C → Real.exp (x ^ (eps / 6)) ≤ q → 100000 ≤ N ∧ 0 ≤ badBound g f m N q ∧ 6 * badBound g f m N q ≤ Real.exp (-(x ^ (eps / 7))) := by
  intro eps C he he1
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.1 (badBound_tail eps C he)
  refine ⟨max (max X1 8) (max (20 * |C| + 1) ((100000 : ℝ) ^ (1 / eps))), ?_⟩
  intro x hx g f m N q hg hf1 hf2 hm1 hm2 hN1 hN2 hq
  have hxX1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx8 : 8 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxC : 20 * |C| + 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxN : (100000 : ℝ) ^ (1 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx1' : 1 < x := by linarith
  have hNbig : 100000 ≤ N := by
    have e : (100000 : ℝ) = ((100000 : ℝ) ^ (1 / eps)) ^ eps := by
      rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel he.ne', Real.rpow_one]
    have h2 : ((100000 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps := Real.rpow_le_rpow (by positivity) hxN he.le
    linarith
  have hTail := hX1 x hxX1
  have hCe : eps ≤ C := (Real.rpow_le_rpow_left_iff hx1').1 (le_trans hN1 hN2)
  have hC0 : 0 ≤ C := by linarith
  set P := x ^ C with hP
  set E := Real.exp (-(x ^ (eps / 6))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hN0 : 0 < N := by linarith
  have hP1 : 1 ≤ P := Real.one_le_rpow hx1 hC0
  have hx2 : x ^ (2 : ℝ) = x * x := by rw [Real.rpow_two, sq]
  rw [hx2] at hf1
  have hf0 : 0 ≤ f := le_trans (by positivity) hf1
  have he6 : x ^ (eps / 6) ≤ x ^ eps := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have he6h : x ^ (eps / 6) ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsq : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by rw [← Real.rpow_add hx0]; norm_num
  have hs0 : 0 ≤ x ^ (1 / 2 : ℝ) := by positivity
  have hsx : x ^ (1 / 2 : ℝ) ≤ x := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hxe1 : 1 ≤ x ^ eps := Real.one_le_rpow hx1 he.le
  have hg8 : Real.exp 8 ≤ g := le_trans (Real.exp_le_exp.2 (by linarith)) hg
  have hg2 : 2 ≤ g := by have := Real.add_one_le_exp 8; linarith
  have hg0 : 0 < g := by linarith
  have hEg : 1 ≤ E * g := by
    calc (1 : ℝ) = E * Real.exp (x ^ (eps / 6)) := by rw [hE, ← Real.exp_add]; simp
      _ ≤ E * g := mul_le_mul_of_nonneg_left (le_trans (Real.exp_le_exp.2 (by linarith)) hg) hE0.le
  have hginv : 1 / g ≤ E := by rw [div_le_iff₀ hg0]; linarith
  have hT2 : Real.log g / Real.sqrt g ≤ 4 * E := by
    have h := log_div_sqrt_le_four_exp (u := 2 * x ^ eps) (g := g)
      (by rw [show 4 * (2 * x ^ eps) = 8 * x ^ eps by ring]; exact hg)
    refine h.trans ?_
    rw [hE]
    gcongr
    linarith
  have hLg : 0 ≤ Real.log g / Real.sqrt g :=
    div_nonneg (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _)
  have hq0 : 0 < q := lt_of_lt_of_le (Real.exp_pos _) hq
  have hEq : 1 ≤ E * q := by
    calc (1 : ℝ) = E * Real.exp (x ^ (eps / 6)) := by rw [hE, ← Real.exp_add]; simp
      _ ≤ E * q := mul_le_mul_of_nonneg_left hq hE0.le
  have hqinv : 1 / (4 * q) ≤ E / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hlogN : 1 + Real.log N ≤ N := by linarith [Real.log_le_sub_one_of_pos hN0]
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hT3b : (1 + Real.log N) / (g - 1) ≤ 2 * N * E := by
    rw [div_le_iff₀ (by linarith)]
    have h1 := mul_nonneg (mul_nonneg hN0.le hE0.le) (show 0 ≤ g - 2 by linarith)
    have h2 : N * 1 ≤ N * (E * g) := mul_le_mul_of_nonneg_left hEg hN0.le
    linarith
  have hT4 : (7 / 8 : ℝ) ^ f ≤ E := by
    rw [Real.rpow_def_of_pos (by norm_num), hE, Real.exp_le_exp]
    have hl78 : Real.log (7 / 8) ≤ -(1 / 8) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 8 by norm_num); linarith
    have h1 : Real.log (7 / 8) * f ≤ -(1 / 8) * f := mul_le_mul_of_nonneg_right hl78 hf0
    have h2 : 8 * x ≤ x * x := mul_le_mul_of_nonneg_right hx8 hx0.le
    linarith
  have hT5 : Real.exp (-(f / (10 * Real.log N))) ≤ E := by
    have hlN0 : 0 < Real.log N := Real.log_pos (by linarith)
    rw [hE, Real.exp_le_exp, neg_le_neg_iff, le_div_iff₀ (by linarith)]
    have hlN : Real.log N ≤ C * Real.log x := by
      rw [← Real.log_rpow hx0]; exact Real.log_le_log hN0 hN2
    have hlx : Real.log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div hx0.le (by norm_num)
    have h1 : x ^ (eps / 6) * (10 * Real.log N) ≤
        x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2)))) := by
      apply mul_le_mul he6h _ (by linarith) hs0
      have : C * Real.log x ≤ C * (x ^ (1 / 2 : ℝ) / (1 / 2)) := mul_le_mul_of_nonneg_left hlx hC0
      linarith
    have h2 : x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2)))) = 20 * C * x := by
      calc x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2))))
          = 20 * C * (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by ring
        _ = 20 * C * x := by rw [hsq]
    have h3 : 20 * C * x ≤ x * x := by
      have : 20 * C ≤ x := by have := le_abs_self C; linarith
      exact mul_le_mul_of_nonneg_right this hx0.le
    linarith
  have hgm1 : 0 < g - 1 := by linarith
  unfold badBound
  refine ⟨hNbig, ?_, ?_⟩
  · have t1 : 0 ≤ 3 * f / g := div_nonneg (by linarith) hg0.le
    have t2 : 0 ≤ 23 * f * Real.log g / Real.sqrt g :=
      div_nonneg (mul_nonneg (by linarith) (Real.log_nonneg (by linarith))) (Real.sqrt_nonneg _)
    have t3 : 0 ≤ 2 * f * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) :=
      mul_nonneg (mul_nonneg (by linarith) hm1)
        (add_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg (by linarith) hgm1.le))
    have t4 : 0 ≤ N / 2 * (7 / 8 : ℝ) ^ f := mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) _)
    have t5 : 0 ≤ Real.exp (-(f / (10 * Real.log N))) := (Real.exp_pos _).le
    linarith
  · have b1 : 3 * f / g ≤ 3 * P * E := by
      calc 3 * f / g = 3 * f * (1 / g) := by ring
        _ ≤ 3 * P * E := mul_le_mul (by linarith) hginv (div_nonneg zero_le_one hg0.le) (by linarith)
    have b2 : 23 * f * Real.log g / Real.sqrt g ≤ 92 * P * E := by
      calc 23 * f * Real.log g / Real.sqrt g = 23 * f * (Real.log g / Real.sqrt g) := by ring
        _ ≤ 23 * P * (4 * E) := mul_le_mul (by linarith) hT2 hLg (by linarith)
        _ = 92 * P * E := by ring
    have b3 : 2 * f * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) ≤ 2 * P * P * (E / 4 + 2 * P * E) := by
      have hfm : 2 * f * m ≤ 2 * P * P := mul_le_mul (by linarith) hm2 hm1 (by linarith)
      have hsum : 1 / (4 * q) + (1 + Real.log N) / (g - 1) ≤ E / 4 + 2 * P * E := by
        have : 2 * N * E ≤ 2 * P * E := mul_le_mul_of_nonneg_right (by linarith) hE0.le
        linarith
      exact mul_le_mul hfm hsum
        (add_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg (by linarith) hgm1.le))
        (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
    have b4 : N / 2 * (7 / 8 : ℝ) ^ f ≤ P / 2 * E :=
      mul_le_mul (by linarith) hT4 (Real.rpow_nonneg (by norm_num) _) (by linarith)
    have hP0 : 0 ≤ P := by linarith
    have hPP : P ≤ P * P := le_mul_of_one_le_right hP0 hP1
    have hPPP : P * P ≤ P ^ 3 := by
      rw [show P ^ 3 = P * P * P by ring]
      exact le_mul_of_one_le_right (mul_nonneg hP0 hP0) hP1
    have c1 : P * E ≤ P ^ 3 * E := mul_le_mul_of_nonneg_right (hPP.trans hPPP) hE0.le
    have c2 : P * P * E ≤ P ^ 3 * E := mul_le_mul_of_nonneg_right hPPP hE0.le
    have c3 : E ≤ P ^ 3 * E := le_mul_of_one_le_left hE0.le (hP1.trans (hPP.trans hPPP))
    have hnn : 0 ≤ P ^ 3 * E := mul_nonneg (pow_nonneg hP0 3) hE0.le
    linarith

end GlobalTheory.BadShare
