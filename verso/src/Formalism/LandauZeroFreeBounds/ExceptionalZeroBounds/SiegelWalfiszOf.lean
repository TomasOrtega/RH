import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf

open Complex Finset ArithmeticFunction

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `hq : (1:ℝ) ≤ q`. Establish `h1 : 1 ≤ q` using `Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)`. Conclude with `h1` after adjusting the coercions. Apply `Real.log_pos` to reduce the goal to its premises. Establish `ht` using `abs_nonneg t`.

Use the polynomial consequences of the given equalities and inequalities.
-/
lemma log_analytic_conductor_pos (q : ℕ) [NeZero q] (t : ℝ) : 0 < Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq : (1:ℝ) ≤ q := by
    have h1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast h1
  apply Real.log_pos
  have ht := abs_nonneg t
  nlinarith

/- English proof (translation)
Unfold `InRegion at hs ⊢`. Establish `hL` using `log_analytic_conductor_pos q s.im`. Establish `h2 : c / Real.log (↑q * (|s.im| + 2)) ≤ c' / Real.log (↑q * (|s.im| + 2))` using `by first`. Consider the case `exact div_le_div_of_nonneg_right h hL.le`. Consider the case `exact (div_le_div_iff_of_pos_right hL).mpr h`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma zero_free_region_mono {c c' : ℝ} (h : c ≤ c') {q : ℕ} [NeZero q] {s : ℂ} (hs : InRegion c q s) :
    InRegion c' q s := by
  unfold InRegion at hs ⊢
  have hL := log_analytic_conductor_pos q s.im
  have h2 : c / Real.log (↑q * (|s.im| + 2)) ≤ c' / Real.log (↑q * (|s.im| + 2)) := by
    first
      | exact div_le_div_of_nonneg_right h hL.le
      | exact (div_le_div_iff_of_pos_right hL).mpr h
  linarith

/- English proof (translation)
Unfold `InRegion at hs`. Establish `hL` using `log_analytic_conductor_pos q (β:ℂ).im`. Establish `h2 : (2:ℝ) ≤ (q:ℝ) * (|(β:ℂ).im| + 2)`. Establish `hq : (1:ℝ) ≤ q`. Establish `h1 : 1 ≤ q` using `Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)`.

Conclude with `h1` after adjusting the coercions. Establish `ht` using `abs_nonneg (β:ℂ).im`. Use the polynomial consequences of the given equalities and inequalities. Establish `hl2 : Real.log 2 ≤ Real.log ((q:ℝ) * (|(β:ℂ).im| + 2))` using `Real.log_le_log (by norm_num) h2`. Establish `hlt` using `Real.log_two_gt_d9`.

Establish `hc : c₁ / Real.log ((q:ℝ) * (|(β:ℂ).im| + 2)) ≤ 1 / 2`. Rewrite using `[div_le_iff₀ hL]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hre : (β:ℂ).re = β` using `Complex.ofReal_re β`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma half_le_of_real_in_region {c₁ : ℝ} (h : c₁ ≤ 1 / 20) {q : ℕ} [NeZero q] {β : ℝ} (hs : InRegion c₁ q (β : ℂ)) :
    1 / 2 ≤ β := by
  unfold InRegion at hs
  have hL := log_analytic_conductor_pos q (β:ℂ).im
  have h2 : (2:ℝ) ≤ (q:ℝ) * (|(β:ℂ).im| + 2) := by
    have hq : (1:ℝ) ≤ q := by
      have h1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      exact_mod_cast h1
    have ht := abs_nonneg (β:ℂ).im
    nlinarith
  have hl2 : Real.log 2 ≤ Real.log ((q:ℝ) * (|(β:ℂ).im| + 2)) := Real.log_le_log (by norm_num) h2
  have hlt := Real.log_two_gt_d9
  have hc : c₁ / Real.log ((q:ℝ) * (|(β:ℂ).im| + 2)) ≤ 1 / 2 := by
    rw [div_le_iff₀ hL]
    linarith
  have hre : (β:ℂ).re = β := Complex.ofReal_re β
  linarith

/- English proof (translation)
Distinguish the cases in `h : ∃ s : ℂ, InRegion c₁ q s ∧ IsLZero χ s`. Take `⟨s, hs, hL⟩` from `h`. Take `⟨-, hχ1, him, hder, huniq⟩` from `hZ q χ s (zero_free_region_mono hle hs) hL`. Use `⟨{s.re}, by simp, ?_, ?_⟩` and prove the remaining obligations. Introduce `β hβ`.

Rewrite `hβ` using `[Finset.mem_singleton]`. Substitute `hβ` using the available equality. Establish `hs' : s = ((s.re : ℝ) : ℂ)` using `Complex.ext (by simp) (by simp [him])`. Rewrite using `[← hs']`. Conclude with `⟨hχ1, hs, hL.2, hder⟩`.

Introduce `s' hs' hL'`. Take `⟨-, hss⟩` from `huniq χ s' (zero_free_region_mono hle hs') hL'`. Use `⟨s.re, Finset.mem_singleton_self _, ?_⟩` and prove the remaining obligations. Rewrite using `[hss]`. Conclude with `Complex.ext (by simp) (by simp [him])`.

Use `push_neg at h`. Use `⟨∅, by simp, by simp, ?_⟩` and prove the remaining obligations. Introduce `s hs hL`. Conclude with `absurd hL (h s hs)`.
-/
lemma exists_exceptional_zero_set (cZ c₁ : ℝ) (hle : c₁ ≤ cZ)
    (hZ : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      InRegion cZ q s → IsLZero χ s →
        χ ^ 2 = 1 ∧ χ ≠ 1 ∧ s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 ∧
        ∀ (χ' : DirichletCharacter ℂ q) (s' : ℂ), InRegion cZ q s' → IsLZero χ' s' → χ' = χ ∧ s' = s)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) : ∃ B : Finset ℝ, ExcZeros c₁ χ B := by
  by_cases h : ∃ s : ℂ, InRegion c₁ q s ∧ IsLZero χ s
  · obtain ⟨s, hs, hL⟩ := h
    obtain ⟨-, hχ1, him, hder, huniq⟩ := hZ q χ s (zero_free_region_mono hle hs) hL
    refine ⟨{s.re}, by simp, ?_, ?_⟩
    · intro β hβ
      rw [Finset.mem_singleton] at hβ
      subst hβ
      have hs' : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
      rw [← hs']
      exact ⟨hχ1, hs, hL.2, hder⟩
    · intro s' hs' hL'
      obtain ⟨-, hss⟩ := huniq χ s' (zero_free_region_mono hle hs') hL'
      refine ⟨s.re, Finset.mem_singleton_self _, ?_⟩
      rw [hss]
      exact Complex.ext (by simp) (by simp [him])
  · push_neg at h
    refine ⟨∅, by simp, by simp, ?_⟩
    intro s hs hL
    exact absurd hL (h s hs)

/- English proof (translation)
Establish `hx0 : (0:ℝ) ≤ x` using `by linarith`. Establish `hlx : 0 ≤ Real.log x` using `Real.log_nonneg hx`. Establish `h1 : ‖psiChi χ x‖ ≤ x * Real.log x`. Unfold `psiChi`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `n hn`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]`. Establish `hχ : ‖χ (n : ZMod q)‖ ≤ 1` using `DirichletCharacter.norm_le_one χ _`.

Establish `hn1 : 1 ≤ n` using `(Finset.mem_Icc.mp hn).1`. Establish `hnx : (n:ℝ) ≤ x` using `le_trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2) (Nat.floor_le hx0)`. Establish `hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log n` using `ArithmeticFunction.vonMangoldt_le_log`. Establish `hlog : Real.log n ≤ Real.log x` using `Real.log_le_log (Nat.cast_pos.mpr (by omega)) hnx`. Establish `hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n` using `ArithmeticFunction.vonMangoldt_nonneg`.

Combine the equalities or inequalities in the displayed calculation. Use `_ = ((Finset.Icc 1 ⌊x⌋₊).card : ℝ) * Real.log x := by rw [Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ x * Real.log x := by`. Apply `mul_le_mul_of_nonneg_right _ hlx` to reduce the goal to its premises. Rewrite using `[Nat.card_Icc, Nat.add_sub_cancel]`.

Conclude with `Nat.floor_le hx0`. Establish `h2 : ‖(if χ = 1 then (x : ℂ) else 0)‖ ≤ x` using `by split_ifs`. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg hx0]`. Rewrite using `[norm_zero]`. Conclude with `hx0`.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma chebyshev_character_trivial_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) (hx : 1 ≤ x) :
    ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤ x * (Real.log x + 1) := by
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : ‖psiChi χ x‖ ≤ x * Real.log x := by
    unfold psiChi
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log x := by
          apply Finset.sum_le_sum
          intro n hn
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          have hχ : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hnx : (n:ℝ) ≤ x :=
            le_trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2) (Nat.floor_le hx0)
          have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
          have hlog : Real.log n ≤ Real.log x := Real.log_le_log (Nat.cast_pos.mpr (by omega)) hnx
          have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
          calc ArithmeticFunction.vonMangoldt n * ‖χ (n : ZMod q)‖
              ≤ ArithmeticFunction.vonMangoldt n * 1 := mul_le_mul_of_nonneg_left hχ hΛ0
            _ ≤ Real.log x := by linarith
      _ = ((Finset.Icc 1 ⌊x⌋₊).card : ℝ) * Real.log x := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ x * Real.log x := by
          apply mul_le_mul_of_nonneg_right _ hlx
          rw [Nat.card_Icc, Nat.add_sub_cancel]
          exact Nat.floor_le hx0
  have h2 : ‖(if χ = 1 then (x : ℂ) else 0)‖ ≤ x := by
    split_ifs
    · rw [Complex.norm_real, Real.norm_of_nonneg hx0]
    · rw [norm_zero]
      exact hx0
  calc ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0)‖
      ≤ ‖psiChi χ x‖ + ‖(if χ = 1 then (x : ℂ) else 0)‖ := norm_sub_le _ _
    _ ≤ x * Real.log x + x := add_le_add h1 h2
    _ = x * (Real.log x + 1) := by ring

/- English proof (translation)
Establish `hx0 : (0:ℝ) < x` using `by linarith`. Establish `hβ0 : (0:ℝ) < β` using `by linarith`. Establish `hlog : 0 < Real.log x` using `Real.log_pos (by linarith)`. Establish `hn : ‖(x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ = x ^ β / β`. Rewrite using `[norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg hβ0.le]`.

Rewrite using `[hn]`. Establish `hq0 : (0:ℝ) < q` using `by linarith`. Establish `hA0 : A ≠ 0` using `hA.ne'`. Establish `h1 : q ^ (1 / (2 * A)) ≤ Real.sqrt (Real.log x)`. Rewrite using `[Real.sqrt_eq_rpow]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_mul hlog.le]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `h2 : q ^ (-(1 / (2 * A))) = (q ^ (1 / (2 * A)))⁻¹` using `Real.rpow_neg hq0.le _`.

Establish `hs : 0 < Real.sqrt (Real.log x)` using `Real.sqrt_pos.mpr hlog`. Establish `hqa : 0 < q ^ (1 / (2 * A))` using `Real.rpow_pos_of_pos hq0 _`. Establish `h3 : cE / Real.sqrt (Real.log x) ≤ 1 - β`. Establish `h3a : cE * q ^ (-(1 / (2 * A))) ≤ 1 - β` using `by linarith`. Rewrite `h3a` using `[h2]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h4 : (β - 1) * Real.log x ≤ -cE * Real.sqrt (Real.log x)`. Establish `hsq : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x` using `Real.mul_self_sqrt hlog.le`. Establish `h4a` using `(div_le_iff₀ hs).mp h3`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h5 : x ^ β ≤ x * Real.exp (-cE * Real.sqrt (Real.log x))`. Establish `e1 : x * Real.exp (-cE * Real.sqrt (Real.log x)) = Real.exp (Real.log x + -cE * Real.sqrt (Real.log x))`. Rewrite using `[Real.exp_add, Real.exp_log hx0]`. Rewrite using `[e1, Real.rpow_def_of_pos hx0]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Establish `h6 : x ^ β / β ≤ 2 * x ^ β`. Rewrite using `[div_le_iff₀ hβ0]`. Establish `h6a` using `Real.rpow_pos_of_pos hx0 β`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear relations using `[h5, h6]`.
-/
lemma exceptional_zero_term_bound (x A q cE β : ℝ) (hx : 2 ≤ x) (hA : 0 < A) (hq : 1 ≤ q)
    (hqL : q ≤ Real.log x ^ A) (hcE : 0 < cE) (hβ1 : 1 / 2 ≤ β)
    (hβ2 : β ≤ 1 - cE * q ^ (-(1 / (2 * A)))) :
    ‖(x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ 2 * x * Real.exp (-cE * Real.sqrt (Real.log x)) := by
  have hx0 : (0:ℝ) < x := by linarith
  have hβ0 : (0:ℝ) < β := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hn : ‖(x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ = x ^ β / β := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.ofReal_re, Complex.norm_real,
      Real.norm_of_nonneg hβ0.le]
  rw [hn]
  have hq0 : (0:ℝ) < q := by linarith
  have hA0 : A ≠ 0 := hA.ne'
  have h1 : q ^ (1 / (2 * A)) ≤ Real.sqrt (Real.log x) := by
    rw [Real.sqrt_eq_rpow]
    calc q ^ (1 / (2 * A)) ≤ (Real.log x ^ A) ^ (1 / (2 * A)) :=
          Real.rpow_le_rpow hq0.le hqL (by positivity)
      _ = Real.log x ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul hlog.le]
          congr 1
          field_simp
  have h2 : q ^ (-(1 / (2 * A))) = (q ^ (1 / (2 * A)))⁻¹ := Real.rpow_neg hq0.le _
  have hs : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hlog
  have hqa : 0 < q ^ (1 / (2 * A)) := Real.rpow_pos_of_pos hq0 _
  have h3 : cE / Real.sqrt (Real.log x) ≤ 1 - β := by
    have h3a : cE * q ^ (-(1 / (2 * A))) ≤ 1 - β := by linarith
    rw [h2] at h3a
    calc cE / Real.sqrt (Real.log x) ≤ cE / q ^ (1 / (2 * A)) :=
          div_le_div_of_nonneg_left hcE.le hqa h1
      _ = cE * (q ^ (1 / (2 * A)))⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 1 - β := h3a
  have h4 : (β - 1) * Real.log x ≤ -cE * Real.sqrt (Real.log x) := by
    have hsq : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x := Real.mul_self_sqrt hlog.le
    have h4a := (div_le_iff₀ hs).mp h3
    nlinarith
  have h5 : x ^ β ≤ x * Real.exp (-cE * Real.sqrt (Real.log x)) := by
    have e1 : x * Real.exp (-cE * Real.sqrt (Real.log x)) =
        Real.exp (Real.log x + -cE * Real.sqrt (Real.log x)) := by
      rw [Real.exp_add, Real.exp_log hx0]
    rw [e1, Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    nlinarith
  have h6 : x ^ β / β ≤ 2 * x ^ β := by
    rw [div_le_iff₀ hβ0]
    have h6a := Real.rpow_pos_of_pos hx0 β
    nlinarith
  linarith [h5, h6]

/- English proof (translation)
Establish `ho` using `(isLittleO_rpow_exp_pos_mul_atTop (2 * A) hc).comp_tendsto Real.tendsto_sqrt_atTop`. Establish `hb` using `ho.bound (show (0:ℝ) < 1 / 2 by norm_num)`. Take `⟨N, hN⟩` from `Filter.eventually_atTop.mp hb`. Use `⟨max N 0, le_max_right _ _, fun L hL hlt => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `hLN : N ≤ L` using `le_trans (le_max_left _ _) hcon.le`. Establish `h2 : ‖Real.sqrt L ^ (2 * A)‖ ≤ 1 / 2 * ‖Real.exp (c * Real.sqrt L)‖` using `hN L hLN`. Establish `hs : Real.sqrt L ^ (2 * A) = L ^ A`. Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_mul hL.le]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le, hs]`. Combine the linear relations using `[Real.exp_pos (c * Real.sqrt L)]`.
-/
lemma bounded_of_exp_sqrt_lt_pow (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ L : ℝ, 0 < L → Real.exp (c * Real.sqrt L) < L ^ A → L ≤ U := by
  have ho := (isLittleO_rpow_exp_pos_mul_atTop (2 * A) hc).comp_tendsto Real.tendsto_sqrt_atTop
  have hb := ho.bound (show (0:ℝ) < 1 / 2 by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hb
  refine ⟨max N 0, le_max_right _ _, fun L hL hlt => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hLN : N ≤ L := le_trans (le_max_left _ _) hcon.le
  have h2 : ‖Real.sqrt L ^ (2 * A)‖ ≤ 1 / 2 * ‖Real.exp (c * Real.sqrt L)‖ := hN L hLN
  have hs : Real.sqrt L ^ (2 * A) = L ^ A := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL.le]
    congr 1
    ring
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le, hs] at h2
  linarith [Real.exp_pos (c * Real.sqrt L)]

/- English proof (translation)
Introduce `hP hZ hE A hA`. Take `⟨cZ, hcZ, hZ'⟩` from `hZ`. Use `set c₁ : ℝ := min cZ (1 / 20) with hc₁`. Establish `hc₁0 : 0 < c₁` using `lt_min hcZ (by norm_num)`. Establish `hc₁20 : c₁ ≤ 1 / 20` using `min_le_right _ _`.

Establish `hc₁Z : c₁ ≤ cZ` using `min_le_left _ _`. Take `⟨c, C, hc, hPC⟩` from `hP c₁ hc₁0 hc₁20`. Take `⟨cE, hcE, hEB⟩` from `hE (1 / (2 * A)) (by positivity)`. Take `⟨U, hU0, hU⟩` from `bounded_of_exp_sqrt_lt_pow A c hA hc`. Use `set cf : ℝ := min c cE with hcf`.

Establish `hcf0 : 0 < cf` using `lt_min hc hcE`. Establish `hK0 : 0 ≤ (U + 1) * Real.exp (cf * Real.sqrt U)` using `mul_nonneg (by linarith) (Real.exp_pos _).le`. Use `⟨cf, (max C 0 + 2) + (U + 1) * Real.exp (cf * Real.sqrt U), hcf0, ?_⟩` and prove the remaining obligations. Introduce `q _ χ x hx hqL`. Establish `hx0 : (0:ℝ) ≤ x` using `by linarith`.

Establish `hx1 : (1:ℝ) ≤ x` using `by linarith`. Establish `hlx : 0 < Real.log x` using `Real.log_pos (by linarith)`. Establish `hq1 : (1:ℝ) ≤ q`. Establish `h1 : 1 ≤ q` using `Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)`. Conclude with `h1` after adjusting the coercions.

Establish `hM0 : 0 ≤ (max C 0 + 2) * x * Real.exp (-cf * Real.sqrt (Real.log x))` using `mul_nonneg (mul_nonneg (by linarith [le_max_right C 0]) hx0) (Real.exp_pos _).le`. Establish `hK : 0 ≤ (U + 1) * Real.exp (cf * Real.sqrt U) * x * Real.exp (-cf * Real.sqrt (Real.log x))` using `mul_nonneg (mul_nonneg hK0 hx0) (Real.exp_pos _).le`. Establish `hfin : ((max C 0 + 2) + (U + 1) * Real.exp (cf * Real.sqrt U)) * x * Real.exp (-cf * Real.sqrt (Real.log x)) = (max C 0 + 2) * x * Real.exp (-cf * Real.sqrt (Real.log x)) + (U + 1) * Real.exp (cf * Real.sqrt U) * x * Real.exp (-cf * Real.sqrt (Real.log x))` using `by ring`. Rewrite using `[hfin]`. Distinguish the cases in `hsmall : Real.exp (c * Real.sqrt (Real.log x)) < Real.log x ^ A`.

Establish `hLU : Real.log x ≤ U` using `hU (Real.log x) hlx hsmall`. Establish `htriv` using `chebyshev_character_trivial_bound χ x hx1`. Establish `hsqU : Real.sqrt (Real.log x) ≤ Real.sqrt U` using `Real.sqrt_le_sqrt hLU`. Establish `he : 1 ≤ Real.exp (cf * Real.sqrt U) * Real.exp (-cf * Real.sqrt (Real.log x))`. Rewrite using `[← Real.exp_add]`.

Apply `Real.one_le_exp` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `hxU : 0 ≤ x * (U + 1)` using `mul_nonneg hx0 (by linarith)`. Establish `s1 : x * (Real.log x + 1) ≤ x * (U + 1)` using `mul_le_mul_of_nonneg_left (by linarith) hx0`. Establish `s2 : x * (U + 1) ≤ x * (U + 1) * (Real.exp (cf * Real.sqrt U) * Real.exp (-cf * Real.sqrt (Real.log x)))` using `le_mul_of_one_le_right hxU he`.

Establish `s3 : x * (U + 1) * (Real.exp (cf * Real.sqrt U) * Real.exp (-cf * Real.sqrt (Real.log x))) = (U + 1) * Real.exp (cf * Real.sqrt U) * x * Real.exp (-cf * Real.sqrt (Real.log x))` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Use `push_neg at hsmall`. Establish `hqexp : (q:ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x))` using `le_trans hqL hsmall`. Take `⟨B, hB⟩` from `exists_exceptional_zero_set cZ c₁ hc₁Z hZ' q χ`.

Establish `hmain` using `hPC q χ B x hB hx hqexp`. Establish `hsumB : ‖∑ β ∈ B, (x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ 2 * x * Real.exp (-cE * Real.sqrt (Real.log x))`. Take `⟨hcard, hmem, -⟩` from `hB`. Break down `B.eq_empty_or_nonempty with hBe | ⟨β, hβ⟩` into its components or cases. Rewrite using `[hBe, Finset.sum_empty, norm_zero]`.

Conclude with `mul_nonneg (by linarith) (Real.exp_pos _).le`. Establish `hBs : B = {β}` using `Finset.eq_singleton_iff_unique_mem.mpr ⟨hβ, fun b hb => Finset.card_le_one.mp hcard b hb β hβ⟩`. Rewrite using `[hBs, Finset.sum_singleton]`. Take `⟨hχ1, hreg, hL0, -⟩` from `hmem β hβ`. Establish `hβ1 : 1 / 2 ≤ β` using `half_le_of_real_in_region hc₁20 hreg`.

Establish `hχ2 : χ ^ 2 = 1` using `(hZ' q χ (β:ℂ) (zero_free_region_mono hc₁Z hreg) ⟨Or.inl hχ1, hL0⟩).1`. Establish `hβ2` using `hEB q χ β hχ2 hχ1 hL0`. Conclude with `exceptional_zero_term_bound x A q cE β hx hA hq1 hqL hcE hβ1 hβ2`. Establish `e1 : Real.exp (-c * Real.sqrt (Real.log x)) ≤ Real.exp (-cf * Real.sqrt (Real.log x))`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises.

Establish `h1 : cf ≤ c` using `min_le_left _ _`. Establish `h2` using `Real.sqrt_nonneg (Real.log x)`. Use the polynomial consequences of the given equalities and inequalities. Establish `e2 : Real.exp (-cE * Real.sqrt (Real.log x)) ≤ Real.exp (-cf * Real.sqrt (Real.log x))`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises.

Establish `h1 : cf ≤ cE` using `min_le_right _ _`. Establish `h2` using `Real.sqrt_nonneg (Real.log x)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hC : C * x * Real.exp (-c * Real.sqrt (Real.log x)) ≤ max C 0 * x * Real.exp (-cf * Real.sqrt (Real.log x))`. Combine the equalities or inequalities in the displayed calculation.

Establish `hE2 : 2 * x * Real.exp (-cE * Real.sqrt (Real.log x)) ≤ 2 * x * Real.exp (-cf * Real.sqrt (Real.log x))` using `mul_le_mul_of_nonneg_left e2 (by linarith)`. Use `set S : ℂ := ∑ β ∈ B, (x : ℂ) ^ (β : ℂ) / (β : ℂ) with hS`. Use `set a : ℂ := psiChi χ x - (if χ = 1 then (x : ℂ) else 0) with ha`. Establish `htri : ‖a‖ ≤ ‖a + S‖ + ‖S‖`. Combine the equalities or inequalities in the displayed calculation.

Establish `hsplit : (max C 0 + 2) * x * Real.exp (-cf * Real.sqrt (Real.log x)) = max C 0 * x * Real.exp (-cf * Real.sqrt (Real.log x)) + 2 * x * Real.exp (-cf * Real.sqrt (Real.log x))` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem siegel_walfisz_character_of : SiegelWalfiszOf := by
  intro hP hZ hE A hA
  obtain ⟨cZ, hcZ, hZ'⟩ := hZ
  set c₁ : ℝ := min cZ (1 / 20) with hc₁
  have hc₁0 : 0 < c₁ := lt_min hcZ (by norm_num)
  have hc₁20 : c₁ ≤ 1 / 20 := min_le_right _ _
  have hc₁Z : c₁ ≤ cZ := min_le_left _ _
  obtain ⟨c, C, hc, hPC⟩ := hP c₁ hc₁0 hc₁20
  obtain ⟨cE, hcE, hEB⟩ := hE (1 / (2 * A)) (by positivity)
  obtain ⟨U, hU0, hU⟩ := bounded_of_exp_sqrt_lt_pow A c hA hc
  set cf : ℝ := min c cE with hcf
  have hcf0 : 0 < cf := lt_min hc hcE
  have hK0 : 0 ≤ (U + 1) * Real.exp (cf * Real.sqrt U) :=
    mul_nonneg (by linarith) (Real.exp_pos _).le
  refine ⟨cf, (max C 0 + 2) + (U + 1) * Real.exp (cf * Real.sqrt U), hcf0, ?_⟩
  intro q _ χ x hx hqL
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hq1 : (1:ℝ) ≤ q := by
    have h1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast h1
  have hM0 : 0 ≤ (max C 0 + 2) * x * Real.exp (-cf * Real.sqrt (Real.log x)) :=
    mul_nonneg (mul_nonneg (by linarith [le_max_right C 0]) hx0) (Real.exp_pos _).le
  have hK : 0 ≤ (U + 1) * Real.exp (cf * Real.sqrt U) * x * Real.exp (-cf * Real.sqrt (Real.log x)) :=
    mul_nonneg (mul_nonneg hK0 hx0) (Real.exp_pos _).le
  have hfin : ((max C 0 + 2) + (U + 1) * Real.exp (cf * Real.sqrt U)) * x *
      Real.exp (-cf * Real.sqrt (Real.log x)) =
      (max C 0 + 2) * x * Real.exp (-cf * Real.sqrt (Real.log x)) +
      (U + 1) * Real.exp (cf * Real.sqrt U) * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by ring
  rw [hfin]
  by_cases hsmall : Real.exp (c * Real.sqrt (Real.log x)) < Real.log x ^ A
  · have hLU : Real.log x ≤ U := hU (Real.log x) hlx hsmall
    have htriv := chebyshev_character_trivial_bound χ x hx1
    have hsqU : Real.sqrt (Real.log x) ≤ Real.sqrt U := Real.sqrt_le_sqrt hLU
    have he : 1 ≤ Real.exp (cf * Real.sqrt U) * Real.exp (-cf * Real.sqrt (Real.log x)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    have hxU : 0 ≤ x * (U + 1) := mul_nonneg hx0 (by linarith)
    have s1 : x * (Real.log x + 1) ≤ x * (U + 1) := mul_le_mul_of_nonneg_left (by linarith) hx0
    have s2 : x * (U + 1) ≤ x * (U + 1) * (Real.exp (cf * Real.sqrt U) * Real.exp (-cf * Real.sqrt (Real.log x))) :=
      le_mul_of_one_le_right hxU he
    have s3 : x * (U + 1) * (Real.exp (cf * Real.sqrt U) * Real.exp (-cf * Real.sqrt (Real.log x))) =
        (U + 1) * Real.exp (cf * Real.sqrt U) * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by ring
    linarith
  · push_neg at hsmall
    have hqexp : (q:ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x)) := le_trans hqL hsmall
    obtain ⟨B, hB⟩ := exists_exceptional_zero_set cZ c₁ hc₁Z hZ' q χ
    have hmain := hPC q χ B x hB hx hqexp
    have hsumB : ‖∑ β ∈ B, (x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
        2 * x * Real.exp (-cE * Real.sqrt (Real.log x)) := by
      obtain ⟨hcard, hmem, -⟩ := hB
      rcases B.eq_empty_or_nonempty with hBe | ⟨β, hβ⟩
      · rw [hBe, Finset.sum_empty, norm_zero]
        exact mul_nonneg (by linarith) (Real.exp_pos _).le
      · have hBs : B = {β} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hβ, fun b hb => Finset.card_le_one.mp hcard b hb β hβ⟩
        rw [hBs, Finset.sum_singleton]
        obtain ⟨hχ1, hreg, hL0, -⟩ := hmem β hβ
        have hβ1 : 1 / 2 ≤ β := half_le_of_real_in_region hc₁20 hreg
        have hχ2 : χ ^ 2 = 1 := (hZ' q χ (β:ℂ) (zero_free_region_mono hc₁Z hreg) ⟨Or.inl hχ1, hL0⟩).1
        have hβ2 := hEB q χ β hχ2 hχ1 hL0
        exact exceptional_zero_term_bound x A q cE β hx hA hq1 hqL hcE hβ1 hβ2
    have e1 : Real.exp (-c * Real.sqrt (Real.log x)) ≤ Real.exp (-cf * Real.sqrt (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      have h1 : cf ≤ c := min_le_left _ _
      have h2 := Real.sqrt_nonneg (Real.log x)
      nlinarith
    have e2 : Real.exp (-cE * Real.sqrt (Real.log x)) ≤ Real.exp (-cf * Real.sqrt (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      have h1 : cf ≤ cE := min_le_right _ _
      have h2 := Real.sqrt_nonneg (Real.log x)
      nlinarith
    have hC : C * x * Real.exp (-c * Real.sqrt (Real.log x)) ≤
        max C 0 * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
      calc C * x * Real.exp (-c * Real.sqrt (Real.log x))
          ≤ max C 0 * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0) (Real.exp_pos _).le
        _ ≤ max C 0 * x * Real.exp (-cf * Real.sqrt (Real.log x)) :=
            mul_le_mul_of_nonneg_left e1 (mul_nonneg (le_max_right _ _) hx0)
    have hE2 : 2 * x * Real.exp (-cE * Real.sqrt (Real.log x)) ≤
        2 * x * Real.exp (-cf * Real.sqrt (Real.log x)) :=
      mul_le_mul_of_nonneg_left e2 (by linarith)
    set S : ℂ := ∑ β ∈ B, (x : ℂ) ^ (β : ℂ) / (β : ℂ) with hS
    set a : ℂ := psiChi χ x - (if χ = 1 then (x : ℂ) else 0) with ha
    have htri : ‖a‖ ≤ ‖a + S‖ + ‖S‖ := by
      calc ‖a‖ = ‖(a + S) - S‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖a + S‖ + ‖S‖ := norm_sub_le _ _
    have hsplit : (max C 0 + 2) * x * Real.exp (-cf * Real.sqrt (Real.log x)) =
        max C 0 * x * Real.exp (-cf * Real.sqrt (Real.log x)) +
        2 * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by ring
    linarith

end Formalism.ZeroFreeDirichlet
