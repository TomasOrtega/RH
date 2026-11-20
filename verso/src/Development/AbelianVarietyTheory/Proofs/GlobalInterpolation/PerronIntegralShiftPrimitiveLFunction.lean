import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBoundRight
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivLFunctionNearZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AnalyticAtDslope
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.PerronShift

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Use `le_trans ?_ (Complex.abs_re_le_norm (s - w))` and prove the remaining obligations. Rewrite using `[Complex.sub_re, hs]`. Break down `le_or_gt w.re 0 with hre | hre` into its components or cases. Take `⟨⟨n, rfl⟩, -⟩` from `_root_.GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ w hre hw`. Simplify using `only [Complex.neg_re, Complex.natCast_re]`.

Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Evaluate the numerical expressions. Establish `: (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Rewrite using `[abs_of_nonneg (by linarith)]; linarith`. Rewrite using `[abs_of_neg (by linarith)]; linarith`.
-/
private theorem half_le_norm_sub_of_re_eq_neg_half_of_LFunction_eq_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {s w : ℂ} (hs : s.re = -(1 / 2))
    (hw : LFunction χ w = 0) : 1 / 2 ≤ ‖s - w‖ := by
  refine le_trans ?_ (Complex.abs_re_le_norm (s - w))
  rw [Complex.sub_re, hs]
  rcases le_or_gt w.re 0 with hre | hre
  · obtain ⟨⟨n, rfl⟩, -⟩ := _root_.GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ w hre hw
    simp only [Complex.neg_re, Complex.natCast_re]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Introduce `h`. Use `half_le_norm_sub_of_re_eq_neg_half_of_LFunction_eq_zero χ hχ hs h` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem LFunction_ne_zero_of_re_eq_neg_half {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {s : ℂ} (hs : s.re = -(1 / 2)) :
    LFunction χ s ≠ 0 := by
  intro h
  have := half_le_norm_sub_of_re_eq_neg_half_of_LFunction_eq_zero χ hχ hs h
  simp at this
  linarith

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS, Finset.mul_sum]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun w hw => ?_)` and prove the remaining obligations. Establish `hw'` using `hd w (hS.mem_toFinset.mp hw)`. Establish `hpos : 0 < ‖s - w‖` using `by linarith`. Rewrite using `[norm_div, Complex.norm_natCast, div_le_iff₀ hpos]`.

Establish `: (0 : ℝ) ≤ k w` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem norm_finsum_div_sub_le_two_mul_finsum_of_half_le_dist {S : Set ℂ} (hS : S.Finite) (k : ℂ → ℕ) (s : ℂ)
    (hd : ∀ w ∈ S, 1 / 2 ≤ ‖s - w‖) :
    ‖∑ᶠ (w : ℂ) (_ : w ∈ S), (k w : ℂ) / (s - w)‖ ≤ 2 * ∑ᶠ (w : ℂ) (_ : w ∈ S), (k w : ℝ) := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS,
    Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w hw => ?_)
  have hw' := hd w (hS.mem_toFinset.mp hw)
  have hpos : 0 < ‖s - w‖ := by linarith
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hpos]
  have : (0 : ℝ) ≤ k w := Nat.cast_nonneg _
  nlinarith

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Take `⟨C₁, hC₁, H₁⟩` from `_root_.GlobalTheory.LWide.logDeriv_LFunction_strip`. Take `⟨C₂, hC₂, H₂⟩` from `_root_.GlobalTheory.ZetaWide.main`. Use `⟨3 * C₁ + 3 * C₂ + 1, by positivity, fun N _ χ hχ t => ?_⟩` and prove the remaining obligations. Use `set s : ℂ := ((-(1 / 2) : ℝ) : ℂ) + t * I with hs_def`. Establish `hre : s.re = -(1 / 2)` using `by simp [s]`.

Establish `him : s.im = t` using `by simp [s]`. Establish `hlog2 : (2 / 3 : ℝ) < Real.log 2`. Use `Real.log_two_gt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht2 : Real.log 2 ≤ Real.log (|t| + 2)` using `Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])`.

Establish `hN : (1 : ℝ) ≤ N` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)`. Establish `hlogN : Real.log (|t| + 2) ≤ Real.log (N * (|t| + 2))` using `Real.log_le_log (by positivity) (by nlinarith [abs_nonneg t])`. Establish `hL0 : 0 ≤ Real.log (N * (|t| + 2))` using `by linarith`. Distinguish the cases in `h1 : χ = 1`. Substitute `h1` using the available equality.

Establish `hN1 : N = 1`. Establish `h` using `hχ`. Rewrite `h` using `[DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one]`. Conclude with `h.symm`. Substitute `hN1` using the available equality.

Rewrite using `[LFunction_modOne_eq]`. Establish `hs1 : s ≠ 1`. Introduce `h`. Use `congrArg Complex.re h` as an intermediate fact. Rewrite `this` using `[hre]`.

Evaluate the numerical expressions using `at this`. Establish `hz : riemannZeta s ≠ 0`. Use `LFunction_ne_zero_of_re_eq_neg_half (1 : DirichletCharacter ℂ 1) hχ hre` as an intermediate fact. Rewrite `this` using `[LFunction_modOne_eq]`. Then use the resulting hypothesis. Take `⟨hfin, hcnt, hbd⟩` from `H₂ s (by rw [hre]; norm_num) (by rw [hre]; norm_num) hs1 hz`.

Establish `hsum` using `norm_finsum_div_sub_le_two_mul_finsum_of_half_le_dist hfin (analyticOrderNatAt riemannZeta) s (fun w hw => half_le_norm_sub_of_re_eq_neg_half_of_LFunction_eq_zero (1 : DirichletCharacter ℂ 1) hχ hre (by rw [LFunction_modOne_eq]; exact hw.2.2))`. Establish `hinv : ‖1 / (s - 1)‖ ≤ 2 / 3`. Establish `: (3 / 2 : ℝ) ≤ ‖s - 1‖`. Use `le_trans ?_ (Complex.abs_re_le_norm _)` and prove the remaining obligations. Rewrite using `[Complex.sub_re, hre, Complex.one_re]`.

Evaluate the numerical expressions. Rewrite using `[norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith`. Establish `key : ‖deriv riemannZeta s / riemannZeta s‖ ≤ C₂ * Real.log (|s.im| + 2) + 2 * (C₂ * Real.log (|s.im| + 2)) + 2 / 3`. Establish `e : deriv riemannZeta s / riemannZeta s = (deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - ∑ᶠ (w : ℂ) (_ : w ∈ {w | ‖w - (2 + ↑s.im * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧ riemannZeta w = 0}), (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)) + ∑ᶠ (w : ℂ) (_ : w ∈ {w | ‖w - (2 + ↑s.im * I)‖ …` using `by ring`. Rewrite using `[e]`.

Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Use `add_le_add ((norm_add_le _ _).trans (add_le_add hbd ?_)) hinv` and prove the remaining obligations. Conclude with `hsum.trans (by linarith)`. Rewrite `key` using `[him]`. Simplify using `only [Nat.cast_one, one_mul]`.

Use polynomial arithmetic with `[mul_nonneg hC₁.le (by linarith : (0:ℝ) ≤ Real.log (|t| + 2))]`. Establish `hLs` using `LFunction_ne_zero_of_re_eq_neg_half χ hχ hre`. Take `⟨hfin, hcnt, hbd⟩` from `H₁ N χ h1 s (by rw [hre]; norm_num) (by rw [hre]; norm_num) hLs`. Rewrite `hcnt`, `hbd` using `[him]`. Establish `hsum` using `norm_finsum_div_sub_le_two_mul_finsum_of_half_le_dist hfin (analyticOrderNatAt (LFunction χ)) s (fun w hw => half_le_norm_sub_of_re_eq_neg_half_of_LFunction_eq_zero χ hχ hre hw.2)`.

Rewrite `hsum` using `[him]`. Establish `e : deriv (LFunction χ) s / LFunction χ s = (deriv (LFunction χ) s / LFunction χ s - ∑ᶠ (w : ℂ) (_ : w ∈ {w | ‖w - (2 + ↑t * I)‖ ≤ 7 / 2 ∧ LFunction χ w = 0}), (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)) + ∑ᶠ (w : ℂ) (_ : w ∈ {w | ‖w - (2 + ↑t * I)‖ ≤ 7 / 2 ∧ LFunction χ …` using `by ring`. Rewrite using `[e]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Use `add_le_add hbd (hsum.trans (by linarith : _ ≤ 2 * (C₁ * Real.log (N * (|t| + 2)))))` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem exists_norm_logDeriv_LFunction_neg_half_le_log_conductor :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ t : ℝ, ‖deriv (LFunction χ) (((-(1 / 2) : ℝ) : ℂ) + t * I) /
        LFunction χ (((-(1 / 2) : ℝ) : ℂ) + t * I)‖ ≤ C * Real.log (N * (|t| + 2)) := by
  obtain ⟨C₁, hC₁, H₁⟩ := _root_.GlobalTheory.LWide.logDeriv_LFunction_strip
  obtain ⟨C₂, hC₂, H₂⟩ := _root_.GlobalTheory.ZetaWide.main
  refine ⟨3 * C₁ + 3 * C₂ + 1, by positivity, fun N _ χ hχ t => ?_⟩
  set s : ℂ := ((-(1 / 2) : ℝ) : ℂ) + t * I with hs_def
  have hre : s.re = -(1 / 2) := by simp [s]
  have him : s.im = t := by simp [s]
  have hlog2 : (2 / 3 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have ht2 : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlogN : Real.log (|t| + 2) ≤ Real.log (N * (|t| + 2)) :=
    Real.log_le_log (by positivity) (by nlinarith [abs_nonneg t])
  have hL0 : 0 ≤ Real.log (N * (|t| + 2)) := by linarith
  by_cases h1 : χ = 1
  · subst h1
    have hN1 : N = 1 := by
      have h := hχ
      rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hN1
    rw [LFunction_modOne_eq]
    have hs1 : s ≠ 1 := by
      intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
    have hz : riemannZeta s ≠ 0 := by
      have := LFunction_ne_zero_of_re_eq_neg_half (1 : DirichletCharacter ℂ 1) hχ hre
      rwa [LFunction_modOne_eq] at this
    obtain ⟨hfin, hcnt, hbd⟩ := H₂ s (by rw [hre]; norm_num) (by rw [hre]; norm_num) hs1 hz
    have hsum := norm_finsum_div_sub_le_two_mul_finsum_of_half_le_dist hfin (analyticOrderNatAt riemannZeta) s
      (fun w hw => half_le_norm_sub_of_re_eq_neg_half_of_LFunction_eq_zero (1 : DirichletCharacter ℂ 1) hχ hre
        (by rw [LFunction_modOne_eq]; exact hw.2.2))
    have hinv : ‖1 / (s - 1)‖ ≤ 2 / 3 := by
      have : (3 / 2 : ℝ) ≤ ‖s - 1‖ := by
        refine le_trans ?_ (Complex.abs_re_le_norm _)
        rw [Complex.sub_re, hre, Complex.one_re]; norm_num
      rw [norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith
    have key : ‖deriv riemannZeta s / riemannZeta s‖ ≤ C₂ * Real.log (|s.im| + 2)
        + 2 * (C₂ * Real.log (|s.im| + 2)) + 2 / 3 := by
      have e : deriv riemannZeta s / riemannZeta s = (deriv riemannZeta s / riemannZeta s
          + 1 / (s - 1) - ∑ᶠ (w : ℂ) (_ : w ∈ {w | ‖w - (2 + ↑s.im * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧
            riemannZeta w = 0}), (analyticOrderNatAt riemannZeta w : ℂ) / (s - w))
          + ∑ᶠ (w : ℂ) (_ : w ∈ {w | ‖w - (2 + ↑s.im * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧
            riemannZeta w = 0}), (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)
          - 1 / (s - 1) := by ring
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      refine add_le_add ((norm_add_le _ _).trans (add_le_add hbd ?_)) hinv
      exact hsum.trans (by linarith)
    rw [him] at key
    simp only [Nat.cast_one, one_mul]
    nlinarith [mul_nonneg hC₁.le (by linarith : (0:ℝ) ≤ Real.log (|t| + 2))]
  · have hLs := LFunction_ne_zero_of_re_eq_neg_half χ hχ hre
    obtain ⟨hfin, hcnt, hbd⟩ := H₁ N χ h1 s (by rw [hre]; norm_num) (by rw [hre]; norm_num) hLs
    rw [him] at hcnt hbd
    have hsum := norm_finsum_div_sub_le_two_mul_finsum_of_half_le_dist hfin (analyticOrderNatAt (LFunction χ)) s
      (fun w hw => half_le_norm_sub_of_re_eq_neg_half_of_LFunction_eq_zero χ hχ hre hw.2)
    rw [him] at hsum
    have e : deriv (LFunction χ) s / LFunction χ s = (deriv (LFunction χ) s / LFunction χ s
          - ∑ᶠ (w : ℂ) (_ : w ∈ {w | ‖w - (2 + ↑t * I)‖ ≤ 7 / 2 ∧ LFunction χ w = 0}),
            (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w))
          + ∑ᶠ (w : ℂ) (_ : w ∈ {w | ‖w - (2 + ↑t * I)‖ ≤ 7 / 2 ∧ LFunction χ w = 0}),
            (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := add_le_add hbd (hsum.trans (by linarith : _ ≤ 2 * (C₁ * Real.log (N * (|t| + 2)))))
    nlinarith

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Rewrite using `[norm_div, norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hu]`.
-/
private theorem norm_neg_mul_ofReal_cpow_div_eq (a s : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖-a * (u : ℂ) ^ s / s‖ = ‖a‖ * u ^ s.re / ‖s‖ := by
  rw [norm_div, norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hu]

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Establish `hc : Continuous fun t : ℝ => 1 / (|t| + 1 / 2)` using `continuous_const.div (continuous_abs.add continuous_const) (fun t => by positivity)`. Establish `h0 : ∫ t in (0:ℝ)..a, 1 / (|t| + 1 / 2) = Real.log (2 * a + 1)`. Rewrite using `[intervalIntegral.integral_congr (g := fun t => 1 / (t + 1 / 2)) (fun t ht => by`. Rewrite `ht` using `[Set.uIcc_of_le ha]`. Simplify using `only [abs_of_nonneg ht.1])]`.

Rewrite using `[intervalIntegral.integral_comp_add_right (fun t => 1 / t), integral_one_div_of_pos (by norm_num) (by linarith)]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hneg : ∫ t in -a..0, 1 / (|t| + 1 / 2) = ∫ t in (0:ℝ)..a, 1 / (|t| + 1 / 2)`.

Use `intervalIntegral.integral_comp_neg (a := 0) (b := a) (fun t : ℝ => 1 / (|t| + 1 / 2))` as an intermediate fact. Simplify using `only [abs_neg, neg_zero] at this`. Conclude with `this.symm`. Rewrite using `[← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), hneg, h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem integral_one_div_abs_add_half_eq_two_mul_log (a : ℝ) (ha : 0 ≤ a) :
    ∫ t in -a..a, 1 / (|t| + 1 / 2) = 2 * Real.log (2 * a + 1) := by
  have hc : Continuous fun t : ℝ => 1 / (|t| + 1 / 2) :=
    continuous_const.div (continuous_abs.add continuous_const) (fun t => by positivity)
  have h0 : ∫ t in (0:ℝ)..a, 1 / (|t| + 1 / 2) = Real.log (2 * a + 1) := by
    rw [intervalIntegral.integral_congr (g := fun t => 1 / (t + 1 / 2)) (fun t ht => by
      rw [Set.uIcc_of_le ha] at ht; simp only [abs_of_nonneg ht.1])]
    rw [intervalIntegral.integral_comp_add_right (fun t => 1 / t),
      integral_one_div_of_pos (by norm_num) (by linarith)]
    congr 1; field_simp; ring
  have hneg : ∫ t in -a..0, 1 / (|t| + 1 / 2) = ∫ t in (0:ℝ)..a, 1 / (|t| + 1 / 2) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := a) (fun t : ℝ => 1 / (|t| + 1 / 2))
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), hneg, h0]
  ring

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Take `⟨C₀, hC₀, H⟩` from `exists_norm_logDeriv_LFunction_neg_half_le_log_conductor`. Use `⟨4 * C₀, by positivity, fun N _ χ hχ u T' hu hT' => ?_⟩` and prove the remaining obligations. Establish `hN : (1 : ℝ) ≤ N` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)`. Establish `hL : 0 ≤ Real.log (N * (T' + 2))` using `Real.log_nonneg (by nlinarith)`. Establish `hg : Continuous fun t : ℝ => 2 * C₀ * Real.log (N * (T' + 2)) * (1 / (|t| + 1 / 2))` using `continuous_const.mul (continuous_const.div (continuous_abs.add continuous_const) (fun t => by positivity))`.

Use `(intervalIntegral.norm_integral_le_of_norm_le (by linarith) (Filter.Eventually.of_forall fun t ht => ?_) (hg.intervalIntegrable _ _)).trans ?_` and prove the remaining obligations. Establish `ht' : |t| ≤ T'` using `abs_le.mpr ⟨ht.1.le, ht.2⟩ set s : ℂ := ((-(1 / 2) : ℝ) : ℂ) + t * I with hs_def`. Establish `hre : s.re = -(1 / 2)` using `by simp [s]`. Establish `him : s.im = t` using `by simp [s]`. Rewrite using `[norm_neg_mul_ofReal_cpow_div_eq _ _ (by linarith : (0 : ℝ) < u), hre]`.

Establish `hp : u ^ (-(1 / 2) : ℝ) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hu (by norm_num)`. Establish `hp0 : 0 ≤ u ^ (-(1 / 2) : ℝ)` using `Real.rpow_nonneg (by linarith) _`. Establish `hA : ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ C₀ * Real.log (N * (T' + 2))`. Use `(H N χ hχ t).trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by nlinarith)) hC₀.le)` and prove the remaining obligations. Establish `hs1 : |t| ≤ ‖s‖` using `by rw [← him]; exact Complex.abs_im_le_norm s`.

Establish `hs2 : 1 / 2 ≤ ‖s‖`. Use `Complex.abs_re_le_norm s` as an intermediate fact. Rewrite `this` using `[hre]`. Evaluate the numerical expressions using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hs0 : 0 < ‖s‖` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Apply `div_le_div_of_nonneg_right _ hs0.le` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Use `_ ≤ C₀ * Real.log (N * (T' + 2)) / ((|t| + 1 / 2) / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)`.

Use `_ = 2 * C₀ * Real.log (N * (T' + 2)) * (1 / (|t| + 1 / 2)) := by`. Clear the denominators using the available nonvanishing facts. Rewrite using `[intervalIntegral.integral_const_mul, integral_one_div_abs_add_half_eq_two_mul_log T' hT']`. Apply `le_of_eq` to reduce the goal to its premises. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem norm_integral_logDeriv_LFunction_mul_cpow_div_neg_half_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ u T' : ℝ, 1 ≤ u → 0 ≤ T' →
      ‖∫ t in -T'..T', -(deriv (LFunction χ) (((-(1 / 2) : ℝ) : ℂ) + t * I) /
        LFunction χ (((-(1 / 2) : ℝ) : ℂ) + t * I)) * (u : ℂ) ^ (((-(1 / 2) : ℝ) : ℂ) + t * I) /
        (((-(1 / 2) : ℝ) : ℂ) + t * I)‖ ≤
        C * Real.log (N * (T' + 2)) * Real.log (2 * T' + 1) := by
  obtain ⟨C₀, hC₀, H⟩ := exists_norm_logDeriv_LFunction_neg_half_le_log_conductor
  refine ⟨4 * C₀, by positivity, fun N _ χ hχ u T' hu hT' => ?_⟩
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hL : 0 ≤ Real.log (N * (T' + 2)) := Real.log_nonneg (by nlinarith)
  have hg : Continuous fun t : ℝ => 2 * C₀ * Real.log (N * (T' + 2)) * (1 / (|t| + 1 / 2)) :=
    continuous_const.mul
      (continuous_const.div (continuous_abs.add continuous_const) (fun t => by positivity))
  refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    (Filter.Eventually.of_forall fun t ht => ?_) (hg.intervalIntegrable _ _)).trans ?_
  · have ht' : |t| ≤ T' := abs_le.mpr ⟨ht.1.le, ht.2⟩
    set s : ℂ := ((-(1 / 2) : ℝ) : ℂ) + t * I with hs_def
    have hre : s.re = -(1 / 2) := by simp [s]
    have him : s.im = t := by simp [s]
    rw [norm_neg_mul_ofReal_cpow_div_eq _ _ (by linarith : (0 : ℝ) < u), hre]
    have hp : u ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu (by norm_num)
    have hp0 : 0 ≤ u ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by linarith) _
    have hA : ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ C₀ * Real.log (N * (T' + 2)) := by
      refine (H N χ hχ t).trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity)
        (by nlinarith)) hC₀.le)
    have hs1 : |t| ≤ ‖s‖ := by rw [← him]; exact Complex.abs_im_le_norm s
    have hs2 : 1 / 2 ≤ ‖s‖ := by
      have := Complex.abs_re_le_norm s; rw [hre] at this; norm_num at this; linarith
    have hs0 : 0 < ‖s‖ := by linarith
    calc ‖deriv (LFunction χ) s / LFunction χ s‖ * u ^ (-(1 / 2) : ℝ) / ‖s‖
        ≤ C₀ * Real.log (N * (T' + 2)) / ‖s‖ := by
          apply div_le_div_of_nonneg_right _ hs0.le
          calc _ ≤ ‖deriv (LFunction χ) s / LFunction χ s‖ * 1 :=
                mul_le_mul_of_nonneg_left hp (norm_nonneg _)
            _ ≤ _ := by rw [mul_one]; exact hA
      _ ≤ C₀ * Real.log (N * (T' + 2)) / ((|t| + 1 / 2) / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ = 2 * C₀ * Real.log (N * (T' + 2)) * (1 / (|t| + 1 / 2)) := by
          field_simp
  · rw [intervalIntegral.integral_const_mul, integral_one_div_abs_add_half_eq_two_mul_log T' hT']
    apply le_of_eq; ring

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Establish `hl : 0 < Real.log u` using `Real.log_pos hu`. Rewrite using `[Real.rpow_add (by linarith), Real.rpow_one, Real.rpow_def_of_pos (by linarith), mul_one_div_cancel hl.ne']`. Use `Real.exp_one_lt_d9` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem rpow_one_add_inv_log_le_three_mul (u : ℝ) (hu : 1 < u) :
    u ^ (1 + 1 / Real.log u) ≤ 3 * u := by
  have hl : 0 < Real.log u := Real.log_pos hu
  rw [Real.rpow_add (by linarith), Real.rpow_one, Real.rpow_def_of_pos (by linarith),
    mul_one_div_cancel hl.ne']
  have := Real.exp_one_lt_d9
  nlinarith

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Establish `hπ : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `hk : (1 / (2 * (Real.pi : ℂ))) * (2 * (Real.pi : ℂ)) = 1` using `by field_simp`. Establish `hI : I ^ 2 = -1` using `Complex.I_sq`. Take the linear combination `(-I * (1 / (2 * (Real.pi : ℂ)))) * hid + ((1 / (2 * (Real.pi : ℂ))) * V - (1 / (2 * (Real.pi : ℂ))) * W - (1 / (2 * (Real.pi : ℂ))) * (2 * (Real.pi : ℂ)) * (M - S - E)) * hI + (M - S - E) * hk`.
-/
private theorem inv_two_pi_mul_sub_add_eq_of_contour_identity (H₁ H₂ V W M S E : ℂ)
    (hid : H₁ - H₂ + I * V - I * W = 2 * (Real.pi : ℂ) * I * (M - S - E)) :
    (1 / (2 * (Real.pi : ℂ))) * V - M + S =
      -E + (1 / (2 * (Real.pi : ℂ))) * (W + I * (H₁ - H₂)) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hk : (1 / (2 * (Real.pi : ℂ))) * (2 * (Real.pi : ℂ)) = 1 := by field_simp
  have hI : I ^ 2 = -1 := Complex.I_sq
  linear_combination (-I * (1 / (2 * (Real.pi : ℂ)))) * hid
    + ((1 / (2 * (Real.pi : ℂ))) * V - (1 / (2 * (Real.pi : ℂ))) * W
      - (1 / (2 * (Real.pi : ℂ))) * (2 * (Real.pi : ℂ)) * (M - S - E)) * hI
    + (M - S - E) * hk

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Establish `h1 : ‖(1 / (2 * (Real.pi : ℂ)))‖ ≤ 1`. Rewrite using `[norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, div_le_one (by positivity)]`. Combine the linear relations using `[Real.pi_gt_three]`. Establish `h2 : ‖W + I * (H₁ - H₂)‖ ≤ ‖W‖ + ‖H₁‖ + ‖H₂‖`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, Complex.norm_I, one_mul]`. Combine the linear relations using `[norm_sub_le H₁ H₂]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_neg, norm_mul]`. Use `mul_le_mul h1 h2 (norm_nonneg _) zero_le_one` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem norm_neg_add_inv_two_pi_mul_add_I_mul_sub_le (H₁ H₂ W E : ℂ) :
    ‖-E + (1 / (2 * (Real.pi : ℂ))) * (W + I * (H₁ - H₂))‖ ≤ ‖E‖ + ‖W‖ + ‖H₁‖ + ‖H₂‖ := by
  have h1 : ‖(1 / (2 * (Real.pi : ℂ)))‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  have h2 : ‖W + I * (H₁ - H₂)‖ ≤ ‖W‖ + ‖H₁‖ + ‖H₂‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    linarith [norm_sub_le H₁ H₂]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg, norm_mul]
  have := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
  linarith

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨C₁, hC₁, HZ⟩` from `_root_.GlobalTheory.GoodHeight.exists_height`. Take `⟨C₀, hC₀, HP⟩` from `_root_.GlobalTheory.LAtZero.logDeriv_LFunction_near_zero`. Take `⟨C₂, hC₂, HV⟩` from `norm_integral_logDeriv_LFunction_mul_cpow_div_neg_half_le`. Use `⟨1 + C₀ + 4 * C₂ + 18 * C₁, by positivity, fun N _ χ hχ u T hT hTu => ?_⟩` and prove the remaining obligations. Take `⟨T', hT1, hT2, hZ⟩` from `HZ N χ hχ T hT`.

Take `⟨m, h, hm, hh, hev, hh0⟩` from `HP N χ hχ`. Use `⟨T', hT1, hT2, ?_⟩` and prove the remaining obligations. Establish `hu1 : 1 < u` using `by linarith`. Establish `hlogu : 0 < Real.log u` using `Real.log_pos hu1`. Establish `hlog2 : (2 / 3 : ℝ) < Real.log 2` using `by linarith [Real.log_two_gt_d9]`.

Establish `hlogu2 : Real.log 2 ≤ Real.log u` using `Real.log_le_log (by norm_num) (by linarith)`. Establish `hcu : u ^ (1 + 1 / Real.log u) ≤ 3 * u` using `rpow_one_add_inv_log_le_three_mul u hu1`. Establish `hinv : 1 / Real.log u ≤ 3 / 2` using `by rw [div_le_iff₀ hlogu]; linarith`. Establish `hinv0 : 0 < 1 / Real.log u` using `by positivity`. Take `⟨c, hc⟩ : ∃ c : ℝ, c = 1 + 1 / Real.log u` from `⟨_, rfl⟩`.

Rewrite `hcu`, the goal using `[← hc]`. Establish `hc1 : 1 < c` using `by linarith`. Establish `hc3 : c ≤ 5 / 2` using `by linarith`. Establish `hid` using `_root_.GlobalTheory.ExplicitRect.residue_identity N χ hχ u c T' m h hu1 hc1 (by linarith) hh hev (fun s h1 h2 h3 => (hZ s h1 (by linarith) h3).1) (fun s hs => LFunction_ne_zero_of_re_eq_neg_half χ hχ hs)`. Rewrite using `[inv_two_pi_mul_sub_add_eq_of_contour_identity _ _ _ _ _ _ _ hid]`.

Use `(norm_neg_add_inv_two_pi_mul_add_I_mul_sub_le _ _ _ _).trans ?_` and prove the remaining obligations. Establish `hN : (1 : ℝ) ≤ N` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)`. Establish `hP4 : 4 ≤ (N : ℝ) * u * T` using `by nlinarith [mul_le_mul hN hTu (by linarith) (by linarith)]`. Establish `hlogP : 0 ≤ Real.log (N * u * T)` using `Real.log_nonneg (by linarith)`. Establish `hP2 : Real.log (((N : ℝ) * u * T) ^ 2) = 2 * Real.log (N * u * T)`.

Rewrite using `[Real.log_pow]`. Evaluate the numerical expressions. Establish `hNuT : (N : ℝ) * u * T * (N * u * T) ≥ 4 * (N * u * T)` using `by nlinarith`. Establish `hNT : (N : ℝ) * T ≤ N * u * T` using `by nlinarith`. Establish `hNT2 : 2 * ((N : ℝ) * T) ≤ N * u * T`.

Use polynomial arithmetic with `[mul_nonneg (by positivity : (0 : ℝ) ≤ N * T) (by linarith : (0 : ℝ) ≤ u - 2)]`. Establish `hsq : 4 * ((N : ℝ) * u * T) ≤ ((N : ℝ) * u * T) ^ 2` using `by nlinarith`. Establish `hS0 : 0 ≤ ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖` using `finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity`. Establish `hlogNu : Real.log u ≤ Real.log (N * u)` using `Real.log_le_log (by linarith) (by nlinarith)`. Establish `hlog2N : Real.log (2 * N) ≤ Real.log (N * u)` using `Real.log_le_log (by positivity) (by nlinarith)`.

Establish `hE : ‖(m : ℂ) * ((Real.log u : ℝ) : ℂ) + h 0‖ ≤ Real.log u + ‖h 0‖`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogu]`. Establish `: (m : ℝ) ≤ 1` using `by exact_mod_cast hm`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hW` using `HV N χ hχ u T' hu1.le (by linarith)`. Establish `hW1 : Real.log (N * (T' + 2)) ≤ 2 * Real.log (N * u * T)`. Rewrite using `[← hP2]; exact Real.log_le_log (by nlinarith) (by nlinarith)`. Establish `hW2 : Real.log (2 * T' + 1) ≤ 2 * Real.log (N * u * T)`. Rewrite using `[← hP2]; exact Real.log_le_log (by linarith) (by nlinarith)`.

Establish `hW0 : 0 ≤ Real.log (2 * T' + 1)` using `Real.log_nonneg (by linarith)`. Establish `hW10 : 0 ≤ Real.log (N * (T' + 2))` using `Real.log_nonneg (by nlinarith)`. Establish `hX : Real.log (N * u * T) ^ 2 ≤ u * Real.log (N * u * T) ^ 2 / T`. Rewrite using `[le_div_iff₀ (by linarith)]`. Use `mul_le_mul_of_nonneg_left hTu (sq_nonneg (Real.log (N * u * T)))` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogNT : 0 ≤ Real.log (N * T)` using `Real.log_nonneg (by nlinarith)`. Establish `hlogNT' : Real.log (N * T) ≤ Real.log (N * u * T)` using `Real.log_le_log (by positivity) hNT`. Establish `hH : ∀ y : ℝ, |y| = T' → ‖∫ x in -(1 / 2)..c, -(deriv (LFunction χ) (↑x + ↑y * I) / LFunction χ (↑x + ↑y * I)) * (u : ℂ) ^ (↑x + ↑y * I) / (↑x + ↑y * I)‖ ≤ 9 * C₁ * (u * Real.log (N * u * T) ^ 2 / T)`. Introduce `y hy`.

Use `(intervalIntegral.norm_integral_le_of_norm_le_const (C := C₁ * Real.log (N * T) ^ 2 * (3 * u) / T) fun x hx => ?_).trans ?_` and prove the remaining obligations. Rewrite using `[Set.uIoc_of_le (by linarith)] at hx set s : ℂ := ↑x + ↑y * I with hs_def`. Establish `hre : s.re = x` using `by simp [s]`. Establish `him : s.im = y` using `by simp [s]`. Rewrite using `[norm_neg_mul_ofReal_cpow_div_eq _ _ (by linarith : (0 : ℝ) < u), hre]`.

Establish `hA` using `(hZ s (by rw [hre]; linarith [hx.1]) (by rw [hre]; linarith [hx.2]) (by rw [him, hy])).2`. Establish `hp : u ^ x ≤ 3 * u` using `(Real.rpow_le_rpow_of_exponent_le hu1.le hx.2).trans hcu`. Establish `hs : T ≤ ‖s‖`. Use `Complex.abs_im_le_norm s` as an intermediate fact. Rewrite `this` using `[him, hy]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp0 : 0 ≤ u ^ x` using `Real.rpow_nonneg (by linarith) _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[abs_of_pos (by linarith : (0 : ℝ) < c - -(1 / 2))]`. Establish `h1 : C₁ * Real.log (N * T) ^ 2 ≤ C₁ * Real.log (N * u * T) ^ 2` using `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogNT hlogNT' 2) hC₁.le`.

Establish `hq : 0 ≤ 3 * u / T` using `div_nonneg (by linarith) (by linarith)`. Combine the equalities or inequalities in the displayed calculation. Establish `hH1` using `hH (-T') (by rw [abs_neg, abs_of_nonneg (by linarith)])`. Establish `hH2` using `hH T' (abs_of_nonneg (by linarith))`. Simplify using `only [Complex.ofReal_neg, neg_mul (T' : ℂ) I, ← sub_eq_add_neg] at hH1`.

Establish `hXn : 0 ≤ u * Real.log (N * u * T) ^ 2 / T` using `by positivity`. Establish `hWb : C₂ * Real.log (N * (T' + 2)) * Real.log (2 * T' + 1) ≤ 4 * C₂ * (u * Real.log (N * u * T) ^ 2 / T)`. Use `mul_le_mul hW1 hW2 hW0 (by linarith)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hLg : 0 ≤ Real.log (N * u)` using `hlogu.le.trans hlogNu`.

Establish `key` using `add_le_add (add_le_add (add_le_add (hE.trans (add_le_add le_rfl hh0)) (hW.trans hWb)) hH1) hH2`. Use `key.trans ?_` and prove the remaining obligations. Combine the linear relations using `[mul_nonneg hC₀.le hXn, mul_nonneg hC₁.le hS0, mul_nonneg hC₂.le hS0, mul_nonneg hC₁.le hLg, mul_nonneg hC₂.le hLg, mul_nonneg hC₀.le hLg, mul_le_mul_of_nonneg_left hlog2N hC₀.le]`.
-/
theorem _root_.GlobalTheory.PerronShift.perron_shift : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧ ‖(1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ in (-T')..T', (-(deriv (LFunction χ) (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / LFunction χ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)) * (u : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I))) - (if N = 1 then (u : ℂ) else 0) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) := by
  obtain ⟨C₁, hC₁, HZ⟩ := _root_.GlobalTheory.GoodHeight.exists_height
  obtain ⟨C₀, hC₀, HP⟩ := _root_.GlobalTheory.LAtZero.logDeriv_LFunction_near_zero
  obtain ⟨C₂, hC₂, HV⟩ := norm_integral_logDeriv_LFunction_mul_cpow_div_neg_half_le
  refine ⟨1 + C₀ + 4 * C₂ + 18 * C₁, by positivity, fun N _ χ hχ u T hT hTu => ?_⟩
  obtain ⟨T', hT1, hT2, hZ⟩ := HZ N χ hχ T hT
  obtain ⟨m, h, hm, hh, hev, hh0⟩ := HP N χ hχ
  refine ⟨T', hT1, hT2, ?_⟩
  have hu1 : 1 < u := by linarith
  have hlogu : 0 < Real.log u := Real.log_pos hu1
  have hlog2 : (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogu2 : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) (by linarith)
  have hcu : u ^ (1 + 1 / Real.log u) ≤ 3 * u := rpow_one_add_inv_log_le_three_mul u hu1
  have hinv : 1 / Real.log u ≤ 3 / 2 := by rw [div_le_iff₀ hlogu]; linarith
  have hinv0 : 0 < 1 / Real.log u := by positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 + 1 / Real.log u := ⟨_, rfl⟩
  rw [← hc] at hcu ⊢
  have hc1 : 1 < c := by linarith
  have hc3 : c ≤ 5 / 2 := by linarith
  have hid := _root_.GlobalTheory.ExplicitRect.residue_identity N χ hχ u c T' m h hu1 hc1
    (by linarith) hh hev (fun s h1 h2 h3 => (hZ s h1 (by linarith) h3).1)
    (fun s hs => LFunction_ne_zero_of_re_eq_neg_half χ hχ hs)
  rw [inv_two_pi_mul_sub_add_eq_of_contour_identity _ _ _ _ _ _ _ hid]
  refine (norm_neg_add_inv_two_pi_mul_add_I_mul_sub_le _ _ _ _).trans ?_
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hP4 : 4 ≤ (N : ℝ) * u * T := by nlinarith [mul_le_mul hN hTu (by linarith) (by linarith)]
  have hlogP : 0 ≤ Real.log (N * u * T) := Real.log_nonneg (by linarith)
  have hP2 : Real.log (((N : ℝ) * u * T) ^ 2) = 2 * Real.log (N * u * T) := by
    rw [Real.log_pow]; norm_num
  have hNuT : (N : ℝ) * u * T * (N * u * T) ≥ 4 * (N * u * T) := by nlinarith
  have hNT : (N : ℝ) * T ≤ N * u * T := by nlinarith
  have hNT2 : 2 * ((N : ℝ) * T) ≤ N * u * T := by
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ N * T) (by linarith : (0 : ℝ) ≤ u - 2)]
  have hsq : 4 * ((N : ℝ) * u * T) ≤ ((N : ℝ) * u * T) ^ 2 := by nlinarith

  have hS0 : 0 ≤ ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖ :=
    finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  have hlogNu : Real.log u ≤ Real.log (N * u) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hlog2N : Real.log (2 * N) ≤ Real.log (N * u) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hE : ‖(m : ℂ) * ((Real.log u : ℝ) : ℂ) + h 0‖ ≤ Real.log u + ‖h 0‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogu]
    have : (m : ℝ) ≤ 1 := by exact_mod_cast hm
    nlinarith

  have hW := HV N χ hχ u T' hu1.le (by linarith)
  have hW1 : Real.log (N * (T' + 2)) ≤ 2 * Real.log (N * u * T) := by
    rw [← hP2]; exact Real.log_le_log (by nlinarith) (by nlinarith)
  have hW2 : Real.log (2 * T' + 1) ≤ 2 * Real.log (N * u * T) := by
    rw [← hP2]; exact Real.log_le_log (by linarith) (by nlinarith)
  have hW0 : 0 ≤ Real.log (2 * T' + 1) := Real.log_nonneg (by linarith)
  have hW10 : 0 ≤ Real.log (N * (T' + 2)) := Real.log_nonneg (by nlinarith)
  have hX : Real.log (N * u * T) ^ 2 ≤ u * Real.log (N * u * T) ^ 2 / T := by
    rw [le_div_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hTu (sq_nonneg (Real.log (N * u * T)))
    linarith

  have hlogNT : 0 ≤ Real.log (N * T) := Real.log_nonneg (by nlinarith)
  have hlogNT' : Real.log (N * T) ≤ Real.log (N * u * T) := Real.log_le_log (by positivity) hNT
  have hH : ∀ y : ℝ, |y| = T' → ‖∫ x in -(1 / 2)..c, -(deriv (LFunction χ) (↑x + ↑y * I) /
      LFunction χ (↑x + ↑y * I)) * (u : ℂ) ^ (↑x + ↑y * I) / (↑x + ↑y * I)‖ ≤
      9 * C₁ * (u * Real.log (N * u * T) ^ 2 / T) := by
    intro y hy
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := C₁ * Real.log (N * T) ^ 2 * (3 * u) / T) fun x hx => ?_).trans ?_
    · rw [Set.uIoc_of_le (by linarith)] at hx
      set s : ℂ := ↑x + ↑y * I with hs_def
      have hre : s.re = x := by simp [s]
      have him : s.im = y := by simp [s]
      rw [norm_neg_mul_ofReal_cpow_div_eq _ _ (by linarith : (0 : ℝ) < u), hre]
      have hA := (hZ s (by rw [hre]; linarith [hx.1]) (by rw [hre]; linarith [hx.2])
        (by rw [him, hy])).2
      have hp : u ^ x ≤ 3 * u := (Real.rpow_le_rpow_of_exponent_le hu1.le hx.2).trans hcu
      have hs : T ≤ ‖s‖ := by
        have := Complex.abs_im_le_norm s; rw [him, hy] at this; linarith
      have hp0 : 0 ≤ u ^ x := Real.rpow_nonneg (by linarith) _
      calc ‖deriv (LFunction χ) s / LFunction χ s‖ * u ^ x / ‖s‖
          ≤ C₁ * Real.log (N * T) ^ 2 * (3 * u) / ‖s‖ :=
            div_le_div_of_nonneg_right (mul_le_mul hA hp hp0 (by positivity)) (by positivity)
        _ ≤ C₁ * Real.log (N * T) ^ 2 * (3 * u) / T :=
            div_le_div_of_nonneg_left (by positivity) (by linarith) hs
    · rw [abs_of_pos (by linarith : (0 : ℝ) < c - -(1 / 2))]
      have h1 : C₁ * Real.log (N * T) ^ 2 ≤ C₁ * Real.log (N * u * T) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogNT hlogNT' 2) hC₁.le
      have hq : 0 ≤ 3 * u / T := div_nonneg (by linarith) (by linarith)
      calc C₁ * Real.log (N * T) ^ 2 * (3 * u) / T * (c - -(1 / 2))
          = (C₁ * Real.log (N * T) ^ 2) * (3 * u / T) * (c - -(1 / 2)) := by ring
        _ ≤ (C₁ * Real.log (N * u * T) ^ 2) * (3 * u / T) * 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 hq) (by linarith) (by linarith)
            (mul_nonneg (mul_nonneg hC₁.le (sq_nonneg _)) hq)
        _ = 9 * C₁ * (u * Real.log (N * u * T) ^ 2 / T) := by ring
  have hH1 := hH (-T') (by rw [abs_neg, abs_of_nonneg (by linarith)])
  have hH2 := hH T' (abs_of_nonneg (by linarith))
  simp only [Complex.ofReal_neg, neg_mul (T' : ℂ) I, ← sub_eq_add_neg] at hH1
  have hXn : 0 ≤ u * Real.log (N * u * T) ^ 2 / T := by positivity
  have hWb : C₂ * Real.log (N * (T' + 2)) * Real.log (2 * T' + 1) ≤
      4 * C₂ * (u * Real.log (N * u * T) ^ 2 / T) := by
    have := mul_le_mul hW1 hW2 hW0 (by linarith)
    nlinarith
  have hLg : 0 ≤ Real.log (N * u) := hlogu.le.trans hlogNu
  have key := add_le_add (add_le_add (add_le_add (hE.trans (add_le_add le_rfl hh0))
    (hW.trans hWb)) hH1) hH2
  refine key.trans ?_
  linarith [mul_nonneg hC₀.le hXn, mul_nonneg hC₁.le hS0, mul_nonneg hC₂.le hS0,
    mul_nonneg hC₁.le hLg, mul_nonneg hC₂.le hLg, mul_nonneg hC₀.le hLg,
    mul_le_mul_of_nonneg_left hlog2N hC₀.le]

end GlobalTheory.PerronShift
