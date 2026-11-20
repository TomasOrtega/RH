import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DHFinish2Of
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHHyperC

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

namespace Hyp

/- English proof (translation)
Establish `ha0 : 0 < a` using `by linarith`. Establish `hb0 : 0 < b` using `by linarith`. Establish `hL : 0 ≤ Real.log a` using `Real.log_nonneg ha`. Establish `hsa : 0 < √a` using `Real.sqrt_pos.2 ha0`. Establish `hsb : 0 < √b` using `Real.sqrt_pos.2 hb0`.

Use `set s := √b / √a with hs`. Establish `hs1 : 1 ≤ s`. Rewrite using `[hs, le_div_iff₀ hsa, one_mul]`. Conclude with `Real.sqrt_le_sqrt hab`. Establish `hs0 : 0 < s` using `by linarith`.

Establish `hsb' : √b = √a * s`. Rewrite using `[hs]`. Clear the denominators using the available nonvanishing facts. Establish `hb' : b = a * s ^ 2`. Rewrite using `[hs, div_pow, Real.sq_sqrt hb0.le, Real.sq_sqrt ha0.le]`.

Clear the denominators using the available nonvanishing facts. Establish `hlogb : Real.log b = Real.log a + 2 * Real.log s`. Rewrite using `[hb', Real.log_mul ha0.ne' (by positivity), Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hlogs : Real.log s ≤ s - 1` using `Real.log_le_sub_one_of_pos hs0`. Rewrite using `[hsb', hlogb, div_le_iff₀ (by positivity)]`. Establish `e : 2 * ((Real.log a + 1) / √a) * (√a * s) = 2 * (Real.log a + 1) * s`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hs1 hL]`.
-/
theorem g_mono (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (Real.log b + 1) / √b ≤ 2 * ((Real.log a + 1) / √a) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hL : 0 ≤ Real.log a := Real.log_nonneg ha
  have hsa : 0 < √a := Real.sqrt_pos.2 ha0
  have hsb : 0 < √b := Real.sqrt_pos.2 hb0
  set s := √b / √a with hs
  have hs1 : 1 ≤ s := by
    rw [hs, le_div_iff₀ hsa, one_mul]
    exact Real.sqrt_le_sqrt hab
  have hs0 : 0 < s := by linarith
  have hsb' : √b = √a * s := by
    rw [hs]
    field_simp
  have hb' : b = a * s ^ 2 := by
    rw [hs, div_pow, Real.sq_sqrt hb0.le, Real.sq_sqrt ha0.le]
    field_simp
  have hlogb : Real.log b = Real.log a + 2 * Real.log s := by
    rw [hb', Real.log_mul ha0.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
  rw [hsb', hlogb, div_le_iff₀ (by positivity)]
  have e : 2 * ((Real.log a + 1) / √a) * (√a * s) = 2 * (Real.log a + 1) * s := by
    field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hs1 hL]

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/- English proof (translation)
Use `set L := DirichletCharacter.LFunction χ 1`. Use `set U₀ := Nat.sqrt N₀ with hU₀`. Use `set U₁ := Nat.sqrt N₁ with hU₁`. Use `set B := (q : ℝ) + 1 with hBdef`. Establish `hB : 1 ≤ B` using `by have := Nat.cast_nonneg (α := ℝ) q; linarith`.

Establish `hN0r : (1 : ℝ) ≤ N₀` using `by exact_mod_cast h0`. Establish `hN01r : (N₀ : ℝ) ≤ N₁` using `by exact_mod_cast h01`. Establish `hU01 : U₀ ≤ U₁` using `Nat.sqrt_le_sqrt h01`. Establish `hU0 : 1 ≤ U₀` using `Nat.sqrt_pos.mpr (by omega)`. Establish `hR1` using `cF_approx χ hχ N₁ (by omega)`.

Establish `hR0` using `cF_approx χ hχ N₀ h0`. Establish `hT` using `cT_diff χ hχ U₀ U₁ hU0 hU01`. Use `set R₁ := cF χ N₁ - (((Real.log N₁ + Real.eulerMascheroniConstant : ℝ) : ℂ) * L - cT χ U₁)`. Use `set R₀ := cF χ N₀ - (((Real.log N₀ + Real.eulerMascheroniConstant : ℝ) : ℂ) * L - cT χ U₀)`. Use `set t := Real.log N₁ - Real.log N₀ with ht`.

Establish `ht0 : 0 ≤ t`. Use `Real.log_le_log (by linarith) hN01r; linarith` as an intermediate fact. Use `set W := -(cT χ U₁ - cT χ U₀) + R₁ - R₀ with hW`. Establish `eD : cF χ N₁ - cF χ N₀ = (t : ℂ) * L + W`. Simplify using `only [hW, R₁, R₀, ht]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eD, Complex.add_re, Complex.re_ofReal_mul]`. Establish `hLre : L.re ≤ ‖L‖` using `Complex.re_le_norm L`. Establish `hWre : W.re ≤ ‖W‖` using `Complex.re_le_norm W`.

Establish `hWn : ‖W‖ ≤ ‖cT χ U₁ - cT χ U₀‖ + ‖R₁‖ + ‖R₀‖`. Rewrite using `[hW]`. Combine the equalities or inequalities in the displayed calculation. Establish `hg` using `g_mono (N₀ : ℝ) (N₁ : ℝ) hN0r hN01r`. Use `set g₀ := (Real.log N₀ + 1) / √(N₀ : ℝ)`.

Establish `hg0 : 0 ≤ g₀` using `div_nonneg (by linarith [Real.log_natCast_nonneg N₀]) (Real.sqrt_nonneg _)`. Establish `hR1' : ‖R₁‖ ≤ 52 * B * g₀`. Establish `e : 26 * B * (Real.log N₁ + 1) / √(N₁ : ℝ) = 26 * B * ((Real.log N₁ + 1) / √(N₁ : ℝ))` using `by ring`. Rewrite `hR1` using `[e]`. Use `mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 26 * B)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `hR0' : ‖R₀‖ ≤ 26 * B * g₀`. Establish `e : 26 * B * (Real.log N₀ + 1) / √(N₀ : ℝ) = 26 * B * g₀` using `by ring`. Rewrite `hR0` using `[e]`. Conclude with `hR0`.

Establish `hT' : ‖cT χ U₁ - cT χ U₀‖ ≤ 8 * B * g₀`. Establish `hUr : (1 : ℝ) ≤ U₀` using `by exact_mod_cast hU0`. Establish `hUN : U₀ ≤ N₀` using `Nat.sqrt_le_self N₀`. Establish `hUNr : (U₀ : ℝ) ≤ N₀` using `by exact_mod_cast hUN`. Establish `hlt : N₀ < (U₀ + 1) * (U₀ + 1)` using `Nat.lt_succ_sqrt N₀`.

Establish `hltr : (N₀ : ℝ) < ((U₀ : ℝ) + 1) * ((U₀ : ℝ) + 1)` using `by exact_mod_cast hlt`. Establish `hsU : √(N₀ : ℝ) < (U₀ : ℝ) + 1`. Use `Real.sqrt_lt_sqrt (Nat.cast_nonneg N₀) hltr` as an intermediate fact. Rewrite `this` using `[Real.sqrt_mul_self (by linarith)]`. Then use the resulting hypothesis. Establish `hs0 : 0 < √(N₀ : ℝ)` using `Real.sqrt_pos.mpr (by linarith)`.

Establish `hlog : Real.log ((U₀ : ℝ) + 1) ≤ 1 + Real.log N₀`. Establish `h1 : Real.log ((U₀ : ℝ) + 1) ≤ Real.log (2 * N₀)` using `Real.log_le_log (by linarith) (by linarith)`. Rewrite `h1` using `[Real.log_mul (by norm_num) (by linarith)]`. Use `Real.log_two_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hln : 0 ≤ Real.log N₀` using `Real.log_natCast_nonneg N₀`. Establish `h2 : (1 + Real.log ((U₀ : ℝ) + 1)) / ((U₀ : ℝ) + 1) ≤ 2 * g₀`. Establish `e : 2 * g₀ = 2 * (Real.log N₀ + 1) / √(N₀ : ℝ)` using `by ring`. Rewrite using `[e, div_le_div_iff₀ (by linarith) hs0]`. Use the polynomial consequences of the given equalities and inequalities.

Use `mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * B)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLt : t * L.re ≤ ‖L‖ * t` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem diff_bound (hχ : χ ≠ 1) (N₀ N₁ : ℕ) (h0 : 1 ≤ N₀) (h01 : N₀ ≤ N₁) :
    (cF χ N₁ - cF χ N₀).re ≤ ‖DirichletCharacter.LFunction χ 1‖ * (Real.log N₁ - Real.log N₀) +
      86 * ((q : ℝ) + 1) * ((Real.log N₀ + 1) / √(N₀ : ℝ)) := by
  set L := DirichletCharacter.LFunction χ 1
  set U₀ := Nat.sqrt N₀ with hU₀
  set U₁ := Nat.sqrt N₁ with hU₁
  set B := (q : ℝ) + 1 with hBdef
  have hB : 1 ≤ B := by have := Nat.cast_nonneg (α := ℝ) q; linarith
  have hN0r : (1 : ℝ) ≤ N₀ := by exact_mod_cast h0
  have hN01r : (N₀ : ℝ) ≤ N₁ := by exact_mod_cast h01
  have hU01 : U₀ ≤ U₁ := Nat.sqrt_le_sqrt h01
  have hU0 : 1 ≤ U₀ := Nat.sqrt_pos.mpr (by omega)
  have hR1 := cF_approx χ hχ N₁ (by omega)
  have hR0 := cF_approx χ hχ N₀ h0
  have hT := cT_diff χ hχ U₀ U₁ hU0 hU01
  set R₁ := cF χ N₁ - (((Real.log N₁ + Real.eulerMascheroniConstant : ℝ) : ℂ) * L - cT χ U₁)
  set R₀ := cF χ N₀ - (((Real.log N₀ + Real.eulerMascheroniConstant : ℝ) : ℂ) * L - cT χ U₀)
  set t := Real.log N₁ - Real.log N₀ with ht
  have ht0 : 0 ≤ t := by
    have := Real.log_le_log (by linarith) hN01r; linarith
  set W := -(cT χ U₁ - cT χ U₀) + R₁ - R₀ with hW
  have eD : cF χ N₁ - cF χ N₀ = (t : ℂ) * L + W := by
    simp only [hW, R₁, R₀, ht]; push_cast; ring
  rw [eD, Complex.add_re, Complex.re_ofReal_mul]
  have hLre : L.re ≤ ‖L‖ := Complex.re_le_norm L
  have hWre : W.re ≤ ‖W‖ := Complex.re_le_norm W
  have hWn : ‖W‖ ≤ ‖cT χ U₁ - cT χ U₀‖ + ‖R₁‖ + ‖R₀‖ := by
    rw [hW]
    calc ‖-(cT χ U₁ - cT χ U₀) + R₁ - R₀‖ ≤ ‖-(cT χ U₁ - cT χ U₀) + R₁‖ + ‖R₀‖ := norm_sub_le _ _
      _ ≤ ‖-(cT χ U₁ - cT χ U₀)‖ + ‖R₁‖ + ‖R₀‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by rw [norm_neg]
  have hg := g_mono (N₀ : ℝ) (N₁ : ℝ) hN0r hN01r
  set g₀ := (Real.log N₀ + 1) / √(N₀ : ℝ)
  have hg0 : 0 ≤ g₀ := div_nonneg (by linarith [Real.log_natCast_nonneg N₀]) (Real.sqrt_nonneg _)
  have hR1' : ‖R₁‖ ≤ 52 * B * g₀ := by
    have e : 26 * B * (Real.log N₁ + 1) / √(N₁ : ℝ) = 26 * B * ((Real.log N₁ + 1) / √(N₁ : ℝ)) := by ring
    rw [e] at hR1
    have := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 26 * B)
    nlinarith
  have hR0' : ‖R₀‖ ≤ 26 * B * g₀ := by
    have e : 26 * B * (Real.log N₀ + 1) / √(N₀ : ℝ) = 26 * B * g₀ := by ring
    rw [e] at hR0; exact hR0
  have hT' : ‖cT χ U₁ - cT χ U₀‖ ≤ 8 * B * g₀ := by
    have hUr : (1 : ℝ) ≤ U₀ := by exact_mod_cast hU0
    have hUN : U₀ ≤ N₀ := Nat.sqrt_le_self N₀
    have hUNr : (U₀ : ℝ) ≤ N₀ := by exact_mod_cast hUN
    have hlt : N₀ < (U₀ + 1) * (U₀ + 1) := Nat.lt_succ_sqrt N₀
    have hltr : (N₀ : ℝ) < ((U₀ : ℝ) + 1) * ((U₀ : ℝ) + 1) := by exact_mod_cast hlt
    have hsU : √(N₀ : ℝ) < (U₀ : ℝ) + 1 := by
      have := Real.sqrt_lt_sqrt (Nat.cast_nonneg N₀) hltr
      rwa [Real.sqrt_mul_self (by linarith)] at this
    have hs0 : 0 < √(N₀ : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hlog : Real.log ((U₀ : ℝ) + 1) ≤ 1 + Real.log N₀ := by
      have h1 : Real.log ((U₀ : ℝ) + 1) ≤ Real.log (2 * N₀) := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) (by linarith)] at h1
      have := Real.log_two_lt_d9
      linarith
    have hln : 0 ≤ Real.log N₀ := Real.log_natCast_nonneg N₀
    have h2 : (1 + Real.log ((U₀ : ℝ) + 1)) / ((U₀ : ℝ) + 1) ≤ 2 * g₀ := by
      have e : 2 * g₀ = 2 * (Real.log N₀ + 1) / √(N₀ : ℝ) := by ring
      rw [e, div_le_div_iff₀ (by linarith) hs0]
      nlinarith
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * B)
    linarith
  have hLt : t * L.re ≤ ‖L‖ * t := by nlinarith
  linarith

end Hyp

/- English proof (translation)
Use `⟨400, by norm_num, ?_⟩` and prove the remaining obligations. Introduce `M _ χ₁ y x hM _ hne hy hyx`. Establish `e : ∀ N₀ N₁ : ℕ, N₀ ≤ N₁ → ∑ n ∈ Finset.Ioc N₀ N₁, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) = (Hyp.cF χ₁ N₁ - Hyp.cF χ₁ N₀).re`. Introduce `N₀ N₁ h`. Rewrite using `[Hyp.cF, Hyp.cF, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le N₀) h, add_sub_cancel_left, Complex.re_sum]`.

Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.div_natCast_re]`. Establish `h0 : 1 ≤ ⌊y⌋₊` using `Nat.le_floor (by simpa using hy)`. Establish `h01 : ⌊y⌋₊ ≤ ⌊x⌋₊` using `Nat.floor_mono hyx`. Rewrite using `[e _ _ h01]`.

Establish `hd` using `Hyp.diff_bound χ₁ hne ⌊y⌋₊ ⌊x⌋₊ h0 h01`. Use `set N₀ := ⌊y⌋₊ with hN₀`. Use `set N₁ := ⌊x⌋₊ with hN₁`. Use `set L := DirichletCharacter.LFunction χ₁ 1`. Use `set B := (M : ℝ) + 1 with hBdef`.

Establish `hMr : (3 : ℝ) ≤ M` using `by exact_mod_cast hM`. Establish `hN0y : (N₀ : ℝ) ≤ y` using `Nat.floor_le (by linarith)`. Establish `hyN0 : y < N₀ + 1` using `Nat.lt_floor_add_one y`. Establish `hN1x : (N₁ : ℝ) ≤ x` using `Nat.floor_le (by linarith)`. Establish `hN0r : (1 : ℝ) ≤ N₀` using `by exact_mod_cast h0`.

Establish `hN01r : (N₀ : ℝ) ≤ N₁` using `by exact_mod_cast h01`. Establish `hly : 0 ≤ Real.log y` using `Real.log_nonneg hy`. Establish `hlog1 : Real.log N₁ ≤ Real.log x` using `Real.log_le_log (by linarith) hN1x`. Establish `hlog0 : Real.log y - Real.log N₀ ≤ 2 / y`. Rewrite using `[← Real.log_div (by linarith) (by linarith)]`.

Establish `h` using `Real.log_le_sub_one_of_pos (show 0 < y / N₀ by positivity)`. Establish `h' : y / N₀ - 1 ≤ 2 / y`. Rewrite using `[div_sub_one (by linarith), div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hxy : Real.log (x / y) = Real.log x - Real.log y` using `Real.log_div (by linarith) (by linarith)`.

Establish `hLB : ‖L‖ ≤ 5 * B`. Establish `h` using `Hyp.cS_approx χ₁ hne 1 le_rfl`. Establish `h1 : Hyp.cS χ₁ 1 = 1` using `by simp [Hyp.cS]`. Rewrite `h` using `[h1]`. Use `norm_sub_norm_le L 1` as an intermediate fact.

Simplify using `only [norm_one, Nat.cast_one, div_one] at h this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsy : 0 < √y` using `Real.sqrt_pos.mpr (by linarith)`. Establish `hs0 : 0 < √(N₀ : ℝ)` using `Real.sqrt_pos.mpr (by linarith)`. Establish `hsyN : √y ≤ 2 * √(N₀ : ℝ)`.

Establish `h4 : (2 * √(N₀ : ℝ)) * (2 * √(N₀ : ℝ)) = 4 * N₀`. Use `Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) N₀)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Use `Real.sqrt_le_sqrt (show y ≤ (2 * √(N₀ : ℝ)) * (2 * √(N₀ : ℝ)) by rw [h4]; linarith)` as an intermediate fact. Rewrite `this` using `[Real.sqrt_mul_self (by positivity)]`. Then use the resulting hypothesis.

Establish `hlN0 : Real.log N₀ ≤ Real.log y` using `Real.log_le_log (by linarith) hN0y`. Use `set Y := (Real.log y + 1) / √y with hY`. Establish `hY0 : 0 ≤ Y` using `by positivity`. Establish `hg0 : (Real.log N₀ + 1) / √(N₀ : ℝ) ≤ 2 * Y`. Establish `e2 : 2 * Y = 2 * (Real.log y + 1) / √y` using `by ring`.

Rewrite using `[e2, div_le_div_iff₀ hs0 hsy]`. Establish `hln : 0 ≤ Real.log N₀` using `Real.log_natCast_nonneg N₀`. Use the polynomial consequences of the given equalities and inequalities. Establish `hyY : 2 / y ≤ 2 * Y`. Establish `hsyy : √y ≤ y`.

Use `Real.sqrt_le_sqrt (show y ≤ y * y by nlinarith)` as an intermediate fact. Rewrite `this` using `[Real.sqrt_mul_self (by linarith)]`. Then use the resulting hypothesis. Establish `e2 : 2 * Y = 2 * (Real.log y + 1) / √y` using `by ring`. Rewrite using `[e2, div_le_div_iff₀ (by linarith) hsy]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hLn : 0 ≤ ‖L‖` using `norm_nonneg _`. Establish `i1 : ‖L‖ * (Real.log N₁ - Real.log N₀) ≤ ‖L‖ * Real.log (x / y) + ‖L‖ * (2 / y)`. Rewrite using `[hxy, ← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hLn`. Establish `i2 : ‖L‖ * (2 / y) ≤ 5 * B * (2 * Y)` using `mul_le_mul hLB hyY (by positivity) (by positivity)`. Establish `i3 : 86 * B * ((Real.log N₀ + 1) / √(N₀ : ℝ)) ≤ 86 * B * (2 * Y)` using `mul_le_mul_of_nonneg_left hg0 (by positivity)`.

Establish `e3 : 400 * (M : ℝ) * (Real.log y + 1) / √y = 400 * M * Y` using `by rw [hY]; ring`. Rewrite using `[e3]`. Establish `hB2 : B ≤ 2 * M` using `by rw [hBdef]; linarith`. Establish `i4 : 5 * B * (2 * Y) + 86 * B * (2 * Y) ≤ 400 * M * Y` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem deuring_heilbronn_hypergeometric : DHHyper := by
  refine ⟨400, by norm_num, ?_⟩
  intro M _ χ₁ y x hM _ hne hy hyx
  have e : ∀ N₀ N₁ : ℕ, N₀ ≤ N₁ → ∑ n ∈ Finset.Ioc N₀ N₁, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) =
      (Hyp.cF χ₁ N₁ - Hyp.cF χ₁ N₀).re := by
    intro N₀ N₁ h
    rw [Hyp.cF, Hyp.cF, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le N₀) h, add_sub_cancel_left,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.div_natCast_re]
  have h0 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy)
  have h01 : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hyx
  rw [e _ _ h01]
  have hd := Hyp.diff_bound χ₁ hne ⌊y⌋₊ ⌊x⌋₊ h0 h01
  set N₀ := ⌊y⌋₊ with hN₀
  set N₁ := ⌊x⌋₊ with hN₁
  set L := DirichletCharacter.LFunction χ₁ 1
  set B := (M : ℝ) + 1 with hBdef
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hN0y : (N₀ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyN0 : y < N₀ + 1 := Nat.lt_floor_add_one y
  have hN1x : (N₁ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hN0r : (1 : ℝ) ≤ N₀ := by exact_mod_cast h0
  have hN01r : (N₀ : ℝ) ≤ N₁ := by exact_mod_cast h01
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy

  have hlog1 : Real.log N₁ ≤ Real.log x := Real.log_le_log (by linarith) hN1x
  have hlog0 : Real.log y - Real.log N₀ ≤ 2 / y := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have h := Real.log_le_sub_one_of_pos (show 0 < y / N₀ by positivity)
    have h' : y / N₀ - 1 ≤ 2 / y := by
      rw [div_sub_one (by linarith), div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    linarith
  have hxy : Real.log (x / y) = Real.log x - Real.log y := Real.log_div (by linarith) (by linarith)

  have hLB : ‖L‖ ≤ 5 * B := by
    have h := Hyp.cS_approx χ₁ hne 1 le_rfl
    have h1 : Hyp.cS χ₁ 1 = 1 := by simp [Hyp.cS]
    rw [h1] at h
    have := norm_sub_norm_le L 1
    simp only [norm_one, Nat.cast_one, div_one] at h this
    linarith

  have hsy : 0 < √y := Real.sqrt_pos.mpr (by linarith)
  have hs0 : 0 < √(N₀ : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsyN : √y ≤ 2 * √(N₀ : ℝ) := by
    have h4 : (2 * √(N₀ : ℝ)) * (2 * √(N₀ : ℝ)) = 4 * N₀ := by
      have := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) N₀); nlinarith
    have := Real.sqrt_le_sqrt (show y ≤ (2 * √(N₀ : ℝ)) * (2 * √(N₀ : ℝ)) by rw [h4]; linarith)
    rwa [Real.sqrt_mul_self (by positivity)] at this
  have hlN0 : Real.log N₀ ≤ Real.log y := Real.log_le_log (by linarith) hN0y
  set Y := (Real.log y + 1) / √y with hY
  have hY0 : 0 ≤ Y := by positivity
  have hg0 : (Real.log N₀ + 1) / √(N₀ : ℝ) ≤ 2 * Y := by
    have e2 : 2 * Y = 2 * (Real.log y + 1) / √y := by ring
    rw [e2, div_le_div_iff₀ hs0 hsy]
    have hln : 0 ≤ Real.log N₀ := Real.log_natCast_nonneg N₀
    nlinarith
  have hyY : 2 / y ≤ 2 * Y := by
    have hsyy : √y ≤ y := by
      have := Real.sqrt_le_sqrt (show y ≤ y * y by nlinarith)
      rwa [Real.sqrt_mul_self (by linarith)] at this
    have e2 : 2 * Y = 2 * (Real.log y + 1) / √y := by ring
    rw [e2, div_le_div_iff₀ (by linarith) hsy]
    nlinarith
  have hLn : 0 ≤ ‖L‖ := norm_nonneg _
  have i1 : ‖L‖ * (Real.log N₁ - Real.log N₀) ≤ ‖L‖ * Real.log (x / y) + ‖L‖ * (2 / y) := by
    rw [hxy, ← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hLn
  have i2 : ‖L‖ * (2 / y) ≤ 5 * B * (2 * Y) := mul_le_mul hLB hyY (by positivity) (by positivity)
  have i3 : 86 * B * ((Real.log N₀ + 1) / √(N₀ : ℝ)) ≤ 86 * B * (2 * Y) :=
    mul_le_mul_of_nonneg_left hg0 (by positivity)
  have e3 : 400 * (M : ℝ) * (Real.log y + 1) / √y = 400 * M * Y := by rw [hY]; ring
  rw [e3]
  have hB2 : B ≤ 2 * M := by rw [hBdef]; linarith
  have i4 : 5 * B * (2 * Y) + 86 * B * (2 * Y) ≤ 400 * M * Y := by nlinarith
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
