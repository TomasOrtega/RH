import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TsumOneDivRpowLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOneSubConjMul
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableAtFractInt
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.ZetaLocal

/- English proof (translation)
Rewrite using `[riemannZeta_eq_inv_sub_mul hs, mul_inv_cancel_left₀ (sub_ne_zero.2 hs)]`.
-/
lemma zeta₁_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, mul_inv_cancel_left₀ (sub_ne_zero.2 hs)]

/- English proof (translation)
Distinguish the cases in `h : w = 1`. Simplify using `[h]`. Simplify using `[zeta₁_eq h, sub_ne_zero.2 h, h]`.
-/
lemma zeta₁_eq_zero_iff (w : ℂ) : riemannZeta₁ w = 0 ↔ w ≠ 1 ∧ riemannZeta w = 0 := by
  by_cases h : w = 1
  · simp [h]
  · simp [zeta₁_eq h, sub_ne_zero.2 h, h]

/- English proof (translation)
Establish `h1 : riemannZeta₁ =ᶠ[nhds w] (fun s => s - 1) * riemannZeta` using `by filter_upwards [compl_singleton_mem_nhds hw] with s hs using zeta₁_eq hs`. Establish `h2 : AnalyticAt ℂ riemannZeta w` using `differentiableOn_riemannZeta.analyticAt (compl_singleton_mem_nhds hw)`. Establish `h3 : AnalyticAt ℂ (fun s : ℂ => s - 1) w` using `by fun_prop`. Unfold `analyticOrderNatAt`. Rewrite using `[analyticOrderAt_congr h1, analyticOrderAt_mul h3 h2, h3.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 hw), zero_add]`.
-/
lemma order_zeta₁ {w : ℂ} (hw : w ≠ 1) :
    analyticOrderNatAt riemannZeta₁ w = analyticOrderNatAt riemannZeta w := by
  have h1 : riemannZeta₁ =ᶠ[nhds w] (fun s => s - 1) * riemannZeta := by
    filter_upwards [compl_singleton_mem_nhds hw] with s hs using zeta₁_eq hs
  have h2 : AnalyticAt ℂ riemannZeta w :=
    differentiableOn_riemannZeta.analyticAt (compl_singleton_mem_nhds hw)
  have h3 : AnalyticAt ℂ (fun s : ℂ => s - 1) w := by fun_prop
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr h1, analyticOrderAt_mul h3 h2,
    h3.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 hw), zero_add]

/- English proof (translation)
Unfold `analyticOrderNatAt`. Use `analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta₁) (g := fun z => c + z) (z₀ := w) (by fun_prop) (by simp)` as an intermediate fact. Conclude with `congrArg _ this`.
-/
lemma order_shift (c w : ℂ) :
    analyticOrderNatAt (fun z => riemannZeta₁ (c + z)) w
      = analyticOrderNatAt riemannZeta₁ (c + w) := by
  unfold analyticOrderNatAt
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta₁) (g := fun z => c + z)
    (z₀ := w) (by fun_prop) (by simp)
  exact congrArg _ this

/- English proof (translation)
Rewrite using `[deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs, zeta₁_eq hs]`. Use `sub_ne_zero.2 hs` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma logDeriv_zeta₁ {s : ℂ} (hs : s ≠ 1) (h0 : riemannZeta s ≠ 0) :
    deriv riemannZeta₁ s / riemannZeta₁ s = deriv riemannZeta s / riemannZeta s + 1 / (s - 1) := by
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs, zeta₁_eq hs]
  have := sub_ne_zero.2 hs
  field_simp
  ring

/- English proof (translation)
Establish `ht` using `abs_nonneg t`. Use `set w : ℂ := 3/2 + t * I + z with hw`. Distinguish the cases in `h : w = 1`. Rewrite using `[h, riemannZeta₁_one, norm_one]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hre : 1 / 2 ≤ w.re`. Use `(abs_le.1 ((abs_re_le_norm z).trans hz)).1` as an intermediate fact. Simplify using `[hw]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `htI : ‖(t : ℂ) * I‖ = |t|` using `by simp`.

Establish `h1 : ‖w - 1‖ ≤ |t| + 2`. Establish `: w - 1 = 1/2 + t * I + z` using `by rw [hw]; ring`. Rewrite using `[this]`. Use `norm_add₃_le.trans ?_` and prove the remaining obligations. Rewrite using `[htI]`.

Evaluate the numerical expressions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : ‖w‖ ≤ 2 * (|t| + 2)`. Use `norm_add₃_le.trans ?_` and prove the remaining obligations. Rewrite using `[htI]`.

Evaluate the numerical expressions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3` using `GlobalTheory.ZetaHalfPlane.norm_zeta_sub_le w (by linarith) h`. Establish `h4 : ‖w‖ / w.re ≤ 2 * ‖w‖`. Rewrite using `[div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg w]`.

Establish `e : riemannZeta₁ w = (w - 1) * (riemannZeta w - w / (w - 1)) + w`. Use `sub_ne_zero.2 h` as an intermediate fact. Rewrite using `[zeta₁_eq h]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Establish `h5 : ‖w - 1‖ * ‖riemannZeta w - w / (w - 1)‖ ≤ (|t| + 2) * (4 * (|t| + 2))` using `mul_le_mul h1 (by linarith) (norm_nonneg _) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma norm_zeta₁_le (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖riemannZeta₁ (3/2 + t * I + z)‖ ≤ 5 * (|t| + 2) ^ 2 := by
  have ht := abs_nonneg t
  set w : ℂ := 3/2 + t * I + z with hw
  by_cases h : w = 1
  · rw [h, riemannZeta₁_one, norm_one]; nlinarith
  have hre : 1 / 2 ≤ w.re := by
    have := (abs_le.1 ((abs_re_le_norm z).trans hz)).1
    simp [hw]; linarith
  have htI : ‖(t : ℂ) * I‖ = |t| := by simp
  have h1 : ‖w - 1‖ ≤ |t| + 2 := by
    have : w - 1 = 1/2 + t * I + z := by rw [hw]; ring
    rw [this]
    refine norm_add₃_le.trans ?_
    rw [htI]; norm_num; linarith
  have h2 : ‖w‖ ≤ 2 * (|t| + 2) := by
    refine norm_add₃_le.trans ?_
    rw [htI]; norm_num; linarith
  have h3 := GlobalTheory.ZetaHalfPlane.norm_zeta_sub_le w (by linarith) h
  have h4 : ‖w‖ / w.re ≤ 2 * ‖w‖ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg w]
  have e : riemannZeta₁ w = (w - 1) * (riemannZeta w - w / (w - 1)) + w := by
    have := sub_ne_zero.2 h
    rw [zeta₁_eq h]; field_simp; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have h5 : ‖w - 1‖ * ‖riemannZeta w - w / (w - 1)‖ ≤ (|t| + 2) * (4 * (|t| + 2)) :=
    mul_le_mul h1 (by linarith) (norm_nonneg _) (by linarith)
  nlinarith

/- English proof (translation)
Use `set w : ℂ := 3/2 + t * I with hw`. Establish `hre : w.re = 3 / 2` using `by simp [hw]`. Establish `h : w ≠ 1`. Introduce `h`. Rewrite `hre` using `[h]`.

Evaluate the numerical expressions using `at hre`. Establish `h1` using `GlobalTheory.LLower.norm_LFunction_ge 1 (1 : DirichletCharacter ℂ 1) w (by rw [hre]; norm_num)`. Rewrite `h1` using `[LFunction_modOne_eq, hre]`. Establish `h2 : 1 / 2 ≤ ‖w - 1‖`. Use `le_trans ?_ (re_le_norm _)` and prove the remaining obligations.

Rewrite using `[sub_re, hre]`. Evaluate the numerical expressions. Rewrite using `[zeta₁_eq h, norm_mul]`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma le_norm_zeta₁ (t : ℝ) : 1 / 6 ≤ ‖riemannZeta₁ (3/2 + t * I)‖ := by
  set w : ℂ := 3/2 + t * I with hw
  have hre : w.re = 3 / 2 := by simp [hw]
  have h : w ≠ 1 := by
    intro h; rw [h] at hre; norm_num at hre
  have h1 := GlobalTheory.LLower.norm_LFunction_ge 1 (1 : DirichletCharacter ℂ 1) w (by rw [hre]; norm_num)
  rw [LFunction_modOne_eq, hre] at h1
  have h2 : 1 / 2 ≤ ‖w - 1‖ := by
    refine le_trans ?_ (re_le_norm _)
    rw [sub_re, hre]; norm_num
  rw [zeta₁_eq h, norm_mul]
  nlinarith

/- English proof (translation)
Take `⟨C, hC, H⟩` from `GlobalTheory.LogDerivZeros.main (2/3) (5/6) (by norm_num) (by norm_num) (by norm_num)`. Use `⟨9 * C, by positivity, fun t s hs hs1 hs0 => ?_⟩` and prove the remaining obligations. Establish `hlow` using `le_norm_zeta₁ t`. Establish `hup` using `fun z => norm_zeta₁_le t (z := z)`. Use `set c : ℂ := 3/2 + t * I with hc`.

Establish `hd : Differentiable ℂ fun z => riemannZeta₁ (c + z)` using `by fun_prop`. Take `⟨⟨hfin, -⟩, H2⟩` from `H (fun z => riemannZeta₁ (c + z)) (5 * (|t| + 2) ^ 2) (fun z _ => hd.analyticAt z) (by`. Simplify using `only [add_zero]`. Introduce `h`. Rewrite `hlow` using `[h, norm_zero]`.

Evaluate the numerical expressions using `at hlow)`. Use the proof step `(fun z hz => hup z (by simpa using hz))`. Establish `hset : {w : ℂ | ‖w - c‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0} = (fun z => c + z) '' {w : ℂ | ‖w‖ ≤ 5/6 ∧ riemannZeta₁ (c + w) = 0}`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨w - c, ⟨h1, by rw [add_sub_cancel]; exact (zeta₁_eq_zero_iff w).2 h2⟩, by simp⟩`. Introduce and unpack `⟨z, ⟨h1, h2⟩, rfl⟩`. Conclude with `⟨by simpa using h1, (zeta₁_eq_zero_iff _).1 h2⟩`. Rewrite using `[hset]`.

Use `⟨hfin.image _, ?_⟩` and prove the remaining obligations. Establish `H3` using `H2 (s - c) hs (by`. Simplify using `only [add_sub_cancel]`. Conclude with `fun h => hs0 ((zeta₁_eq_zero_iff s).1 h).2)`. Rewrite using `[finsum_mem_image (add_right_injective c).injOn, ← logDeriv_zeta₁ hs1 hs0]`.

Establish `e : (∑ᶠ w ∈ {w : ℂ | ‖w‖ ≤ 5/6 ∧ riemannZeta₁ (c + w) = 0}, (analyticOrderNatAt riemannZeta (c + w) : ℂ) / (s - (c + w))) = ∑ᶠ w ∈ {w : ℂ | ‖w‖ ≤ 5/6 ∧ riemannZeta₁ (c + w) = 0}, (analyticOrderNatAt (fun z => riemannZeta₁ (c + z)) w : ℂ) / (s - c - w)`. Use `finsum_mem_congr rfl fun w hw => ?_` and prove the remaining obligations. Rewrite using `[order_shift, order_zeta₁ ((zeta₁_eq_zero_iff _).1 hw.2).1, sub_sub]`. Rewrite using `[e]`. Rewrite `H3` using `[deriv_comp_const_add]`.

Simplify using `only [add_sub_cancel, add_zero] at H3`. Use `H3.trans ?_` and prove the remaining obligations. Establish `ht` using `abs_nonneg t`. Establish `hT : 2 ≤ |t| + 2` using `by linarith`. Use `set T := |t| + 2`.

Establish `hl2 : Real.log 2 ≤ Real.log T` using `Real.log_le_log two_pos hT`. Establish `hl` using `Real.log_two_gt_d9`. Establish `hn : 0 < ‖riemannZeta₁ c‖` using `by linarith`. Establish `h1 : 5 * T ^ 2 / ‖riemannZeta₁ c‖ ≤ T ^ 7`. Rewrite using `[div_le_iff₀ hn]`.

Establish `h5 : (2 : ℝ) ^ 5 ≤ T ^ 5` using `by gcongr`. Establish `h6 : 5 ≤ T ^ 5 * ‖riemannZeta₁ c‖` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `Real.log_le_log (by positivity) h1`. Rewrite `h2` using `[Real.log_pow]`.

Move the coercions through the operations in `at h2`. Establish `: 1 + Real.log (5 * T ^ 2 / ‖riemannZeta₁ c‖) ≤ 9 * Real.log T` using `by linarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem logDeriv_riemannZeta_local : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → s ≠ 1 → riemannZeta s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}.Finite ∧ ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ ≤ C * Real.log (|t| + 2) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LogDerivZeros.main (2/3) (5/6) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨9 * C, by positivity, fun t s hs hs1 hs0 => ?_⟩
  have hlow := le_norm_zeta₁ t
  have hup := fun z => norm_zeta₁_le t (z := z)
  set c : ℂ := 3/2 + t * I with hc
  have hd : Differentiable ℂ fun z => riemannZeta₁ (c + z) := by fun_prop
  obtain ⟨⟨hfin, -⟩, H2⟩ := H (fun z => riemannZeta₁ (c + z)) (5 * (|t| + 2) ^ 2)
    (fun z _ => hd.analyticAt z) (by
      simp only [add_zero]
      intro h; rw [h, norm_zero] at hlow; norm_num at hlow)
    (fun z hz => hup z (by simpa using hz))
  have hset : {w : ℂ | ‖w - c‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}
      = (fun z => c + z) '' {w : ℂ | ‖w‖ ≤ 5/6 ∧ riemannZeta₁ (c + w) = 0} := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨w - c, ⟨h1, by rw [add_sub_cancel]; exact (zeta₁_eq_zero_iff w).2 h2⟩, by simp⟩
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      exact ⟨by simpa using h1, (zeta₁_eq_zero_iff _).1 h2⟩
  rw [hset]
  refine ⟨hfin.image _, ?_⟩
  have H3 := H2 (s - c) hs (by
    simp only [add_sub_cancel]
    exact fun h => hs0 ((zeta₁_eq_zero_iff s).1 h).2)
  rw [finsum_mem_image (add_right_injective c).injOn, ← logDeriv_zeta₁ hs1 hs0]
  have e : (∑ᶠ w ∈ {w : ℂ | ‖w‖ ≤ 5/6 ∧ riemannZeta₁ (c + w) = 0},
      (analyticOrderNatAt riemannZeta (c + w) : ℂ) / (s - (c + w)))
      = ∑ᶠ w ∈ {w : ℂ | ‖w‖ ≤ 5/6 ∧ riemannZeta₁ (c + w) = 0},
      (analyticOrderNatAt (fun z => riemannZeta₁ (c + z)) w : ℂ) / (s - c - w) := by
    refine finsum_mem_congr rfl fun w hw => ?_
    rw [order_shift, order_zeta₁ ((zeta₁_eq_zero_iff _).1 hw.2).1, sub_sub]
  rw [e]
  rw [deriv_comp_const_add] at H3
  simp only [add_sub_cancel, add_zero] at H3
  refine H3.trans ?_
  have ht := abs_nonneg t
  have hT : 2 ≤ |t| + 2 := by linarith
  set T := |t| + 2
  have hl2 : Real.log 2 ≤ Real.log T := Real.log_le_log two_pos hT
  have hl := Real.log_two_gt_d9
  have hn : 0 < ‖riemannZeta₁ c‖ := by linarith
  have h1 : 5 * T ^ 2 / ‖riemannZeta₁ c‖ ≤ T ^ 7 := by
    rw [div_le_iff₀ hn]
    have h5 : (2 : ℝ) ^ 5 ≤ T ^ 5 := by gcongr
    have h6 : 5 ≤ T ^ 5 * ‖riemannZeta₁ c‖ := by nlinarith
    calc 5 * T ^ 2 ≤ (T ^ 5 * ‖riemannZeta₁ c‖) * T ^ 2 := by gcongr
      _ = _ := by ring
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  push_cast at h2
  have : 1 + Real.log (5 * T ^ 2 / ‖riemannZeta₁ c‖) ≤ 9 * Real.log T := by linarith
  nlinarith

end GlobalTheory.ZetaLocal
