import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivEqOrderDivAddAnalytic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivLFunctionStrip
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsMore
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompletedLFunctionNeZeroOfReNonpos
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.LAtZero

/- English proof (translation)
Establish `hc : ContinuousAt (fun s : ℂ => ‖h s + e s - ∑ w ∈ Z.erase 0, (m w : ℂ) / (s - w)‖) 0`. Use `((hh.add he).sub ?_).norm` and prove the remaining obligations. Use `tendsto_finsetSum _ fun w hw => ?_` and prove the remaining obligations. Use `ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const) ?_` and prove the remaining obligations. Simplify using `using Finset.ne_of_mem_erase hw`.

Establish `ht : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 0) (𝓝[≠] (0 : ℂ))`. Use `tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Use `(continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))` as an intermediate fact. Simplify using `using this`. Use `filter_upwards [self_mem_nhdsWithin] with s hs`.

Simplify using `using (ne_of_gt hs)`. Use `le_of_tendsto (hc.tendsto.comp (ht.mono_right nhdsWithin_le_nhds)) ?_` and prove the remaining obligations. Use `filter_upwards [ht.eventually hev, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs hs1`. Establish `h1` using `hloc s hs1.1 hs1.2 hs.1`. Establish `h2 : ∑ w ∈ Z, (m w : ℂ) / (s - w) = (m 0 : ℂ) / s + ∑ w ∈ Z.erase 0, (m w : ℂ) / (s - w)`.

Distinguish the cases in `hz : (0 : ℂ) ∈ Z`. Rewrite using `[← Finset.add_sum_erase _ _ hz, sub_zero]`. Rewrite using `[h0 hz, Finset.erase_eq_of_notMem hz]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[hs.2, h2]`.

Use `le_trans (le_of_eq ?_) h1` and prove the remaining obligations. Simplify using `only [Function.comp]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_limit_le (F h e : ℂ → ℂ) (P : ℂ → Prop) (Z : Finset ℂ) (m : ℂ → ℕ) (B : ℝ)
    (hh : ContinuousAt h 0) (he : ContinuousAt e 0) (h0 : 0 ∉ Z → m 0 = 0)
    (hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), P s ∧ F s = (m 0 : ℂ) / s + h s)
    (hloc : ∀ s : ℝ, 0 < s → s < 1 → P s → ‖F s + e s - ∑ w ∈ Z, (m w : ℂ) / (s - w)‖ ≤ B) :
    ‖h 0 + e 0 - ∑ w ∈ Z.erase 0, (m w : ℂ) / (0 - w)‖ ≤ B := by
  have hc : ContinuousAt (fun s : ℂ => ‖h s + e s - ∑ w ∈ Z.erase 0, (m w : ℂ) / (s - w)‖) 0 := by
    refine ((hh.add he).sub ?_).norm
    refine tendsto_finsetSum _ fun w hw => ?_
    refine ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const) ?_
    simpa using Finset.ne_of_mem_erase hw
  have ht : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 0) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using (ne_of_gt hs)
  refine le_of_tendsto (hc.tendsto.comp (ht.mono_right nhdsWithin_le_nhds)) ?_
  filter_upwards [ht.eventually hev, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs hs1
  have h1 := hloc s hs1.1 hs1.2 hs.1
  have h2 : ∑ w ∈ Z, (m w : ℂ) / (s - w) =
      (m 0 : ℂ) / s + ∑ w ∈ Z.erase 0, (m w : ℂ) / (s - w) := by
    by_cases hz : (0 : ℂ) ∈ Z
    · rw [← Finset.add_sum_erase _ _ hz, sub_zero]
    · rw [h0 hz, Finset.erase_eq_of_notMem hz]; simp
  rw [hs.2, h2] at h1
  refine le_trans (le_of_eq ?_) h1
  simp only [Function.comp]
  congr 1
  ring

/- English proof (translation)
Take `⟨h, hh, hev⟩` from `GlobalTheory.logDeriv_eq_order_div_add_analytic f 0 han hne`. Simplify using `only [sub_zero] at hev`. Use `⟨h, hh, hev.mono fun s hs => hs.2, ?_⟩` and prove the remaining obligations. Simplify using `only [finsum_mem_eq_finite_toFinset_sum _ hS] at hcount hloc`. Establish `key` using `norm_limit_le (fun s => deriv f s / f s) h e (fun s => f s ≠ 0) hS.toFinset (analyticOrderNatAt f) B hh.continuousAt he ?_ hev hloc`.

Use `swap`. Introduce `hz`. Establish `: f 0 ≠ 0` using `fun h0 => hz (by simpa using hS0 h0)`. Rewrite using `[analyticOrderNatAt, han.analyticOrderAt_eq_zero.mpr this]`. Both sides reduce to the same expression.

Establish `hset : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ f ρ = 0} = ↑(hS.toFinset.filter fun ρ => 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1)`. Use extensionality with `w`. Simplify using `only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]`. Conclude with `⟨fun ⟨a, b, c, d⟩ => ⟨hT w a b c d, a, b, c⟩, fun ⟨d, a, b, c⟩ => ⟨a, b, c, hSz w d⟩⟩`. Rewrite using `[hset, finsum_mem_coe_finset, Finset.sum_filter]`.

Establish `hsum : ‖∑ w ∈ hS.toFinset.erase 0, (analyticOrderNatAt f w : ℂ) / (0 - w)‖ ≤ ∑ w ∈ hS.toFinset, ((analyticOrderNatAt f w : ℝ) + if 0 < w.re ∧ w.re < 1 ∧ |w.im| < 1 then (analyticOrderNatAt f w : ℝ) / ‖w‖ else 0)`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Use `le_trans (Finset.sum_le_sum fun w hw => ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset 0 _) fun w _ _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_div, zero_sub, norm_neg, Complex.norm_natCast] split_ifs with hc`. Conclude with `le_add_of_nonneg_left (Nat.cast_nonneg _)`.

Rewrite using `[add_zero]`. Use `div_le_self (Nat.cast_nonneg _) ?_` and prove the remaining obligations. Break down `le_or_gt w.re 0 with h1 | h1` into its components or cases. Conclude with `hbig w (by simpa using Finset.mem_of_mem_erase hw) h1 (Finset.ne_of_mem_erase hw)`. Break down `le_or_gt 1 w.re with h2 | h2` into its components or cases.

Conclude with `h2.trans (re_le_norm w)`. Establish `h3 : 1 ≤ |w.im|` using `not_lt.mp fun h3 => hc ⟨h1, h2, h3⟩`. Conclude with `h3.trans (abs_im_le_norm w)`. Apply the tactic sequence `split_ifs <;> positivity`. Rewrite `hsum` using `[Finset.sum_add_distrib]`.

Use `set X := ∑ w ∈ hS.toFinset.erase 0, (analyticOrderNatAt f w : ℂ) / (0 - w)`. Establish `: ‖h 0‖ ≤ ‖h 0 + e 0 - X‖ + ‖e 0‖ + ‖X‖`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_regular_part (f e : ℂ → ℂ) (S : Set ℂ) (B : ℝ) (hS : S.Finite)
    (he : ContinuousAt e 0) (han : AnalyticAt ℂ f 0) (hne : ¬ ∀ᶠ s in 𝓝 (0 : ℂ), f s = 0)
    (hS0 : f 0 = 0 → 0 ∈ S) (hSz : ∀ w ∈ S, f w = 0)
    (hT : ∀ w : ℂ, 0 < w.re → w.re < 1 → |w.im| < 1 → f w = 0 → w ∈ S)
    (hbig : ∀ w ∈ S, w.re ≤ 0 → w ≠ 0 → 1 ≤ ‖w‖)
    (hcount : ∑ᶠ w ∈ S, (analyticOrderNatAt f w : ℝ) ≤ B)
    (hloc : ∀ s : ℝ, 0 < s → s < 1 → f s ≠ 0 →
      ‖deriv f s / f s + e s - ∑ᶠ w ∈ S, (analyticOrderNatAt f w : ℂ) / (s - w)‖ ≤ B) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧
      (∀ᶠ s in 𝓝[≠] (0 : ℂ), deriv f s / f s = (analyticOrderNatAt f 0 : ℂ) / s + h s) ∧
      ‖h 0‖ ≤ 2 * B + ‖e 0‖ +
        ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ f ρ = 0},
          ((analyticOrderNatAt f ρ : ℕ) : ℝ) / ‖ρ‖ := by
  classical
  obtain ⟨h, hh, hev⟩ := GlobalTheory.logDeriv_eq_order_div_add_analytic f 0 han hne
  simp only [sub_zero] at hev
  refine ⟨h, hh, hev.mono fun s hs => hs.2, ?_⟩
  simp only [finsum_mem_eq_finite_toFinset_sum _ hS] at hcount hloc
  have key := norm_limit_le (fun s => deriv f s / f s) h e (fun s => f s ≠ 0) hS.toFinset
    (analyticOrderNatAt f) B hh.continuousAt he ?_ hev hloc
  swap
  · intro hz
    have : f 0 ≠ 0 := fun h0 => hz (by simpa using hS0 h0)
    rw [analyticOrderNatAt, han.analyticOrderAt_eq_zero.mpr this]; rfl
  have hset : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ f ρ = 0} =
      ↑(hS.toFinset.filter fun ρ => 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1) := by
    ext w
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨hT w a b c d, a, b, c⟩,
      fun ⟨d, a, b, c⟩ => ⟨a, b, c, hSz w d⟩⟩
  rw [hset, finsum_mem_coe_finset, Finset.sum_filter]
  have hsum : ‖∑ w ∈ hS.toFinset.erase 0, (analyticOrderNatAt f w : ℂ) / (0 - w)‖ ≤
      ∑ w ∈ hS.toFinset, ((analyticOrderNatAt f w : ℝ) +
        if 0 < w.re ∧ w.re < 1 ∧ |w.im| < 1 then (analyticOrderNatAt f w : ℝ) / ‖w‖ else 0) := by
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun w hw => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset 0 _) fun w _ _ => ?_)
    · rw [norm_div, zero_sub, norm_neg, Complex.norm_natCast]
      split_ifs with hc
      · exact le_add_of_nonneg_left (Nat.cast_nonneg _)
      · rw [add_zero]
        refine div_le_self (Nat.cast_nonneg _) ?_
        rcases le_or_gt w.re 0 with h1 | h1
        · exact hbig w (by simpa using Finset.mem_of_mem_erase hw) h1 (Finset.ne_of_mem_erase hw)
        rcases le_or_gt 1 w.re with h2 | h2
        · exact h2.trans (re_le_norm w)
        · have h3 : 1 ≤ |w.im| := not_lt.mp fun h3 => hc ⟨h1, h2, h3⟩
          exact h3.trans (abs_im_le_norm w)
    · split_ifs <;> positivity
  rw [Finset.sum_add_distrib] at hsum
  set X := ∑ w ∈ hS.toFinset.erase 0, (analyticOrderNatAt f w : ℂ) / (0 - w)
  have : ‖h 0‖ ≤ ‖h 0 + e 0 - X‖ + ‖e 0‖ + ‖X‖ := by
    calc ‖h 0‖ = ‖(h 0 + e 0 - X) - e 0 + X‖ := by congr 1; ring
      _ ≤ ‖(h 0 + e 0 - X) - e 0‖ + ‖X‖ := norm_add_le _ _
      _ ≤ _ := by gcongr; exact norm_sub_le _ _
  linarith

/- English proof (translation)
Use `(norm_le_abs_re_add_abs_im _).trans ?_` and prove the remaining obligations. Establish `: |w.re - 2| ≤ 2` using `abs_le.mpr ⟨by linarith, by linarith⟩`. Simplify using `only [sub_re, sub_im, re_ofNat, im_ofNat, sub_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_sub_two_le {w : ℂ} (h1 : 0 ≤ w.re) (h2 : w.re < 1) (h3 : |w.im| < 1) :
    ‖w - 2‖ ≤ 7 / 2 := by
  refine (norm_le_abs_re_add_abs_im _).trans ?_
  have : |w.re - 2| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  simp only [sub_re, sub_im, re_ofNat, im_ofNat, sub_zero]
  linarith

/- English proof (translation)
Take `⟨C₁, hC₁, H₁⟩` from `GlobalTheory.LWide.logDeriv_LFunction_strip`. Take `⟨C₂, hC₂, H₂⟩` from `GlobalTheory.ZetaWide.main`. Use `⟨2 * C₁ + 2 * C₂ + 2, by positivity, fun N _ χ hχ => ?_⟩` and prove the remaining obligations. Establish `han : AnalyticAt ℂ (LFunction χ) 0`. Use `DifferentiableOn.analyticAt (s := {1}ᶜ) (fun z hz => (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt) ?_` and prove the remaining obligations.

Conclude with `isOpen_compl_singleton.mem_nhds (by simp)`. Establish `hord : ∀ hL : LFunction χ 0 = 0, analyticOrderNatAt (LFunction χ) 0 = 1` using `fun hL => (GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ 0 (by simp) hL).2.1`. Establish `hm : analyticOrderNatAt (LFunction χ) 0 ≤ 1`. Distinguish the cases in `hL : LFunction χ 0 = 0`. Conclude with `(hord hL).le`.

Rewrite using `[analyticOrderNatAt, han.analyticOrderAt_eq_zero.mpr hL]`. Simplify using the standard rewrite rules. Establish `hne : ¬ ∀ᶠ s in 𝓝 (0 : ℂ), LFunction χ s = 0`. Introduce `hz`. Establish `h1` using `hord hz.self_of_nhds`.

Rewrite `h1` using `[analyticOrderNatAt, analyticOrderAt_eq_top.mpr hz]`. Simplify using `at h1`. Establish `hbig : ∀ w : ℂ, LFunction χ w = 0 → w.re ≤ 0 → w ≠ 0 → 1 ≤ ‖w‖`. Introduce `w hw hre h0`. Take `⟨n, rfl⟩` from `(GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ w hre hw).1`.

Rewrite using `[norm_neg, Complex.norm_natCast]`. Establish `: n ≠ 0` using `by rintro rfl; simp at h0`. Conclude with `Nat.one_le_iff_ne_zero.mpr this` after adjusting the coercions. Establish `hL2 : LFunction χ 2 ≠ 0` using `LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by simp)`. Establish `hN : (1 : ℝ) ≤ N` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)`.

Establish `hlog : 1 / 2 ≤ Real.log (2 * N)`. Establish `h1 : Real.log 2 ≤ Real.log (2 * N)` using `Real.log_le_log (by norm_num) (by linarith)`. Use `Real.log_two_gt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnn : 0 ≤ ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖` using `finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity`.

Distinguish the cases in `h1 : χ = 1`. Establish `hq : N = 1`. Rewrite `hχ` using `[IsPrimitive, h1, conductor_one]`. Conclude with `hχ.symm`. Substitute `hq` using the available equality.

Establish `hf : LFunction χ = riemannZeta` using `LFunction_modOne_eq`. Rewrite `han`, `hm`, `hne`, `hbig`, `hL2`, `hnn`, the goal using `[hf]`. Establish `A` using `H₂ 2 (by norm_num) (by simp) (by norm_num) hL2`. Simplify using `only [im_ofNat, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at A`. Take `⟨h, ha, hb, hc⟩` from `exists_regular_part riemannZeta (fun s => 1 / (s - 1)) _ (C₂ * Real.log 2) A.1 (ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const) (by simp)) han hne (fun h => ⟨norm_sub_two_le (by simp) (by simp) (by simp), by simp, h⟩) (fun w hw => hw.2.2) (fun w a b c …`.

Establish `B` using `(H₂ s (by simp; linarith) (by simp; linarith) (by exact_mod_cast hs1.ne) hs).2.2`. Simplify `B)` using `only [ofReal_im, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add]`. Use `⟨_, h, hm, ha, hb, hc.trans ?_⟩` and prove the remaining obligations. Simplify using `only [Nat.cast_one, mul_one] at hlog ⊢`. Establish `e1 : ‖(1 : ℂ) / (0 - 1)‖ = 1` using `by simp`.

Rewrite using `[e1]`. Use polynomial arithmetic with `[mul_nonneg hC₁.le hnn, mul_nonneg hC₂.le hnn]`. Establish `A` using `H₁ N χ h1 2 (by norm_num) (by simp) hL2`. Simplify using `only [im_ofNat, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at A`. Take `⟨h, ha, hb, hc⟩` from `exists_regular_part (LFunction χ) (fun _ => 0) _ (C₁ * Real.log (N * 2)) A.1 continuousAt_const han hne (fun h => ⟨norm_sub_two_le (by simp) (by simp) (by simp), h⟩) (fun w hw => hw.2) (fun w a b c d => ⟨norm_sub_two_le a.le b c, d⟩) (fun w hw => hbig w hw.2) A.2.1 (fun s hs0 hs1 …`.

Establish `B` using `(H₁ N χ h1 s (by simp; linarith) (by simp; linarith) hs).2.2`. Simplify `B)` using `only [ofReal_im, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add]`. Use `⟨_, h, hm, ha, hb, hc.trans ?_⟩` and prove the remaining obligations. Rewrite using `[norm_zero, mul_comm (N : ℝ) 2]`. Use polynomial arithmetic with `[mul_nonneg hC₁.le hnn, mul_nonneg hC₂.le hnn]`.
-/
theorem logDeriv_LFunction_near_zero : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∃ (m : ℕ) (h : ℂ → ℂ), m ≤ 1 ∧ AnalyticAt ℂ h 0 ∧ (∀ᶠ s in 𝓝[≠] (0 : ℂ), deriv (LFunction χ) s / LFunction χ s = (m : ℂ) / s + h s) ∧ ‖h 0‖ ≤ C * (Real.log (2 * N) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) := by
  obtain ⟨C₁, hC₁, H₁⟩ := GlobalTheory.LWide.logDeriv_LFunction_strip
  obtain ⟨C₂, hC₂, H₂⟩ := GlobalTheory.ZetaWide.main
  refine ⟨2 * C₁ + 2 * C₂ + 2, by positivity, fun N _ χ hχ => ?_⟩
  have han : AnalyticAt ℂ (LFunction χ) 0 := by
    refine DifferentiableOn.analyticAt (s := {1}ᶜ)
      (fun z hz => (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt) ?_
    exact isOpen_compl_singleton.mem_nhds (by simp)
  have hord : ∀ hL : LFunction χ 0 = 0, analyticOrderNatAt (LFunction χ) 0 = 1 := fun hL =>
    (GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ 0 (by simp) hL).2.1
  have hm : analyticOrderNatAt (LFunction χ) 0 ≤ 1 := by
    by_cases hL : LFunction χ 0 = 0
    · exact (hord hL).le
    · rw [analyticOrderNatAt, han.analyticOrderAt_eq_zero.mpr hL]; simp
  have hne : ¬ ∀ᶠ s in 𝓝 (0 : ℂ), LFunction χ s = 0 := by
    intro hz
    have h1 := hord hz.self_of_nhds
    rw [analyticOrderNatAt, analyticOrderAt_eq_top.mpr hz] at h1
    simp at h1
  have hbig : ∀ w : ℂ, LFunction χ w = 0 → w.re ≤ 0 → w ≠ 0 → 1 ≤ ‖w‖ := by
    intro w hw hre h0
    obtain ⟨n, rfl⟩ := (GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ w hre hw).1
    rw [norm_neg, Complex.norm_natCast]
    have : n ≠ 0 := by rintro rfl; simp at h0
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hL2 : LFunction χ 2 ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by simp)
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlog : 1 / 2 ≤ Real.log (2 * N) := by
    have h1 : Real.log 2 ≤ Real.log (2 * N) := Real.log_le_log (by norm_num) (by linarith)
    have := Real.log_two_gt_d9
    linarith
  have hnn : 0 ≤ ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖ :=
    finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  by_cases h1 : χ = 1
  · have hq : N = 1 := by
      rw [IsPrimitive, h1, conductor_one] at hχ
      exact hχ.symm
    subst hq
    have hf : LFunction χ = riemannZeta := LFunction_modOne_eq
    rw [hf] at han hm hne hbig hL2 hnn ⊢
    have A := H₂ 2 (by norm_num) (by simp) (by norm_num) hL2
    simp only [im_ofNat, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at A
    obtain ⟨h, ha, hb, hc⟩ := exists_regular_part riemannZeta (fun s => 1 / (s - 1)) _
      (C₂ * Real.log 2) A.1
      (ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const) (by simp))
      han hne (fun h => ⟨norm_sub_two_le (by simp) (by simp) (by simp), by simp, h⟩)
      (fun w hw => hw.2.2)
      (fun w a b c d => ⟨norm_sub_two_le a.le b c, by rintro rfl; simp at b, d⟩)
      (fun w hw => hbig w hw.2.2) A.2.1 (fun s hs0 hs1 hs => by
        have B := (H₂ s (by simp; linarith) (by simp; linarith)
          (by exact_mod_cast hs1.ne) hs).2.2
        simpa only [ofReal_im, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] using B)
    refine ⟨_, h, hm, ha, hb, hc.trans ?_⟩
    simp only [Nat.cast_one, mul_one] at hlog ⊢
    have e1 : ‖(1 : ℂ) / (0 - 1)‖ = 1 := by simp
    rw [e1]
    nlinarith [mul_nonneg hC₁.le hnn, mul_nonneg hC₂.le hnn]
  · have A := H₁ N χ h1 2 (by norm_num) (by simp) hL2
    simp only [im_ofNat, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at A
    obtain ⟨h, ha, hb, hc⟩ := exists_regular_part (LFunction χ) (fun _ => 0) _
      (C₁ * Real.log (N * 2)) A.1 continuousAt_const
      han hne (fun h => ⟨norm_sub_two_le (by simp) (by simp) (by simp), h⟩)
      (fun w hw => hw.2)
      (fun w a b c d => ⟨norm_sub_two_le a.le b c, d⟩)
      (fun w hw => hbig w hw.2) A.2.1 (fun s hs0 hs1 hs => by
        have B := (H₁ N χ h1 s (by simp; linarith) (by simp; linarith) hs).2.2
        simpa only [ofReal_im, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] using B)
    refine ⟨_, h, hm, ha, hb, hc.trans ?_⟩
    rw [norm_zero, mul_comm (N : ℝ) 2]
    nlinarith [mul_nonneg hC₁.le hnn, mul_nonneg hC₂.le hnn]

end GlobalTheory.LAtZero
