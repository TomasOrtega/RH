import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivLFunctionStrip

open Complex DirichletCharacter

namespace GlobalTheory.CompanionTheory.An

open GlobalTheory.Mem.An

/- English proof (translation)
Establish `hre : w.re < 1`. Assume the negation of the conclusion as `h`. Conclude with `LFunction_ne_zero_of_one_le_re χ (Or.inl h1) (not_lt.1 h) hw`. Distinguish the cases in `h0 : 0 < w.re`. Establish `him : 1 < |w.im|`.

Assume the negation of the conclusion as `h`. Use `hB ⟨h0, hre, ?_, hw⟩` and prove the remaining obligations. Simplify using `using not_lt.1 h`. Use `Complex.abs_im_le_norm (1 - w)` as an intermediate fact. Establish `e : |(1 - w).im| = |w.im|` using `by simp`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `Complex.abs_re_le_norm (1 - w)` as an intermediate fact. Establish `e : (1 - w).re = 1 - w.re` using `by simp`. Rewrite `this` using `[e]`. Use `le_abs_self (1 - w.re)` as an intermediate fact.

Combine the linear relations using `[not_lt.1 h0]`.
-/
theorem one_le_norm_one_sub {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h1 : χ ≠ 1) {w : ℂ}
    (hw : LFunction χ w = 0) (hB : w ∉ zerosIn χ 0 1) : 1 ≤ ‖1 - w‖ := by
  have hre : w.re < 1 := by
    by_contra h
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl h1) (not_lt.1 h) hw
  by_cases h0 : 0 < w.re
  · have him : 1 < |w.im| := by
      by_contra h
      refine hB ⟨h0, hre, ?_, hw⟩
      simpa using not_lt.1 h
    have := Complex.abs_im_le_norm (1 - w)
    have e : |(1 - w).im| = |w.im| := by simp
    linarith
  · have := Complex.abs_re_le_norm (1 - w)
    have e : (1 - w).re = 1 - w.re := by simp
    rw [e] at this
    have := le_abs_self (1 - w.re)
    linarith [not_lt.1 h0]

/- English proof (translation)
Take `⟨h0, h1, h2, -⟩` from `hw`. Use `(Complex.norm_le_abs_re_add_abs_im _).trans ?_` and prove the remaining obligations. Establish `a : (w - 2).re = w.re - 2` using `by simp`. Establish `b : (w - 2).im = w.im` using `by simp`. Rewrite using `[a, b]`.

Apply the tactic sequence `have h3 : |w.re - 2| ≤ 2 := by rw [abs_le]; constructor <;> linarith`. Establish `h4 : |w.im| ≤ 1` using `by simpa using h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_sub_two_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {w : ℂ}
    (hw : w ∈ zerosIn χ 0 1) : ‖w - 2‖ ≤ 7 / 2 := by
  obtain ⟨h0, h1, h2, -⟩ := hw
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have a : (w - 2).re = w.re - 2 := by simp
  have b : (w - 2).im = w.im := by simp
  rw [a, b]
  have h3 : |w.re - 2| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have h4 : |w.im| ≤ 1 := by simpa using h2
  linarith

/- English proof (translation)
Take `⟨C, hC, H⟩` from `GlobalTheory.LWide.logDeriv_LFunction_strip`. Use `⟨2 * C, fun q _ χ hq hχ => ?_⟩` and prove the remaining obligations. Establish `h1 : χ ≠ 1`. Introduce and unpack `rfl`. Rewrite `hχ` using `[DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one]`.

Use linear arithmetic over natural numbers and integers. Establish `hL : LFunction χ 1 ≠ 0` using `LFunction_apply_one_ne_zero h1`. Take `⟨hW, hcount, hmain⟩` from `H q χ h1 1 (by norm_num) (by norm_num) hL`. Simplify using `only [Complex.one_im, Complex.ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at hW hcount hmain`. Use `set W : Set ℂ := {w : ℂ | ‖w - 2‖ ≤ 7 / 2 ∧ LFunction χ w = 0} with hWdef`.

Use `set B : Set ℂ := zerosIn χ 0 1 with hBdef`. Use `set g : ℂ → ℂ := fun w => (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w) with hg`. Establish `hBW : B ⊆ W` using `fun w hw => ⟨norm_sub_two_le hw, hw.2.2.2⟩`. Establish `hz : zsum χ 0 1 (fun ρ => 1 / (1 - ρ)) = ∑ᶠ w ∈ B, g w`. Unfold `zsum zmult`.

Use `finsum_mem_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `only [hg, mul_one_div]`. Establish `hsplit : ∑ᶠ w ∈ B, g w + ∑ᶠ w ∈ W \ B, g w = ∑ᶠ w ∈ W, g w` using `finsum_mem_add_sdiff hBW hW`. Establish `hD : ‖∑ᶠ w ∈ W \ B, g w‖ ≤ ∑ᶠ w ∈ W, (analyticOrderNatAt (LFunction χ) w : ℝ)`. Establish `hfin : (W \ B).Finite` using `hW.subset Set.diff_subset`.

Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hW]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun w hw => ?_` and prove the remaining obligations. Establish `hw' : w ∈ W \ B` using `by simpa using hw`.

Establish `h2` using `one_le_norm_one_sub h1 hw'.1.2 hw'.2`. Simplify using `only [hg, norm_div, Complex.norm_natCast]`. Conclude with `div_le_self (Nat.cast_nonneg _) h2`. Use `_ ≤ ∑ w ∈ hW.toFinset, (analyticOrderNatAt (LFunction χ) w : ℝ) := by`. Use `Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _` and prove the remaining obligations.

Introduce `x hx`. Simplify using `only [Set.Finite.mem_toFinset] at hx ⊢`. Conclude with `hx.1`. Establish `hlog : Real.log (q * 2) ≤ Real.log (3 * q)`. Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast (by omega : 0 < q)`.

Conclude with `Real.log_le_log (by positivity) (by linarith)`. Rewrite using `[hz]`. Establish `hmain' : ‖deriv (LFunction χ) 1 / LFunction χ 1 - ∑ᶠ w ∈ W, g w‖ ≤ C * Real.log (q * 2)` using `hmain`. Establish `e : deriv (LFunction χ) 1 / LFunction χ 1 - ∑ᶠ w ∈ B, g w = (deriv (LFunction χ) 1 / LFunction χ 1 - ∑ᶠ w ∈ W, g w) + ∑ᶠ w ∈ W \ B, g w`. Rewrite using `[← hsplit]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Establish `h3` using `hD.trans hcount`. Establish `h4` using `mul_le_mul_of_nonneg_left hlog hC.le`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logDerOne_holds : LogDerOne := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LWide.logDeriv_LFunction_strip
  refine ⟨2 * C, fun q _ χ hq hχ => ?_⟩
  have h1 : χ ≠ 1 := by
    rintro rfl
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hχ
    omega
  have hL : LFunction χ 1 ≠ 0 := LFunction_apply_one_ne_zero h1
  obtain ⟨hW, hcount, hmain⟩ := H q χ h1 1 (by norm_num) (by norm_num) hL
  simp only [Complex.one_im, Complex.ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at hW hcount hmain
  set W : Set ℂ := {w : ℂ | ‖w - 2‖ ≤ 7 / 2 ∧ LFunction χ w = 0} with hWdef
  set B : Set ℂ := zerosIn χ 0 1 with hBdef
  set g : ℂ → ℂ := fun w => (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w) with hg
  have hBW : B ⊆ W := fun w hw => ⟨norm_sub_two_le hw, hw.2.2.2⟩
  have hz : zsum χ 0 1 (fun ρ => 1 / (1 - ρ)) = ∑ᶠ w ∈ B, g w := by
    unfold zsum zmult
    refine finsum_mem_congr rfl fun w _ => ?_
    simp only [hg, mul_one_div]
  have hsplit : ∑ᶠ w ∈ B, g w + ∑ᶠ w ∈ W \ B, g w = ∑ᶠ w ∈ W, g w :=
    finsum_mem_add_sdiff hBW hW
  have hD : ‖∑ᶠ w ∈ W \ B, g w‖ ≤ ∑ᶠ w ∈ W, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
    have hfin : (W \ B).Finite := hW.subset Set.diff_subset
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hW]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ w ∈ hfin.toFinset, ‖g w‖
        ≤ ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
          refine Finset.sum_le_sum fun w hw => ?_
          have hw' : w ∈ W \ B := by simpa using hw
          have h2 := one_le_norm_one_sub h1 hw'.1.2 hw'.2
          simp only [hg, norm_div, Complex.norm_natCast]
          exact div_le_self (Nat.cast_nonneg _) h2
      _ ≤ ∑ w ∈ hW.toFinset, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _
          intro x hx
          simp only [Set.Finite.mem_toFinset] at hx ⊢
          exact hx.1
  have hlog : Real.log (q * 2) ≤ Real.log (3 * q) := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    exact Real.log_le_log (by positivity) (by linarith)
  rw [hz]
  have hmain' : ‖deriv (LFunction χ) 1 / LFunction χ 1 - ∑ᶠ w ∈ W, g w‖ ≤ C * Real.log (q * 2) := hmain
  have e : deriv (LFunction χ) 1 / LFunction χ 1 - ∑ᶠ w ∈ B, g w =
      (deriv (LFunction χ) 1 / LFunction χ 1 - ∑ᶠ w ∈ W, g w) + ∑ᶠ w ∈ W \ B, g w := by
    rw [← hsplit]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h3 := hD.trans hcount
  have h4 := mul_le_mul_of_nonneg_left hlog hC.le
  linarith

end GlobalTheory.CompanionTheory.An
