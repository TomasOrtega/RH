import ReciprocityTheory.L2DbarEstimates.LeviForms.TwistLeviA

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

/- English proof (translation)
Introduce `z g ph ph2 r j ε δ hz hg hph hLph hph2 hLph2 hr hj hε hδ hbd`. Use `set c := 1 + Real.log (1 + ε ^ 2) with hc`. Establish `hlε` using `tl_lw_smoothR n z g ph r ε hg hph hε`. Establish `hlδ` using `tl_lw_smoothR n z g ph r δ hg hph hδ`. Establish `hwgt : SmoothR n z (wgt n g ph ph2 r j δ)` using `SmoothR.add n z _ _ (SmoothR.add n z _ _ hph2 (SmoothR.mul n z _ _ (smoothR_const n z _) hph)) (SmoothR.mul n z _ _ (smoothR_const n z _) hlδ)`.

Establish `htw : SmoothR n z (twist n g ph r ε)`. Rewrite using `[tl_twist_eq n g ph r ε hr hε hbd]`. Conclude with `SmoothR.comp n z _ (tlK_contDiff c) _ hlε`. Take `⟨hB1, -, -, -⟩` from `hB g ph ph2 r j ε δ hr hε hbd`. Establish `hj' : (2 : ℝ) ≤ j` using `by exact_mod_cast hj`.

Establish `key : ∀ x ξ, tlKpp c (lw n g ph r ε x) * ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 + tlKp c (lw n g ph r ε x) * ((Levi n z (lw n g ph r ε) x ξ).re + (Levi n z ph x ξ).re) ≤ (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re`. Introduce `x ξ`. Rewrite using `[tl_levi_formula n hCh z g ph ph2 r j ε δ hz hg hph hph2 hr hε hδ hbd x ξ]`. Take `⟨hx1, he1, hk2, -⟩` from `hB1 x`. Establish `hq : tlKp c (lw n g ph r ε x) = kap n g ph r ε x / eta n g ph r ε x` using `rfl`.

Establish `hq0 : 0 ≤ kap n g ph r ε x / eta n g ph r ε x`. Unfold `kap; have : 0 ≤ 1 / xx n g ph r ε x := by positivity`. Conclude with `div_nonneg (by linarith) (by linarith)`. Establish `hq2 : kap n g ph r ε x / eta n g ph r ε x ≤ 2`. Rewrite using `[div_le_iff₀ (by linarith)]; nlinarith`.

Establish `hL2` using `hLph2 x ξ`. Establish `hL` using `hLph x ξ`. Establish `hδL` using `(hLog z g ph r δ hz hg hph hLph hr.ne' hδ x ξ).2`. Establish `h1` using `mul_nonneg (show 0 ≤ (j : ℝ) - kap n g ph r ε x / eta n g ph r ε x by linarith) hL`. Establish `h2` using `mul_nonneg (show (0 : ℝ) ≤ n by positivity) hδL`.

Rewrite using `[hq]`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨hwgt, htw, ?_, ?_⟩` and prove the remaining obligations. Introduce `x ξ`. Establish `hk` using `key x ξ`.

Establish `hεL` using `(hLog z g ph r ε hz hg hph hLph hr.ne' hε x ξ).2`. Take `⟨hx1, he1, hk2, -⟩` from `hB1 x`. Establish `hq0 : 0 ≤ tlKp c (lw n g ph r ε x)` using `by show 0 ≤ kap n g ph r ε x / eta n g ph r ε x`. Unfold `kap; have : 0 ≤ 1 / xx n g ph r ε x := by positivity`. Conclude with `div_nonneg (by linarith) (by linarith)`.

Use `mul_nonneg hq0 hεL` as an intermediate fact. Establish `e : tlKpp c (lw n g ph r ε x) = 1 / (xx n g ph r ε x ^ 2 * eta n g ph r ε x) + (kap n g ph r ε x / eta n g ph r ε x) ^ 2` using `rfl`. Rewrite using `[← e]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `x ξ hx`.

Establish `hk` using `key x ξ`. Take `⟨hε1, hεL⟩` from `hLog z g ph r ε hz hg hph hLph hr.ne' hε x ξ`. Take `⟨hx1, he1, hk2, -⟩` from `hB1 x`. Use `set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 with hD`. Use `set A := (Levi n z (lw n g ph r ε) x ξ).re + (Levi n z ph x ξ).re with hAdef`.

Establish `hD0 : 0 ≤ D` using `by positivity`. Establish `hDA : D ≤ A`. Establish `hε2 : 0 < ε ^ 2` using `by positivity`. Establish `: ε ^ 2 * D ≤ ε ^ 2 * A` using `hε1.trans (mul_le_mul_of_nonneg_right hx hεL)`. Conclude with `le_of_mul_le_mul_left this hε2`.

Establish `hq : tlKp c (lw n g ph r ε x) = kap n g ph r ε x / eta n g ph r ε x` using `rfl`. Establish `hpp : 0 ≤ tlKpp c (lw n g ph r ε x)` using `by show 0 ≤ 1 / (xx n g ph r ε x ^ 2 * eta n g ph r ε x) + (kap n g ph r ε x / eta n g ph r ε x) ^ 2`. Establish `: 0 ≤ 1 / (xx n g ph r ε x ^ 2 * eta n g ph r ε x)` using `div_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith))`. Check the signs of the components of the expression. Establish `hq0 : 0 ≤ kap n g ph r ε x / eta n g ph r ε x`.

Unfold `kap; have : 0 ≤ 1 / xx n g ph r ε x := by positivity`. Conclude with `div_nonneg (by linarith) (by linarith)`. Rewrite `hk` using `[hq]`. Establish `h3 : kap n g ph r ε x / eta n g ph r ε x * D ≤ (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re`. Use `mul_le_mul_of_nonneg_left hDA hq0` as an intermediate fact.

Use `mul_nonneg hpp hD0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4` using `mul_le_mul_of_nonneg_left h3 (show 0 ≤ eta n g ph r ε x by linarith)`. Establish `h5 : eta n g ph r ε x * (kap n g ph r ε x / eta n g ph r ε x * D) = kap n g ph r ε x * D`. Clear the denominators using the available nonvanishing facts.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem twistLevi (n : ℕ) (M : Type u) [TopologicalSpace M]
    (hLog : LogLeviStatement n M) (hCh : ChainStatement n M) (hB : BasicStatement n M) :
    TwistLeviStatement n M := by
  intro z g ph ph2 r j ε δ hz hg hph hLph hph2 hLph2 hr hj hε hδ hbd
  set c := 1 + Real.log (1 + ε ^ 2) with hc
  have hlε := tl_lw_smoothR n z g ph r ε hg hph hε
  have hlδ := tl_lw_smoothR n z g ph r δ hg hph hδ
  have hwgt : SmoothR n z (wgt n g ph ph2 r j δ) :=
    SmoothR.add n z _ _ (SmoothR.add n z _ _ hph2 (SmoothR.mul n z _ _ (smoothR_const n z _) hph))
      (SmoothR.mul n z _ _ (smoothR_const n z _) hlδ)
  have htw : SmoothR n z (twist n g ph r ε) := by
    rw [tl_twist_eq n g ph r ε hr hε hbd]; exact SmoothR.comp n z _ (tlK_contDiff c) _ hlε
  obtain ⟨hB1, -, -, -⟩ := hB g ph ph2 r j ε δ hr hε hbd
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj

  have key : ∀ x ξ,
      tlKpp c (lw n g ph r ε x) * ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 +
        tlKp c (lw n g ph r ε x) * ((Levi n z (lw n g ph r ε) x ξ).re + (Levi n z ph x ξ).re) ≤
      (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re := by
    intro x ξ
    rw [tl_levi_formula n hCh z g ph ph2 r j ε δ hz hg hph hph2 hr hε hδ hbd x ξ]
    obtain ⟨hx1, he1, hk2, -⟩ := hB1 x
    have hq : tlKp c (lw n g ph r ε x) = kap n g ph r ε x / eta n g ph r ε x := rfl
    have hq0 : 0 ≤ kap n g ph r ε x / eta n g ph r ε x := by
      unfold kap; have : 0 ≤ 1 / xx n g ph r ε x := by positivity
      exact div_nonneg (by linarith) (by linarith)
    have hq2 : kap n g ph r ε x / eta n g ph r ε x ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hL2 := hLph2 x ξ
    have hL := hLph x ξ
    have hδL := (hLog z g ph r δ hz hg hph hLph hr.ne' hδ x ξ).2
    have h1 := mul_nonneg (show 0 ≤ (j : ℝ) - kap n g ph r ε x / eta n g ph r ε x by linarith) hL
    have h2 := mul_nonneg (show (0 : ℝ) ≤ n by positivity) hδL
    rw [hq]
    nlinarith
  refine ⟨hwgt, htw, ?_, ?_⟩
  · intro x ξ
    have hk := key x ξ
    have hεL := (hLog z g ph r ε hz hg hph hLph hr.ne' hε x ξ).2
    obtain ⟨hx1, he1, hk2, -⟩ := hB1 x
    have hq0 : 0 ≤ tlKp c (lw n g ph r ε x) := by
      show 0 ≤ kap n g ph r ε x / eta n g ph r ε x
      unfold kap; have : 0 ≤ 1 / xx n g ph r ε x := by positivity
      exact div_nonneg (by linarith) (by linarith)
    have := mul_nonneg hq0 hεL
    have e : tlKpp c (lw n g ph r ε x) = 1 / (xx n g ph r ε x ^ 2 * eta n g ph r ε x) +
        (kap n g ph r ε x / eta n g ph r ε x) ^ 2 := rfl
    rw [← e]
    linarith
  · intro x ξ hx
    have hk := key x ξ
    obtain ⟨hε1, hεL⟩ := hLog z g ph r ε hz hg hph hLph hr.ne' hε x ξ
    obtain ⟨hx1, he1, hk2, -⟩ := hB1 x
    set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 with hD
    set A := (Levi n z (lw n g ph r ε) x ξ).re + (Levi n z ph x ξ).re with hAdef
    have hD0 : 0 ≤ D := by positivity
    have hDA : D ≤ A := by
      have hε2 : 0 < ε ^ 2 := by positivity
      have : ε ^ 2 * D ≤ ε ^ 2 * A := hε1.trans (mul_le_mul_of_nonneg_right hx hεL)
      exact le_of_mul_le_mul_left this hε2
    have hq : tlKp c (lw n g ph r ε x) = kap n g ph r ε x / eta n g ph r ε x := rfl
    have hpp : 0 ≤ tlKpp c (lw n g ph r ε x) := by
      show 0 ≤ 1 / (xx n g ph r ε x ^ 2 * eta n g ph r ε x) + (kap n g ph r ε x / eta n g ph r ε x) ^ 2
      have : 0 ≤ 1 / (xx n g ph r ε x ^ 2 * eta n g ph r ε x) :=
        div_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith))
      positivity
    have hq0 : 0 ≤ kap n g ph r ε x / eta n g ph r ε x := by
      unfold kap; have : 0 ≤ 1 / xx n g ph r ε x := by positivity
      exact div_nonneg (by linarith) (by linarith)
    rw [hq] at hk
    have h3 : kap n g ph r ε x / eta n g ph r ε x * D ≤
        (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re := by
      have := mul_le_mul_of_nonneg_left hDA hq0
      have := mul_nonneg hpp hD0
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ eta n g ph r ε x by linarith)
    have h5 : eta n g ph r ε x * (kap n g ph r ε x / eta n g ph r ε x * D) = kap n g ph r ε x * D := by
      field_simp
    linarith

end ReciprocityTheory.L2DbarEstimates.I
