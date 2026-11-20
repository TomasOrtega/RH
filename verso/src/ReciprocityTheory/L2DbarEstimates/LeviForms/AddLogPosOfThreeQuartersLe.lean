import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

universe u

noncomputable section

def dualSig (s : ℝ) : ℝ := 3 / 4 + (s - 3 / 4) * Real.smoothTransition ((s - 3 / 4) * 8)

/- English proof (translation)
Unfold `dualSig`. Conclude with `contDiff_const.add ((contDiff_id.sub contDiff_const).mul (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).mul contDiff_const)))`.
-/
lemma dualSig_contDiff : ContDiff ℝ ∞ dualSig := by
  unfold dualSig
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).mul contDiff_const)))

/- English proof (translation)
Unfold `dualSig`. Break down `le_or_gt s (3 / 4) with h | h` into its components or cases. Rewrite using `[Real.smoothTransition.zero_of_nonpos (by nlinarith)]`. Simplify using the standard rewrite rules. Use `Real.smoothTransition.nonneg ((s - 3 / 4) * 8)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities.
-/
lemma dualSig_ge (s : ℝ) : 3 / 4 ≤ dualSig s := by
  unfold dualSig
  rcases le_or_gt s (3 / 4) with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by nlinarith)]
    simp
  · have := Real.smoothTransition.nonneg ((s - 3 / 4) * 8)
    nlinarith

/- English proof (translation)
Unfold `dualSig`. Rewrite using `[Real.smoothTransition.one_of_one_le (by linarith)]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma dualSig_eq {s : ℝ} (hs : 7 / 8 ≤ s) : dualSig s = s := by
  unfold dualSig
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

/- English proof (translation)
Establish `h0 : 0 < s` using `by linarith`. Establish `h1` using `Real.one_sub_inv_le_log_of_pos h0`. Establish `h2 : s⁻¹ ≤ 4 / 3`. Rewrite using `[inv_le_comm₀ h0 (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma add_log_pos_of_three_quarters_le {s : ℝ} (hs : 3 / 4 ≤ s) : 0 < s + Real.log s := by
  have h0 : 0 < s := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos h0
  have h2 : s⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ h0 (by norm_num)]
    linarith
  linarith

def dualK (c t : ℝ) : ℝ := -Real.log (dualSig (c - t) + Real.log (dualSig (c - t)))

/- English proof (translation)
Establish `hs : ContDiff ℝ ∞ (fun t : ℝ => dualSig (c - t))` using `dualSig_contDiff.comp (contDiff_const.sub contDiff_id)`. Establish `hpos : ∀ t, 0 < dualSig (c - t)` using `fun t => by linarith [dualSig_ge (c - t)]`. Establish `hl : ContDiff ℝ ∞ (fun t : ℝ => Real.log (dualSig (c - t)))` using `hs.log (fun t => (hpos t).ne')`. Establish `hsum : ContDiff ℝ ∞ (fun t : ℝ => dualSig (c - t) + Real.log (dualSig (c - t)))` using `hs.add hl`. Use `hsum.log (fun t => (add_log_pos_of_three_quarters_le (dualSig_ge (c - t))).ne')` as an intermediate fact.

Conclude with `this.neg`.
-/
lemma dualK_contDiff (c : ℝ) : ContDiff ℝ ∞ (dualK c) := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => dualSig (c - t)) :=
    dualSig_contDiff.comp (contDiff_const.sub contDiff_id)
  have hpos : ∀ t, 0 < dualSig (c - t) := fun t => by linarith [dualSig_ge (c - t)]
  have hl : ContDiff ℝ ∞ (fun t : ℝ => Real.log (dualSig (c - t))) :=
    hs.log (fun t => (hpos t).ne')
  have hsum : ContDiff ℝ ∞ (fun t : ℝ => dualSig (c - t) + Real.log (dualSig (c - t))) := hs.add hl
  have := hsum.log (fun t => (add_log_pos_of_three_quarters_le (dualSig_ge (c - t))).ne')
  exact this.neg

/- English proof (translation)
Unfold `dualK`. Rewrite using `[dualSig_eq h]`.
-/
lemma dualK_eq {c t : ℝ} (h : 7 / 8 ≤ c - t) :
    dualK c t = -Real.log ((c - t) + Real.log (c - t)) := by
  unfold dualK
  rw [dualSig_eq h]

/- English proof (translation)
Establish `hev : dualK c =ᶠ[𝓝 t] fun u => -Real.log ((c - u) + Real.log (c - u))`. Establish `: ∀ᶠ u in 𝓝 t, u < t + 1 / 8` using `eventually_lt_nhds (by linarith)`. Use `filter_upwards [this] with u hu`. Conclude with `dualK_eq (by linarith)`. Rewrite using `[hev.deriv_eq]`.

Establish `hs0 : c - t ≠ 0` using `by linarith`. Establish `hpos : 0 < (c - t) + Real.log (c - t)` using `add_log_pos_of_three_quarters_le (by linarith)`. Establish `h1 : HasDerivAt (fun u : ℝ => c - u) (-1) t`. Simplify using `using (hasDerivAt_id t).const_sub c`. Establish `h2` using `h1.log hs0`.

Establish `h4 : HasDerivAt (fun u => -Real.log ((c - u) + Real.log (c - u))) (-((-1 + -1 / (c - t)) / ((c - t) + Real.log (c - t)))) t` using `((h1.add h2).log hpos.ne').neg`. Rewrite using `[h4.deriv]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma dualK_deriv {c t : ℝ} (h : 1 ≤ c - t) :
    deriv (dualK c) t = (1 + 1 / (c - t)) / ((c - t) + Real.log (c - t)) := by
  have hev : dualK c =ᶠ[𝓝 t] fun u => -Real.log ((c - u) + Real.log (c - u)) := by
    have : ∀ᶠ u in 𝓝 t, u < t + 1 / 8 := eventually_lt_nhds (by linarith)
    filter_upwards [this] with u hu
    exact dualK_eq (by linarith)
  rw [hev.deriv_eq]
  have hs0 : c - t ≠ 0 := by linarith
  have hpos : 0 < (c - t) + Real.log (c - t) := add_log_pos_of_three_quarters_le (by linarith)
  have h1 : HasDerivAt (fun u : ℝ => c - u) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub c
  have h2 := h1.log hs0
  have h4 : HasDerivAt (fun u => -Real.log ((c - u) + Real.log (c - u)))
      (-((-1 + -1 / (c - t)) / ((c - t) + Real.log (c - t)))) t :=
    ((h1.add h2).log hpos.ne').neg
  rw [h4.deriv]
  field_simp
  ring

/- English proof (translation)
The claim follows from `|deriv k (f x)| * ‖dDot n z (fun y => (f y : ℂ)) x ξ‖ := by have : dbarDot n z (fun y => (k (f y) : ℂ)) x ξ = ((deriv k (f x) : ℝ) : ℂ) * (starRingEnd ℂ) (dDot n z (fun y => (f y : ℂ)) x ξ) := by unfold dbarDot dDot rw [map_sum, Finset.mul_sum] refine Finset.sum_congr rfl fun i _ …`.
-/
lemma dual_dbarDot_comp_real {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℝ → ℝ)
    (hk : ContDiff ℝ ∞ k) (f : M → ℝ) (hf : CkR n z 1 f) (x : M) (ξ : Fin n → ℂ) :
    ‖dbarDot n z (fun y => (k (f y) : ℂ)) x ξ‖ =
      |deriv k (f x)| * ‖dDot n z (fun y => (f y : ℂ)) x ξ‖ := by
  have : dbarDot n z (fun y => (k (f y) : ℂ)) x ξ =
      ((deriv k (f x) : ℝ) : ℂ) * (starRingEnd ℂ) (dDot n z (fun y => (f y : ℂ)) x ξ) := by
    unfold dbarDot dDot
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [db_comp_real n z k hk f hf i x, db_ofReal, map_mul]
    ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]

/- English proof (translation)
Introduce `z g ph ph2 r j ε δ hz hg hph hphL hph2 hph2L hr hj hε hδ hbd`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Apply the tactic sequence `refine ⟨fun x ξ => ?_, fun x ξ _ => ?_, fun x ξ _ => ?_⟩ <;> simp [dbarDot, Levi]`. Take `⟨hB1, -, -, -⟩` from `hB g ph ph2 r j ε δ hr hε hbd`. Take `⟨-, -, hT1, hT2⟩` from `hT z g ph ph2 r j ε δ hz hg hph hphL hph2 hph2L hr hj hε hδ hbd`.

Take `⟨hW, -, -, -⟩` from `hT z g ph ph2 r j ε ε hz hg hph hphL hph2 hph2L hr hj hε hε hbd`. Establish `hn0 : (n : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`. Establish `hlw : SmoothR n z (lw n g ph r ε)`. Establish `e : (fun y => (lw n g ph r ε y : ℂ)) = fun y => (1 / (n : ℂ)) * (((wgt n g ph ph2 r j ε y : ℝ) : ℂ) - (ph2 y : ℂ) - ((n : ℂ) + j) * (ph y : ℂ))`. Use function extensionality and compare the values at `y`.

Unfold `wgt`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Unfold `SmoothR`.

Rewrite using `[e]`. Conclude with `Smooth.mul _ _ _ _ (Smooth.const _ _ _) (Smooth.sub _ _ _ _ (Smooth.sub _ _ _ _ hW hph2) (Smooth.mul _ _ _ _ (Smooth.const _ _ _) hph))`. Establish `hlw1 : CkR n z 1 (lw n g ph r ε)` using `SmoothR.ckR n z 1 _ hlw`. Establish `hev0 : ∀ y, 0 ≤ ev n g ph r y` using `fun y => by unfold ev; positivity`. Establish `hxx : ∀ y, xx n g ph r ε y = (1 + Real.log (1 + ε ^ 2)) - lw n g ph r ε y` using `fun y => rfl`.

Establish `htw : (fun y => (twist n g ph r ε y : ℂ)) = fun y => ((dualK (1 + Real.log (1 + ε ^ 2)) (lw n g ph r ε y) : ℝ) : ℂ)`. Use function extensionality and compare the values at `y`. Rewrite using `[dualK_eq (by rw [← hxx]; linarith [(hB1 y).1])]`. Unfold `twist eta`. Rewrite using `[hxx]`.

Establish `hevf : (fun y => (ev n g ph r y : ℂ)) = fun y => (((fun t => Real.exp t - ε ^ 2) (lw n g ph r ε y) : ℝ) : ℂ)`. Use function extensionality and compare the values at `y`. Simplify using `only`. Unfold `lw`. Rewrite using `[Real.exp_log (by have := hev0 y; positivity)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hnT : ∀ x ξ, ‖dbarDot n z (fun y => (twist n g ph r ε y : ℂ)) x ξ‖ = kap n g ph r ε x / eta n g ph r ε x * ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖`. Introduce `x ξ`. Rewrite using `[htw, dual_dbarDot_comp_real n z _ (dualK_contDiff _) _ hlw1, dualK_deriv (by rw [← hxx]; exact (hB1 x).1)]`.

Rewrite using `[← hxx]`. Use `congr 1`. Rewrite using `[abs_of_nonneg]`. Both sides reduce to the same expression. Establish `h1` using `(hB1 x).1`.

Establish `h2` using `(hB1 x).2.1`. Unfold `eta at h2`. Check the signs of the components of the expression. Establish `hnE : ∀ x ξ, ‖dbarDot n z (fun y => (ev n g ph r y : ℂ)) x ξ‖ = (ev n g ph r x + ε ^ 2) * ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖`. Introduce `x ξ`.

Rewrite using `[hevf, dual_dbarDot_comp_real n z _ (Real.contDiff_exp.sub contDiff_const) _ hlw1]`. Use `congr 1`. Simplify using `only [deriv_sub_const, Real.deriv_exp]`. Unfold `lw`. Rewrite using `[Real.exp_log (by have := hev0 x; positivity), abs_of_nonneg (by have := hev0 x; positivity)]`.

Use `⟨fun x ξ => ?_, fun x ξ hx => ?_, fun x ξ hx => ?_⟩` and prove the remaining obligations. Rewrite using `[hnT] set X := xx n g ph r ε x set E := eta n g ph r ε x set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ set Θ := (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re`. Establish `h1` using `hT1 x ξ`. Establish `hX : 1 ≤ X` using `(hB1 x).1`. Establish `hE : 1 ≤ E` using `(hB1 x).2.1`.

Establish `hk : kap n g ph r ε x = 1 + 1 / X` using `rfl`. Establish `hb : bfun n g ph r ε x = (X + 1) ^ 2 / ((X + 1) ^ 2 + E)` using `rfl`. Rewrite `h1`, the goal using `[hk]`. Rewrite using `[hb]`. Establish `hid : ((1 + 1 / X) / E) ^ 2 = (X + 1) ^ 2 / ((X + 1) ^ 2 + E) * (1 / (X ^ 2 * E) + ((1 + 1 / X) / E) ^ 2)`.

Establish `: X ≠ 0` using `by positivity`. Establish `: E ≠ 0` using `by positivity`. Establish `: (X + 1) ^ 2 + E ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[mul_pow, hid, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left h1 (by positivity)`. Rewrite using `[hnT] set X := xx n g ph r ε x set E := eta n g ph r ε x set K := kap n g ph r ε x set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ set Θ := (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re`. Establish `h1` using `hT1 x ξ`. Establish `h2` using `hT2 x ξ hx`.

Establish `hX : 1 ≤ X` using `(hB1 x).1`. Establish `hE : 1 ≤ E` using `(hB1 x).2.1`. Establish `hK2 : K ≤ 2` using `(hB1 x).2.2.1`. Establish `hK1 : 1 ≤ K`. Establish `: K = 1 + 1 / X` using `rfl`.

Rewrite using `[this]`. Establish `: 0 < 1 / X` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hΘ : 0 ≤ Θ` using `le_trans (by positivity) h1`. Establish `hE0 : 0 < E` using `by linarith`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hnE] set E := eta n g ph r ε x set K := kap n g ph r ε x set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ set Θ := (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re`. Establish `h2` using `hT2 x ξ hx`. Establish `hK1 : 1 ≤ K`. Establish `: K = 1 + 1 / xx n g ph r ε x` using `rfl`.

Rewrite using `[this]`. Establish `: 0 < 1 / xx n g ph r ε x` using `by have := (hB1 x).1; positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hev` using `hev0 x`. Establish `hQ : (ev n g ph r x + ε ^ 2) ^ 2 ≤ 4 * ε ^ 4` using `by nlinarith`.

Establish `hD : D ^ 2 ≤ E * Θ` using `le_trans (le_mul_of_one_le_left (by positivity) hK1) h2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dual (n : ℕ) (M : Type u) [TopologicalSpace M]
    (hT : TwistLeviStatement n M) (hB : BasicStatement n M) : DualStatement n M := by
  intro z g ph ph2 r j ε δ hz hg hph hphL hph2 hph2L hr hj hε hδ hbd
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun x ξ => ?_, fun x ξ _ => ?_, fun x ξ _ => ?_⟩ <;> simp [dbarDot, Levi]
  obtain ⟨hB1, -, -, -⟩ := hB g ph ph2 r j ε δ hr hε hbd
  obtain ⟨-, -, hT1, hT2⟩ := hT z g ph ph2 r j ε δ hz hg hph hphL hph2 hph2L hr hj hε hδ hbd
  obtain ⟨hW, -, -, -⟩ := hT z g ph ph2 r j ε ε hz hg hph hphL hph2 hph2L hr hj hε hε hbd
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlw : SmoothR n z (lw n g ph r ε) := by
    have e : (fun y => (lw n g ph r ε y : ℂ)) = fun y => (1 / (n : ℂ)) *
        (((wgt n g ph ph2 r j ε y : ℝ) : ℂ) - (ph2 y : ℂ) - ((n : ℂ) + j) * (ph y : ℂ)) := by
      funext y
      unfold wgt
      push_cast
      field_simp
      ring
    unfold SmoothR
    rw [e]
    exact Smooth.mul _ _ _ _ (Smooth.const _ _ _)
      (Smooth.sub _ _ _ _ (Smooth.sub _ _ _ _ hW hph2) (Smooth.mul _ _ _ _ (Smooth.const _ _ _) hph))
  have hlw1 : CkR n z 1 (lw n g ph r ε) := SmoothR.ckR n z 1 _ hlw
  have hev0 : ∀ y, 0 ≤ ev n g ph r y := fun y => by unfold ev; positivity
  have hxx : ∀ y, xx n g ph r ε y = (1 + Real.log (1 + ε ^ 2)) - lw n g ph r ε y := fun y => rfl
  have htw : (fun y => (twist n g ph r ε y : ℂ)) =
      fun y => ((dualK (1 + Real.log (1 + ε ^ 2)) (lw n g ph r ε y) : ℝ) : ℂ) := by
    funext y
    rw [dualK_eq (by rw [← hxx]; linarith [(hB1 y).1])]
    unfold twist eta
    rw [hxx]
  have hevf : (fun y => (ev n g ph r y : ℂ)) =
      fun y => (((fun t => Real.exp t - ε ^ 2) (lw n g ph r ε y) : ℝ) : ℂ) := by
    funext y
    simp only
    unfold lw
    rw [Real.exp_log (by have := hev0 y; positivity)]
    push_cast
    ring
  have hnT : ∀ x ξ, ‖dbarDot n z (fun y => (twist n g ph r ε y : ℂ)) x ξ‖ =
      kap n g ph r ε x / eta n g ph r ε x * ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ := by
    intro x ξ
    rw [htw, dual_dbarDot_comp_real n z _ (dualK_contDiff _) _ hlw1,
      dualK_deriv (by rw [← hxx]; exact (hB1 x).1)]
    rw [← hxx]
    congr 1
    rw [abs_of_nonneg]
    · rfl
    · have h1 := (hB1 x).1
      have h2 := (hB1 x).2.1
      unfold eta at h2
      positivity
  have hnE : ∀ x ξ, ‖dbarDot n z (fun y => (ev n g ph r y : ℂ)) x ξ‖ =
      (ev n g ph r x + ε ^ 2) * ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ := by
    intro x ξ
    rw [hevf, dual_dbarDot_comp_real n z _ (Real.contDiff_exp.sub contDiff_const) _ hlw1]
    congr 1
    simp only [deriv_sub_const, Real.deriv_exp]
    unfold lw
    rw [Real.exp_log (by have := hev0 x; positivity), abs_of_nonneg (by have := hev0 x; positivity)]
  refine ⟨fun x ξ => ?_, fun x ξ hx => ?_, fun x ξ hx => ?_⟩
  · rw [hnT]
    set X := xx n g ph r ε x
    set E := eta n g ph r ε x
    set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖
    set Θ := (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re
    have h1 := hT1 x ξ
    have hX : 1 ≤ X := (hB1 x).1
    have hE : 1 ≤ E := (hB1 x).2.1
    have hk : kap n g ph r ε x = 1 + 1 / X := rfl
    have hb : bfun n g ph r ε x = (X + 1) ^ 2 / ((X + 1) ^ 2 + E) := rfl
    rw [hk] at h1 ⊢
    rw [hb]
    have hid : ((1 + 1 / X) / E) ^ 2 =
        (X + 1) ^ 2 / ((X + 1) ^ 2 + E) * (1 / (X ^ 2 * E) + ((1 + 1 / X) / E) ^ 2) := by
      have : X ≠ 0 := by positivity
      have : E ≠ 0 := by positivity
      have : (X + 1) ^ 2 + E ≠ 0 := by positivity
      field_simp
      ring
    rw [mul_pow, hid, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · rw [hnT]
    set X := xx n g ph r ε x
    set E := eta n g ph r ε x
    set K := kap n g ph r ε x
    set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖
    set Θ := (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re
    have h1 := hT1 x ξ
    have h2 := hT2 x ξ hx
    have hX : 1 ≤ X := (hB1 x).1
    have hE : 1 ≤ E := (hB1 x).2.1
    have hK2 : K ≤ 2 := (hB1 x).2.2.1
    have hK1 : 1 ≤ K := by
      have : K = 1 + 1 / X := rfl
      rw [this]
      have : 0 < 1 / X := by positivity
      linarith
    have hΘ : 0 ≤ Θ := le_trans (by positivity) h1
    have hE0 : 0 < E := by linarith
    calc (K / E * D) ^ 2 = K / E ^ 2 * (K * D ^ 2) := by field_simp
      _ ≤ K / E ^ 2 * (E * Θ) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = K / E * Θ := by field_simp
      _ ≤ 2 / E * Θ := mul_le_mul_of_nonneg_right (by gcongr) hΘ
  · rw [hnE]
    set E := eta n g ph r ε x
    set K := kap n g ph r ε x
    set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖
    set Θ := (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re
    have h2 := hT2 x ξ hx
    have hK1 : 1 ≤ K := by
      have : K = 1 + 1 / xx n g ph r ε x := rfl
      rw [this]
      have : 0 < 1 / xx n g ph r ε x := by have := (hB1 x).1; positivity
      linarith
    have hev := hev0 x
    have hQ : (ev n g ph r x + ε ^ 2) ^ 2 ≤ 4 * ε ^ 4 := by nlinarith
    have hD : D ^ 2 ≤ E * Θ := le_trans (le_mul_of_one_le_left (by positivity) hK1) h2
    calc ((ev n g ph r x + ε ^ 2) * D) ^ 2 = (ev n g ph r x + ε ^ 2) ^ 2 * D ^ 2 := by ring
      _ ≤ 4 * ε ^ 4 * D ^ 2 := mul_le_mul_of_nonneg_right hQ (by positivity)
      _ ≤ 4 * ε ^ 4 * (E * Θ) := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = 4 * ε ^ 4 * E * Θ := by ring

end

end ReciprocityTheory.L2DbarEstimates.I
