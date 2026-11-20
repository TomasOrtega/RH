import Formalism.HermitianCurvature.StatementB

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.B3

open Formalism.FourierDecayAlt.B

def pl (a b k x : ℝ) : ℝ := Real.smoothTransition (k * (x - a)) * Real.smoothTransition (k * (b - x))

/- English proof (translation)
Unfold `pl`. Conclude with `mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)`.
-/
lemma pl_nonneg (a b k x : ℝ) : 0 ≤ pl a b k x := by
  unfold pl
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

/- English proof (translation)
Unfold `pl`. Use polynomial arithmetic with `[Real.smoothTransition.nonneg (k * (x - a)), Real.smoothTransition.nonneg (k * (b - x)), Real.smoothTransition.le_one (k * (x - a)), Real.smoothTransition.le_one (k * (b - x))]`.
-/
lemma pl_le_one (a b k x : ℝ) : pl a b k x ≤ 1 := by
  unfold pl
  nlinarith [Real.smoothTransition.nonneg (k * (x - a)), Real.smoothTransition.nonneg (k * (b - x)),
    Real.smoothTransition.le_one (k * (x - a)), Real.smoothTransition.le_one (k * (b - x))]

/- English proof (translation)
Unfold `pl`. Conclude with `(Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))).mul (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id)))`.
-/
lemma pl_contDiff (a b k : ℝ) : ContDiff ℝ 2 (pl a b k) := by
  unfold pl
  exact (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id)))

/- English proof (translation)
Unfold `pl`. Rewrite `hx` using `[Set.mem_Ioo, not_and_or, not_lt, not_lt]`. Break down `hx with hx | hx` into its components or cases. Rewrite using `[Real.smoothTransition.zero_of_nonpos (show k * (x - a) ≤ 0 by nlinarith), zero_mul]`. Rewrite using `[Real.smoothTransition.zero_of_nonpos (show k * (b - x) ≤ 0 by nlinarith), mul_zero]`.
-/
lemma pl_eq_zero {a b k x : ℝ} (hk : 0 ≤ k) (hx : x ∉ Ioo a b) : pl a b k x = 0 := by
  unfold pl
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hx
  rcases hx with hx | hx
  · rw [Real.smoothTransition.zero_of_nonpos (show k * (x - a) ≤ 0 by nlinarith), zero_mul]
  · rw [Real.smoothTransition.zero_of_nonpos (show k * (b - x) ≤ 0 by nlinarith), mul_zero]

/- English proof (translation)
Unfold `pl`. Rewrite using `[Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, one_mul]`.
-/
lemma pl_eq_one {a b k x : ℝ} (h1 : 1 ≤ k * (x - a)) (h2 : 1 ≤ k * (b - x)) : pl a b k x = 1 := by
  unfold pl
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, one_mul]

/- English proof (translation)
Establish `hsub : Function.support (pl a b k) ⊆ Set.Icc a b`. Introduce `x hx`. Assume the negation of the conclusion as `h`. Conclude with `hx (pl_eq_zero hk (fun h' => h (Set.Ioo_subset_Icc_self h')))`. Use `⟨pl_contDiff a b k, HasCompactSupport.intro (isCompact_Icc (a := a) (b := b)) (fun x hx => ?_), ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Conclude with `hx (hsub h)`. Conclude with `(closure_minimal hsub isClosed_Icc).trans (fun x hx => lt_of_lt_of_le ha hx.1)`.
-/
lemma pl_isTest {a b k : ℝ} (ha : 0 < a) (hk : 0 ≤ k) : IsTest (pl a b k) := by
  have hsub : Function.support (pl a b k) ⊆ Set.Icc a b := by
    intro x hx
    by_contra h
    exact hx (pl_eq_zero hk (fun h' => h (Set.Ioo_subset_Icc_self h')))
  refine ⟨pl_contDiff a b k, HasCompactSupport.intro (isCompact_Icc (a := a) (b := b)) (fun x hx => ?_), ?_⟩
  · by_contra h
    exact hx (hsub h)
  · exact (closure_minimal hsub isClosed_Icc).trans (fun x hx => lt_of_lt_of_le ha hx.1)

/- English proof (translation)
Establish `hpos : 0 < 2 / a` using `div_pos two_pos ha`. Establish `h2a : 2 / a * (a / 2) = 1` using `by field_simp`. Apply `pl_eq_one` to reduce the goal to its premises. Use polynomial arithmetic with `[mul_nonneg hpos.le (by linarith [hx.1] : (0:ℝ) ≤ x - a / 2 - a / 2), hx.1]`. Use polynomial arithmetic with `[mul_nonneg hpos.le (by linarith [hx.2] : (0:ℝ) ≤ b + 1 - x), hx.2]`.
-/
lemma pl_big {a b x : ℝ} (ha : 0 < a) (hx : x ∈ Ioo a b) : pl (a / 2) (b + 1) (2 / a + 1) x = 1 := by
  have hpos : 0 < 2 / a := div_pos two_pos ha
  have h2a : 2 / a * (a / 2) = 1 := by field_simp
  apply pl_eq_one
  · nlinarith [mul_nonneg hpos.le (by linarith [hx.1] : (0:ℝ) ≤ x - a / 2 - a / 2), hx.1]
  · nlinarith [mul_nonneg hpos.le (by linarith [hx.2] : (0:ℝ) ≤ b + 1 - x), hx.2]

/- English proof (translation)
Establish `hxa : 0 < x - a` using `by linarith [hx.1]`. Establish `hbx : 0 < b - x` using `by linarith [hx.2]`. Take `⟨N, hN⟩` from `exists_nat_ge (max (1 / (x - a)) (1 / (b - x)))`. Use `filter_upwards [Filter.eventually_ge_atTop N] with n hn`. Establish `hn' : max (1 / (x - a)) (1 / (b - x)) ≤ (n : ℝ)` using `le_trans hN (by exact_mod_cast hn)`.

Apply `pl_eq_one` to reduce the goal to its premises. Establish `h1 : 1 / (x - a) * (x - a) ≤ (n : ℝ) * (x - a)` using `mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) hn') hxa.le`. Rewrite `h1` using `[one_div_mul_cancel hxa.ne']`. Then use the resulting hypothesis. Establish `h1 : 1 / (b - x) * (b - x) ≤ (n : ℝ) * (b - x)` using `mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) hn') hbx.le`. Rewrite `h1` using `[one_div_mul_cancel hbx.ne']`. Then use the resulting hypothesis.
-/
lemma pl_eventually {a b x : ℝ} (hx : x ∈ Ioo a b) : ∀ᶠ n : ℕ in atTop, pl a b n x = 1 := by
  have hxa : 0 < x - a := by linarith [hx.1]
  have hbx : 0 < b - x := by linarith [hx.2]
  obtain ⟨N, hN⟩ := exists_nat_ge (max (1 / (x - a)) (1 / (b - x)))
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hn' : max (1 / (x - a)) (1 / (b - x)) ≤ (n : ℝ) := le_trans hN (by exact_mod_cast hn)
  apply pl_eq_one
  · have h1 : 1 / (x - a) * (x - a) ≤ (n : ℝ) * (x - a) :=
      mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) hn') hxa.le
    rwa [one_div_mul_cancel hxa.ne'] at h1
  · have h1 : 1 / (b - x) * (b - x) ≤ (n : ℝ) * (b - x) :=
      mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) hn') hbx.le
    rwa [one_div_mul_cancel hbx.ne'] at h1

/- English proof (translation)
Rewrite `hτ` using `[Set.mem_prod, not_and_or]`. Break down `hτ with h | h` into its components or cases. Rewrite using `[pl_eq_zero hk h, zero_mul]`. Rewrite using `[pl_eq_zero hk h, mul_zero]`.
-/
lemma pl_prod_zero {a₁ b₁ a₂ b₂ k : ℝ} (hk : 0 ≤ k) {τ : ℝ × ℝ} (hτ : τ ∉ Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) :
    pl a₁ b₁ k τ.1 * pl a₂ b₂ k τ.2 = 0 := by
  rw [Set.mem_prod, not_and_or] at hτ
  rcases hτ with h | h
  · rw [pl_eq_zero hk h, zero_mul]
  · rw [pl_eq_zero hk h, mul_zero]

/- English proof (translation)
Unfold `Quad`. Conclude with `measurableSet_Ioi.prod measurableSet_Ioi`.
-/
lemma measurableSet_Quad : MeasurableSet Quad := by
  unfold Quad
  exact measurableSet_Ioi.prod measurableSet_Ioi

/- English proof (translation)
Establish `hx' : x ∉ tsupport w` using `fun h => (not_lt.2 hx) (hw.2.2 h)`. Assume the negation of the conclusion as `h`. Conclude with `hx' (subset_tsupport _ h)`.
-/
lemma test_zero {w : ℝ → ℝ} (hw : IsTest w) {x : ℝ} (hx : x ≤ 0) : w x = 0 := by
  have hx' : x ∉ tsupport w := fun h => (not_lt.2 hx) (hw.2.2 h)
  by_contra h
  exact hx' (subset_tsupport _ h)

/- English proof (translation)
Simplify using `only [Quad, Set.mem_prod, Set.mem_Ioi, not_and_or, not_lt] at hτ`. Break down `hτ with h | h` into its components or cases. Rewrite using `[test_zero h₁ h, zero_mul]`. Rewrite using `[test_zero h₂ h, mul_zero]`.
-/
lemma test_prod_zero {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) {τ : ℝ × ℝ} (hτ : τ ∉ Quad) :
    w₁ τ.1 * w₂ τ.2 = 0 := by
  simp only [Quad, Set.mem_prod, Set.mem_Ioi, not_and_or, not_lt] at hτ
  rcases hτ with h | h
  · rw [test_zero h₁ h, zero_mul]
  · rw [test_zero h₂ h, mul_zero]

/- English proof (translation)
Conclude with `ENNReal.measurable_ofReal.comp ((h₁.1.continuous.measurable.comp measurable_fst).mul (h₂.1.continuous.measurable.comp measurable_snd))`.
-/
lemma test_prod_measurable {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Measurable fun τ : ℝ × ℝ => ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) := by
  exact ENNReal.measurable_ofReal.comp ((h₁.1.continuous.measurable.comp measurable_fst).mul
    (h₂.1.continuous.measurable.comp measurable_snd))

def FinT (f : ℝ × ℝ → ℝ≥0∞) : Prop :=
  ∀ w₁ w₂ : ℝ → ℝ, IsTest w₁ → IsTest w₂ → (∀ x, 0 ≤ w₁ x) → (∀ x, 0 ≤ w₂ x) →
    (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * f τ ∂(volume.restrict Quad)) ≠ ∞

/- English proof (translation)
Distinguish the cases in `hτ : τ ∈ Ioo a₁ b₁ ×ˢ Ioo a₂ b₂`. Rewrite using `[Set.indicator_of_mem hτ, pl_big h₁ hτ.1, pl_big h₂ hτ.2, mul_one, ENNReal.ofReal_one, one_mul]`. Simplify using `[Set.indicator, hτ]`.
-/
lemma box_bound (f : ℝ × ℝ → ℝ≥0∞) {a₁ b₁ a₂ b₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) (τ : ℝ × ℝ) :
    (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂).indicator f τ ≤
      ENNReal.ofReal (pl (a₁ / 2) (b₁ + 1) (2 / a₁ + 1) τ.1 * pl (a₂ / 2) (b₂ + 1) (2 / a₂ + 1) τ.2) * f τ := by
  by_cases hτ : τ ∈ Ioo a₁ b₁ ×ˢ Ioo a₂ b₂
  · rw [Set.indicator_of_mem hτ, pl_big h₁ hτ.1, pl_big h₂ hτ.2, mul_one, ENNReal.ofReal_one, one_mul]
  · simp [Set.indicator, hτ]

/- English proof (translation)
Establish `hk₁ : (0:ℝ) ≤ 2 / a₁ + 1` using `by have := div_pos two_pos h₁; linarith`. Establish `hk₂ : (0:ℝ) ≤ 2 / a₂ + 1` using `by have := div_pos two_pos h₂; linarith`. Conclude with `hfin _ _ (pl_isTest (by linarith) hk₁) (pl_isTest (by linarith) hk₂) (pl_nonneg _ _ _) (pl_nonneg _ _ _)`.
-/
lemma bound_fin {f : ℝ × ℝ → ℝ≥0∞} (hfin : FinT f) {a₁ a₂ : ℝ} (b₁ b₂ : ℝ) (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    (∫⁻ τ, ENNReal.ofReal (pl (a₁ / 2) (b₁ + 1) (2 / a₁ + 1) τ.1 * pl (a₂ / 2) (b₂ + 1) (2 / a₂ + 1) τ.2) * f τ
      ∂(volume.restrict Quad)) ≠ ∞ := by
  have hk₁ : (0:ℝ) ≤ 2 / a₁ + 1 := by have := div_pos two_pos h₁; linarith
  have hk₂ : (0:ℝ) ≤ 2 / a₂ + 1 := by have := div_pos two_pos h₂; linarith
  exact hfin _ _ (pl_isTest (by linarith) hk₁) (pl_isTest (by linarith) hk₂) (pl_nonneg _ _ _) (pl_nonneg _ _ _)

/- English proof (translation)
Establish `hS : MeasurableSet (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂)` using `measurableSet_Ioo.prod measurableSet_Ioo`. Rewrite using `[withDensity_apply _ hS, ← lintegral_indicator (hs := hS)]`. Conclude with `ne_top_of_le_ne_top (bound_fin hfin b₁ b₂ h₁ h₂) (lintegral_mono (box_bound f h₁ h₂))`.
-/
lemma box_fin {f : ℝ × ℝ → ℝ≥0∞} (hfin : FinT f) {a₁ a₂ : ℝ} (b₁ b₂ : ℝ) (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    ((volume.restrict Quad).withDensity f) (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) ≠ ∞ := by
  have hS : MeasurableSet (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) := measurableSet_Ioo.prod measurableSet_Ioo
  rw [withDensity_apply _ hS, ← lintegral_indicator (hs := hS)]
  exact ne_top_of_le_ne_top (bound_fin hfin b₁ b₂ h₁ h₂) (lintegral_mono (box_bound f h₁ h₂))

/- English proof (translation)
Establish `hS : MeasurableSet (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂)` using `measurableSet_Ioo.prod measurableSet_Ioo`. Rewrite using `[withDensity_apply _ hS, ← lintegral_indicator (hs := hS)]`. Use `tendsto_lintegral_of_dominated_convergence' ((Ioo a₁ b₁ ×ˢ Ioo a₂ b₂).indicator f) (fun n => ?_) (fun n => ?_) ?_ ?_` and prove the remaining obligations. Conclude with `(ENNReal.measurable_ofReal.comp (((pl_contDiff a₁ b₁ n).continuous.measurable.comp measurable_fst).mul ((pl_contDiff a₂ b₂ n).continuous.measurable.comp measurable_snd))).aemeasurable.mul hf`. Use `ae_of_all _ (fun τ => ?_) dsimp only` and prove the remaining obligations.

Distinguish the cases in `hτ : τ ∈ Ioo a₁ b₁ ×ˢ Ioo a₂ b₂`. Rewrite using `[Set.indicator_of_mem hτ]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.ofReal_le_one]`. Use polynomial arithmetic with `[pl_le_one a₁ b₁ n τ.1, pl_nonneg a₁ b₁ n τ.1, pl_le_one a₂ b₂ n τ.2, pl_nonneg a₂ b₂ n τ.2]`.

Use `_ = f τ := one_mul _`. Rewrite using `[pl_prod_zero (Nat.cast_nonneg n) hτ, ENNReal.ofReal_zero, zero_mul]`. Simplify using the standard rewrite rules. Rewrite using `[lintegral_indicator (hs := hS), ← withDensity_apply _ hS]`. Conclude with `box_fin hfin b₁ b₂ h₁ h₂`.

Use `ae_of_all _ (fun τ => ?_)` and prove the remaining obligations. Distinguish the cases in `hτ : τ ∈ Ioo a₁ b₁ ×ˢ Ioo a₂ b₂`. Rewrite using `[Set.indicator_of_mem hτ]`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [pl_eventually hτ.1, pl_eventually hτ.2] with n h1 h2`.

Rewrite using `[h1, h2, mul_one, ENNReal.ofReal_one, one_mul]`. Establish `h0 : (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂).indicator f τ = 0` using `by simp [Set.indicator, hτ]`. Rewrite using `[h0]`. Use `tendsto_const_nhds.congr (fun n => ?_)` and prove the remaining obligations. Rewrite using `[pl_prod_zero (Nat.cast_nonneg n) hτ, ENNReal.ofReal_zero, zero_mul]`.
-/
lemma box_tendsto {f : ℝ × ℝ → ℝ≥0∞} (hf : AEMeasurable f (volume.restrict Quad)) (hfin : FinT f)
    {a₁ a₂ : ℝ} (b₁ b₂ : ℝ) (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    Tendsto (fun n : ℕ => ∫⁻ τ, ENNReal.ofReal (pl a₁ b₁ n τ.1 * pl a₂ b₂ n τ.2) * f τ ∂(volume.restrict Quad))
      atTop (𝓝 (((volume.restrict Quad).withDensity f) (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂))) := by
  have hS : MeasurableSet (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) := measurableSet_Ioo.prod measurableSet_Ioo
  rw [withDensity_apply _ hS, ← lintegral_indicator (hs := hS)]
  refine tendsto_lintegral_of_dominated_convergence' ((Ioo a₁ b₁ ×ˢ Ioo a₂ b₂).indicator f)
    (fun n => ?_) (fun n => ?_) ?_ ?_
  · exact (ENNReal.measurable_ofReal.comp
      (((pl_contDiff a₁ b₁ n).continuous.measurable.comp measurable_fst).mul
        ((pl_contDiff a₂ b₂ n).continuous.measurable.comp measurable_snd))).aemeasurable.mul hf
  · refine ae_of_all _ (fun τ => ?_)
    dsimp only
    by_cases hτ : τ ∈ Ioo a₁ b₁ ×ˢ Ioo a₂ b₂
    · rw [Set.indicator_of_mem hτ]
      calc ENNReal.ofReal (pl a₁ b₁ n τ.1 * pl a₂ b₂ n τ.2) * f τ ≤ 1 * f τ := by
            gcongr
            rw [ENNReal.ofReal_le_one]
            nlinarith [pl_le_one a₁ b₁ n τ.1, pl_nonneg a₁ b₁ n τ.1, pl_le_one a₂ b₂ n τ.2, pl_nonneg a₂ b₂ n τ.2]
        _ = f τ := one_mul _
    · rw [pl_prod_zero (Nat.cast_nonneg n) hτ, ENNReal.ofReal_zero, zero_mul]
      simp
  · rw [lintegral_indicator (hs := hS), ← withDensity_apply _ hS]
    exact box_fin hfin b₁ b₂ h₁ h₂
  · refine ae_of_all _ (fun τ => ?_)
    by_cases hτ : τ ∈ Ioo a₁ b₁ ×ˢ Ioo a₂ b₂
    · rw [Set.indicator_of_mem hτ]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [pl_eventually hτ.1, pl_eventually hτ.2] with n h1 h2
      rw [h1, h2, mul_one, ENNReal.ofReal_one, one_mul]
    · have h0 : (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂).indicator f τ = 0 := by simp [Set.indicator, hτ]
      rw [h0]
      refine tendsto_const_nhds.congr (fun n => ?_)
      rw [pl_prod_zero (Nat.cast_nonneg n) hτ, ENNReal.ofReal_zero, zero_mul]

/- English proof (translation)
Establish `hgfin : FinT g` using `fun w₁ w₂ h₁ h₂ p₁ p₂ => by`. Rewrite using `[← H w₁ w₂ h₁ h₂ p₁ p₂]`. Conclude with `hfin w₁ w₂ h₁ h₂ p₁ p₂`. Establish `box_eq : ∀ a₁ b₁ a₂ b₂ : ℝ, 0 < a₁ → 0 < a₂ → ((volume.restrict Quad).withDensity f) (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) = ((volume.restrict Quad).withDensity g) (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂)`. Introduce `a₁ b₁ a₂ b₂ h₁ h₂`.

Use `tendsto_nhds_unique (box_tendsto hf hfin b₁ b₂ h₁ h₂) ?_` and prove the remaining obligations. Use `(box_tendsto hg hgfin b₁ b₂ h₁ h₂).congr fun n => ?_` and prove the remaining obligations. Conclude with `(H _ _ (pl_isTest h₁ (Nat.cast_nonneg n)) (pl_isTest h₂ (Nat.cast_nonneg n)) (pl_nonneg _ _ _) (pl_nonneg _ _ _)).symm`. Establish `hcompl : ∀ h : ℝ × ℝ → ℝ≥0∞, ((volume.restrict Quad).withDensity h) Quadᶜ = 0`. Introduce `h`.

Apply `withDensity_absolutelyContinuous` to reduce the goal to its premises. Rewrite using `[Measure.restrict_apply measurableSet_Quad.compl, compl_inter_self, measure_empty]`. Set `B : ℕ → Set (ℝ × ℝ)` to `fun n => Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ×ˢ Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)`. Establish `hpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1)` using `fun n => by positivity`. Establish `key : (volume.restrict Quad).withDensity f = (volume.restrict Quad).withDensity g`.

Use `Measure.ext_of_generateFrom_of_cover (T := insert Quadᶜ (range B)) (generateFrom_eq_prod (Real.borel_eq_generateFrom_Ioo_rat ▸ (BorelSpace.measurable_eq (α := ℝ)).symm) (Real.borel_eq_generateFrom_Ioo_rat ▸ (BorelSpace.measurable_eq (α := ℝ)).symm) (Real.finiteSpanningSetsInIooRa …` and prove the remaining obligations. Use `eq_univ_of_forall fun τ => ?_` and prove the remaining obligations. Distinguish the cases in `hτ : τ ∈ Quad`. Take `⟨n, hn⟩` from `exists_nat_gt (max (max (1 / τ.1) (1 / τ.2)) (max τ.1 τ.2))`. Simplify using `only [max_lt_iff] at hn`.

Take `⟨⟨n1, n2⟩, n3, n4⟩` from `hn`. Establish `h1 : 0 < τ.1` using `hτ.1`. Establish `h2 : 0 < τ.2` using `hτ.2`. Establish `hn0 : (0 : ℝ) < (n : ℝ) + 1` using `by positivity`. Use `mem_sUnion.mpr ⟨B n, Or.inr ⟨n, rfl⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Conclude with `(one_div_lt h1 hn0).mp (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(one_div_lt h2 hn0).mp (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `mem_sUnion.mpr ⟨Quadᶜ, Or.inl rfl, hτ⟩`.

Introduce and unpack `t (rfl | ⟨n, rfl⟩)`. Rewrite using `[hcompl]`. Conclude with `ENNReal.zero_ne_top`. Conclude with `box_fin hfin _ _ (hpos n) (hpos n)`. Introduce and unpack `t (rfl | ⟨n, rfl⟩) s hs`.

Rewrite using `[measure_mono_null inter_subset_right (hcompl f), measure_mono_null inter_subset_right (hcompl g)]`. Take `⟨s₁, hs₁, s₂, hs₂, rfl⟩` from `hs`. Simplify using `only [mem_iUnion, mem_singleton_iff] at hs₁ hs₂`. Take `⟨l₁, u₁, -, rfl⟩` from `hs₁`. Take `⟨l₂, u₂, -, rfl⟩` from `hs₂`.

Simplify using `only [B]`. Rewrite using `[prod_inter_prod, Ioo_inter_Ioo, Ioo_inter_Ioo]`. Conclude with `box_eq _ _ _ _ (lt_max_of_lt_right (hpos n)) (lt_max_of_lt_right (hpos n))`. Introduce and unpack `t (rfl | ⟨n, rfl⟩)`. Rewrite using `[hcompl, hcompl]`.

Conclude with `box_eq _ _ _ _ (hpos n) (hpos n)`. Conclude with `(withDensity_eq_iff_of_sigmaFinite hf hg).mp key`.
-/
lemma ae_eq_of_tests {f g : ℝ × ℝ → ℝ≥0∞} (hf : AEMeasurable f (volume.restrict Quad))
    (hg : AEMeasurable g (volume.restrict Quad)) (hfin : FinT f)
    (H : ∀ w₁ w₂ : ℝ → ℝ, IsTest w₁ → IsTest w₂ → (∀ x, 0 ≤ w₁ x) → (∀ x, 0 ≤ w₂ x) →
      (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * f τ ∂(volume.restrict Quad)) =
        ∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * g τ ∂(volume.restrict Quad)) :
    f =ᵐ[volume.restrict Quad] g := by
  have hgfin : FinT g := fun w₁ w₂ h₁ h₂ p₁ p₂ => by
    rw [← H w₁ w₂ h₁ h₂ p₁ p₂]
    exact hfin w₁ w₂ h₁ h₂ p₁ p₂
  have box_eq : ∀ a₁ b₁ a₂ b₂ : ℝ, 0 < a₁ → 0 < a₂ →
      ((volume.restrict Quad).withDensity f) (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) =
        ((volume.restrict Quad).withDensity g) (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) := by
    intro a₁ b₁ a₂ b₂ h₁ h₂
    refine tendsto_nhds_unique (box_tendsto hf hfin b₁ b₂ h₁ h₂) ?_
    refine (box_tendsto hg hgfin b₁ b₂ h₁ h₂).congr fun n => ?_
    exact (H _ _ (pl_isTest h₁ (Nat.cast_nonneg n)) (pl_isTest h₂ (Nat.cast_nonneg n))
      (pl_nonneg _ _ _) (pl_nonneg _ _ _)).symm
  have hcompl : ∀ h : ℝ × ℝ → ℝ≥0∞, ((volume.restrict Quad).withDensity h) Quadᶜ = 0 := by
    intro h
    apply withDensity_absolutelyContinuous
    rw [Measure.restrict_apply measurableSet_Quad.compl, compl_inter_self, measure_empty]
  let B : ℕ → Set (ℝ × ℝ) := fun n => Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ×ˢ Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)
  have hpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have key : (volume.restrict Quad).withDensity f = (volume.restrict Quad).withDensity g := by
    refine Measure.ext_of_generateFrom_of_cover (T := insert Quadᶜ (range B))
      (generateFrom_eq_prod (Real.borel_eq_generateFrom_Ioo_rat ▸ (BorelSpace.measurable_eq (α := ℝ)).symm)
        (Real.borel_eq_generateFrom_Ioo_rat ▸ (BorelSpace.measurable_eq (α := ℝ)).symm)
        (Real.finiteSpanningSetsInIooRat volume).isCountablySpanning
        (Real.finiteSpanningSetsInIooRat volume).isCountablySpanning).symm
      ((countable_range B).insert _) (Real.isPiSystem_Ioo_rat.prod Real.isPiSystem_Ioo_rat) ?_ ?_ ?_ ?_
    · refine eq_univ_of_forall fun τ => ?_
      by_cases hτ : τ ∈ Quad
      · obtain ⟨n, hn⟩ := exists_nat_gt (max (max (1 / τ.1) (1 / τ.2)) (max τ.1 τ.2))
        simp only [max_lt_iff] at hn
        obtain ⟨⟨n1, n2⟩, n3, n4⟩ := hn
        have h1 : 0 < τ.1 := hτ.1
        have h2 : 0 < τ.2 := hτ.2
        have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        refine mem_sUnion.mpr ⟨B n, Or.inr ⟨n, rfl⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · exact (one_div_lt h1 hn0).mp (by linarith)
        · linarith
        · exact (one_div_lt h2 hn0).mp (by linarith)
        · linarith
      · exact mem_sUnion.mpr ⟨Quadᶜ, Or.inl rfl, hτ⟩
    · rintro t (rfl | ⟨n, rfl⟩)
      · rw [hcompl]; exact ENNReal.zero_ne_top
      · exact box_fin hfin _ _ (hpos n) (hpos n)
    · rintro t (rfl | ⟨n, rfl⟩) s hs
      · rw [measure_mono_null inter_subset_right (hcompl f), measure_mono_null inter_subset_right (hcompl g)]
      · obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hs
        simp only [mem_iUnion, mem_singleton_iff] at hs₁ hs₂
        obtain ⟨l₁, u₁, -, rfl⟩ := hs₁
        obtain ⟨l₂, u₂, -, rfl⟩ := hs₂
        simp only [B]
        rw [prod_inter_prod, Ioo_inter_Ioo, Ioo_inter_Ioo]
        exact box_eq _ _ _ _ (lt_max_of_lt_right (hpos n)) (lt_max_of_lt_right (hpos n))
    · rintro t (rfl | ⟨n, rfl⟩)
      · rw [hcompl, hcompl]
      · exact box_eq _ _ _ _ (hpos n) (hpos n)
  exact (withDensity_eq_iff_of_sigmaFinite hf hg).mp key

/- English proof (translation)
Rewrite using `[← lintegral_indicator (hs := measurableSet_Quad)]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Distinguish the cases in `hτ : τ ∈ Quad`. Rewrite using `[Set.indicator_of_mem hτ]`.

Rewrite using `[test_prod_zero h₁ h₂ hτ, ENNReal.ofReal_zero, zero_mul]`. Simplify using `[Set.indicator, hτ]`.
-/
lemma lintegral_test_restrict {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) (F : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ τ : ℝ × ℝ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * F τ) =
      ∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * F τ ∂(volume.restrict Quad) := by
  rw [← lintegral_indicator (hs := measurableSet_Quad)]
  congr 1
  funext τ
  by_cases hτ : τ ∈ Quad
  · rw [Set.indicator_of_mem hτ]
  · rw [test_prod_zero h₁ h₂ hτ, ENNReal.ofReal_zero, zero_mul]
    simp [Set.indicator, hτ]

/- English proof (translation)
Establish `hK : IsCompact (tsupport w₁ ×ˢ tsupport w₂)` using `h₁.2.1.isCompact.prod h₂.2.1.isCompact`. Establish `hKQ : tsupport w₁ ×ˢ tsupport w₂ ⊆ Quad` using `prod_mono h₁.2.2 h₂.2.2`. Establish `hc : ContinuousOn (fun τ : ℝ × ℝ => (w₁ τ.1 * w₂ τ.2) • h τ) (tsupport w₁ ×ˢ tsupport w₂)` using `(((h₁.1.continuous.comp continuous_fst).mul (h₂.1.continuous.comp continuous_snd)).continuousOn).smul (hh.mono hKQ)`. Establish `hs : Function.support (fun τ : ℝ × ℝ => (w₁ τ.1 * w₂ τ.2) • h τ) ⊆ tsupport w₁ ×ˢ tsupport w₂`. Introduce `τ hτ`.

Use `⟨subset_tsupport _ fun h0 => hτ ?_, subset_tsupport _ fun h0 => hτ ?_⟩` and prove the remaining obligations. Simplify using `[h0]`. Simplify using `[h0]`. Conclude with `((integrableOn_iff_integrable_of_support_subset hs).mp (hc.integrableOn_compact hK)).restrict`.
-/
lemma integrable_test {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁)
    (h₂ : IsTest w₂) {h : ℝ × ℝ → E} (hh : ContinuousOn h Quad) :
    Integrable (fun τ : ℝ × ℝ => (w₁ τ.1 * w₂ τ.2) • h τ) (volume.restrict Quad) := by
  have hK : IsCompact (tsupport w₁ ×ˢ tsupport w₂) := h₁.2.1.isCompact.prod h₂.2.1.isCompact
  have hKQ : tsupport w₁ ×ˢ tsupport w₂ ⊆ Quad := prod_mono h₁.2.2 h₂.2.2
  have hc : ContinuousOn (fun τ : ℝ × ℝ => (w₁ τ.1 * w₂ τ.2) • h τ) (tsupport w₁ ×ˢ tsupport w₂) :=
    (((h₁.1.continuous.comp continuous_fst).mul (h₂.1.continuous.comp continuous_snd)).continuousOn).smul
      (hh.mono hKQ)
  have hs : Function.support (fun τ : ℝ × ℝ => (w₁ τ.1 * w₂ τ.2) • h τ) ⊆ tsupport w₁ ×ˢ tsupport w₂ := by
    intro τ hτ
    refine ⟨subset_tsupport _ fun h0 => hτ ?_, subset_tsupport _ fun h0 => hτ ?_⟩
    · simp [h0]
    · simp [h0]
  exact ((integrableOn_iff_integrable_of_support_subset hs).mp (hc.integrableOn_compact hK)).restrict

/- English proof (translation)
Rewrite using `[ofReal_integral_eq_lintegral_ofReal (by simpa using integrable_test h₁ h₂ hh) (Eventually.of_forall fun τ => mul_nonneg (mul_nonneg (p₁ _) (p₂ _)) (h0 τ))]`. Use `lintegral_congr fun τ => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_mul (mul_nonneg (p₁ _) (p₂ _))]`.
-/
lemma lintegral_test_cont {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) (p₁ : ∀ x, 0 ≤ w₁ x) (p₂ : ∀ x, 0 ≤ w₂ x)
    {h : ℝ × ℝ → ℝ} (hh : ContinuousOn h Quad) (h0 : ∀ τ, 0 ≤ h τ) :
    (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * ENNReal.ofReal (h τ) ∂(volume.restrict Quad)) =
      ENNReal.ofReal (∫ τ, w₁ τ.1 * w₂ τ.2 * h τ ∂(volume.restrict Quad)) := by
  rw [ofReal_integral_eq_lintegral_ofReal (by simpa using integrable_test h₁ h₂ hh)
    (Eventually.of_forall fun τ => mul_nonneg (mul_nonneg (p₁ _) (p₂ _)) (h0 τ))]
  refine lintegral_congr fun τ => ?_
  rw [ENNReal.ofReal_mul (mul_nonneg (p₁ _) (p₂ _))]

/- English proof (translation)
Use `(continuous_id.max continuous_const : Continuous fun y : ℝ => max y 0).comp_continuousOn hh` as an intermediate fact. Conclude with `this`.
-/
lemma contOn_pos {h : ℝ × ℝ → ℝ} (hh : ContinuousOn h Quad) : ContinuousOn (fun τ => max (h τ) 0) Quad := by
  have := (continuous_id.max continuous_const : Continuous fun y : ℝ => max y 0).comp_continuousOn hh
  exact this

/- English proof (translation)
Use `(continuous_neg.max continuous_const : Continuous fun y : ℝ => max (-y) 0).comp_continuousOn hh` as an intermediate fact. Conclude with `this`.
-/
lemma contOn_neg {h : ℝ × ℝ → ℝ} (hh : ContinuousOn h Quad) : ContinuousOn (fun τ => max (-h τ) 0) Quad := by
  have := (continuous_neg.max continuous_const : Continuous fun y : ℝ => max (-y) 0).comp_continuousOn hh
  exact this

/- English proof (translation)
Rewrite using `[← integral_sub (by simpa using integrable_test h₁ h₂ (contOn_pos hh)) (by simpa using integrable_test h₁ h₂ (contOn_neg hh))]`. Use `integral_congr_ae (Eventually.of_forall fun τ => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← mul_sub, max_zero_sub_max_neg_zero_eq_self]`.
-/
lemma integral_test_parts {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂)
    {h : ℝ × ℝ → ℝ} (hh : ContinuousOn h Quad) :
    (∫ τ, w₁ τ.1 * w₂ τ.2 * h τ ∂(volume.restrict Quad)) =
      (∫ τ, w₁ τ.1 * w₂ τ.2 * max (h τ) 0 ∂(volume.restrict Quad)) -
        ∫ τ, w₁ τ.1 * w₂ τ.2 * max (-h τ) 0 ∂(volume.restrict Quad) := by
  rw [← integral_sub (by simpa using integrable_test h₁ h₂ (contOn_pos hh))
    (by simpa using integrable_test h₁ h₂ (contOn_neg hh))]
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only
  rw [← mul_sub, max_zero_sub_max_neg_zero_eq_self]

end Formalism.FourierDecayAlt.P.B3

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B3

/- English proof (translation)
Introduce `b c hb hc H`. Establish `hre : ContinuousOn (fun τ => (c τ).re) Quad` using `Complex.continuous_re.comp_continuousOn hc`. Establish `him : ContinuousOn (fun τ => (c τ).im) Quad` using `Complex.continuous_im.comp_continuousOn hc`. Establish `mO : ∀ h : ℝ × ℝ → ℝ, ContinuousOn h Quad → AEMeasurable (fun τ => ENNReal.ofReal (h τ)) (volume.restrict Quad)` using `fun h hh => (hh.aemeasurable measurableSet_Quad).ennreal_ofReal`. Establish `R : ∀ w₁ w₂ : ℝ → ℝ, IsTest w₁ → IsTest w₂ → (∀ x, 0 ≤ w₁ x) → (∀ x, 0 ≤ w₂ x) → (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * b τ ∂(volume.restrict Quad)) ≠ ∞ ∧ (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * b τ ∂(volume.restrict Quad)).toReal = (∫ τ, w₁ τ.1 * w₂ τ.2 * (c τ).re ∂(volume. …`.

Introduce `w₁ w₂ h₁ h₂ p₁ p₂`. Take `⟨hfin, heq⟩` from `H w₁ w₂ h₁ h₂ p₁ p₂`. Rewrite `hfin`, `heq` using `[lintegral_test_restrict h₁ h₂ b]`. Establish `hint : Integrable (fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * c τ) (volume.restrict Quad)`. Simplify `integrable_test h₁ h₂ hc` using `only [Complex.real_smul]`.

Establish `hres : (∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * c τ) = ∫ τ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * c τ ∂(volume.restrict Quad)`. Use `(setIntegral_eq_integral_of_forall_compl_eq_zero fun τ hτ => ?_).symm` and prove the remaining obligations. Rewrite using `[test_prod_zero h₁ h₂ hτ]`. Simplify using the standard rewrite rules. Rewrite `heq` using `[hres]`.

Use `⟨hfin, ?_, ?_⟩` and prove the remaining obligations. Use `congrArg Complex.re heq` as an intermediate fact. Rewrite `this` using `[Complex.ofReal_re]`. Rewrite using `[this, ← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hint]`. Use `integral_congr_ae (Eventually.of_forall fun τ => ?_)` and prove the remaining obligations.

Simplify using `only [Complex.reCLM_apply, Complex.re_ofReal_mul]`. Use `congrArg Complex.im heq` as an intermediate fact. Rewrite `this` using `[Complex.ofReal_im]`. Rewrite using `[this, ← Complex.imCLM_apply, ← Complex.imCLM.integral_comp_comm hint]`. Use `integral_congr_ae (Eventually.of_forall fun τ => ?_)` and prove the remaining obligations.

Simplify using `only [Complex.imCLM_apply, Complex.im_ofReal_mul]`. Establish `split : ∀ w₁ w₂ : ℝ → ℝ, IsTest w₁ → IsTest w₂ → (∀ x, 0 ≤ w₁ x) → (∀ x, 0 ≤ w₂ x) → (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * (b τ + ENNReal.ofReal (max (-(c τ).re) 0)) ∂(volume.restrict Quad)) = ENNReal.ofReal (∫ τ, w₁ τ.1 * w₂ τ.2 * max (c τ).re 0 ∂(volume.restrict Quad))`. Introduce `w₁ w₂ h₁ h₂ p₁ p₂`. Take `⟨hfin, h1, -⟩` from `R w₁ w₂ h₁ h₂ p₁ p₂`. Establish `hm : AEMeasurable (fun τ : ℝ × ℝ => ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * b τ) (volume.restrict Quad)` using `(test_prod_measurable h₁ h₂).aemeasurable.mul hb`.

Simplify using `only [mul_add]`. Rewrite using `[lintegral_add_left' hm, lintegral_test_cont h₁ h₂ p₁ p₂ (contOn_neg hre) (fun τ => le_max_right _ _), ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_add ENNReal.toReal_nonneg (integral_nonneg fun τ => mul_nonneg (mul_nonneg (p₁ _) (p₂ _)) (le_max_right _ _)), h1, integral_test_p …`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `A : (fun τ => b τ + ENNReal.ofReal (max (-(c τ).re) 0)) =ᵐ[volume.restrict Quad] fun τ => ENNReal.ofReal (max (c τ).re 0)`.

Use `ae_eq_of_tests (hb.add (mO _ (contOn_neg hre))) (mO _ (contOn_pos hre)) ?_ ?_` and prove the remaining obligations. Introduce `w₁ w₂ h₁ h₂ p₁ p₂`. Rewrite using `[split w₁ w₂ h₁ h₂ p₁ p₂]`. Conclude with `ENNReal.ofReal_ne_top`. Introduce `w₁ w₂ h₁ h₂ p₁ p₂`.

Rewrite using `[split w₁ w₂ h₁ h₂ p₁ p₂, lintegral_test_cont h₁ h₂ p₁ p₂ (contOn_pos hre) (fun τ => le_max_right _ _)]`. Establish `B : (fun τ => ENNReal.ofReal (max (c τ).im 0)) =ᵐ[volume.restrict Quad] fun τ => ENNReal.ofReal (max (-(c τ).im) 0)`. Use `ae_eq_of_tests (mO _ (contOn_pos him)) (mO _ (contOn_neg him)) ?_ ?_` and prove the remaining obligations. Introduce `w₁ w₂ h₁ h₂ p₁ p₂`. Rewrite using `[lintegral_test_cont h₁ h₂ p₁ p₂ (contOn_pos him) (fun τ => le_max_right _ _)]`.

Conclude with `ENNReal.ofReal_ne_top`. Introduce `w₁ w₂ h₁ h₂ p₁ p₂`. Take `⟨-, -, h2⟩` from `R w₁ w₂ h₁ h₂ p₁ p₂`. Rewrite using `[lintegral_test_cont h₁ h₂ p₁ p₂ (contOn_pos him) (fun τ => le_max_right _ _), lintegral_test_cont h₁ h₂ p₁ p₂ (contOn_neg him) (fun τ => le_max_right _ _)]`. Use `congr 1`.

Rewrite `h2` using `[integral_test_parts h₁ h₂ him]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `filter_upwards [A, B] with τ hA hB`. Establish `hbt : b τ ≠ ∞`. Introduce `h`.

Rewrite `hA` using `[h, top_add]`. Conclude with `ENNReal.ofReal_ne_top hA.symm`. Establish `h1 : (b τ).toReal + max (-(c τ).re) 0 = max (c τ).re 0`. Use `congrArg ENNReal.toReal hA` as an intermediate fact. Rewrite `this` using `[ENNReal.toReal_add hbt ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (le_max_right _ _), ENNReal.toReal_ofReal (le_max_right _ _)]`. Then use the resulting hypothesis.

Establish `h2 : max (c τ).im 0 = max (-(c τ).im) 0` using `(ENNReal.ofReal_eq_ofReal_iff (le_max_right _ _) (le_max_right _ _)).mp hB`. Establish `e1` using `max_zero_sub_max_neg_zero_eq_self (c τ).re`. Establish `e2` using `max_zero_sub_max_neg_zero_eq_self (c τ).im`. Use `⟨hbt, Complex.ext ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Complex.ofReal_re]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Complex.ofReal_im]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ae_equality_from_test_functions : Formalism.FourierDecayAlt.B.AeFromTests := by
  intro b c hb hc H
  have hre : ContinuousOn (fun τ => (c τ).re) Quad := Complex.continuous_re.comp_continuousOn hc
  have him : ContinuousOn (fun τ => (c τ).im) Quad := Complex.continuous_im.comp_continuousOn hc
  have mO : ∀ h : ℝ × ℝ → ℝ, ContinuousOn h Quad →
      AEMeasurable (fun τ => ENNReal.ofReal (h τ)) (volume.restrict Quad) := fun h hh =>
    (hh.aemeasurable measurableSet_Quad).ennreal_ofReal

  have R : ∀ w₁ w₂ : ℝ → ℝ, IsTest w₁ → IsTest w₂ → (∀ x, 0 ≤ w₁ x) → (∀ x, 0 ≤ w₂ x) →
      (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * b τ ∂(volume.restrict Quad)) ≠ ∞ ∧
      (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * b τ ∂(volume.restrict Quad)).toReal =
        (∫ τ, w₁ τ.1 * w₂ τ.2 * (c τ).re ∂(volume.restrict Quad)) ∧
      (0 : ℝ) = ∫ τ, w₁ τ.1 * w₂ τ.2 * (c τ).im ∂(volume.restrict Quad) := by
    intro w₁ w₂ h₁ h₂ p₁ p₂
    obtain ⟨hfin, heq⟩ := H w₁ w₂ h₁ h₂ p₁ p₂
    rw [lintegral_test_restrict h₁ h₂ b] at hfin heq
    have hint : Integrable (fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * c τ) (volume.restrict Quad) := by
      simpa only [Complex.real_smul] using integrable_test h₁ h₂ hc
    have hres : (∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * c τ) =
        ∫ τ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * c τ ∂(volume.restrict Quad) := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun τ hτ => ?_).symm
      rw [test_prod_zero h₁ h₂ hτ]
      simp
    rw [hres] at heq
    refine ⟨hfin, ?_, ?_⟩
    · have := congrArg Complex.re heq
      rw [Complex.ofReal_re] at this
      rw [this, ← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hint]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only [Complex.reCLM_apply, Complex.re_ofReal_mul]
    · have := congrArg Complex.im heq
      rw [Complex.ofReal_im] at this
      rw [this, ← Complex.imCLM_apply, ← Complex.imCLM.integral_comp_comm hint]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only [Complex.imCLM_apply, Complex.im_ofReal_mul]

  have split : ∀ w₁ w₂ : ℝ → ℝ, IsTest w₁ → IsTest w₂ → (∀ x, 0 ≤ w₁ x) → (∀ x, 0 ≤ w₂ x) →
      (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * (b τ + ENNReal.ofReal (max (-(c τ).re) 0))
        ∂(volume.restrict Quad)) =
        ENNReal.ofReal (∫ τ, w₁ τ.1 * w₂ τ.2 * max (c τ).re 0 ∂(volume.restrict Quad)) := by
    intro w₁ w₂ h₁ h₂ p₁ p₂
    obtain ⟨hfin, h1, -⟩ := R w₁ w₂ h₁ h₂ p₁ p₂
    have hm : AEMeasurable (fun τ : ℝ × ℝ => ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * b τ) (volume.restrict Quad) :=
      (test_prod_measurable h₁ h₂).aemeasurable.mul hb
    simp only [mul_add]
    rw [lintegral_add_left' hm,
      lintegral_test_cont h₁ h₂ p₁ p₂ (contOn_neg hre) (fun τ => le_max_right _ _),
      ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_add ENNReal.toReal_nonneg
        (integral_nonneg fun τ => mul_nonneg (mul_nonneg (p₁ _) (p₂ _)) (le_max_right _ _)),
      h1, integral_test_parts h₁ h₂ hre]
    congr 1
    ring
  have A : (fun τ => b τ + ENNReal.ofReal (max (-(c τ).re) 0)) =ᵐ[volume.restrict Quad]
      fun τ => ENNReal.ofReal (max (c τ).re 0) := by
    refine ae_eq_of_tests (hb.add (mO _ (contOn_neg hre))) (mO _ (contOn_pos hre)) ?_ ?_
    · intro w₁ w₂ h₁ h₂ p₁ p₂
      rw [split w₁ w₂ h₁ h₂ p₁ p₂]
      exact ENNReal.ofReal_ne_top
    · intro w₁ w₂ h₁ h₂ p₁ p₂
      rw [split w₁ w₂ h₁ h₂ p₁ p₂, lintegral_test_cont h₁ h₂ p₁ p₂ (contOn_pos hre) (fun τ => le_max_right _ _)]

  have B : (fun τ => ENNReal.ofReal (max (c τ).im 0)) =ᵐ[volume.restrict Quad]
      fun τ => ENNReal.ofReal (max (-(c τ).im) 0) := by
    refine ae_eq_of_tests (mO _ (contOn_pos him)) (mO _ (contOn_neg him)) ?_ ?_
    · intro w₁ w₂ h₁ h₂ p₁ p₂
      rw [lintegral_test_cont h₁ h₂ p₁ p₂ (contOn_pos him) (fun τ => le_max_right _ _)]
      exact ENNReal.ofReal_ne_top
    · intro w₁ w₂ h₁ h₂ p₁ p₂
      obtain ⟨-, -, h2⟩ := R w₁ w₂ h₁ h₂ p₁ p₂
      rw [lintegral_test_cont h₁ h₂ p₁ p₂ (contOn_pos him) (fun τ => le_max_right _ _),
        lintegral_test_cont h₁ h₂ p₁ p₂ (contOn_neg him) (fun τ => le_max_right _ _)]
      congr 1
      rw [integral_test_parts h₁ h₂ him] at h2
      linarith
  filter_upwards [A, B] with τ hA hB
  have hbt : b τ ≠ ∞ := by
    intro h
    rw [h, top_add] at hA
    exact ENNReal.ofReal_ne_top hA.symm
  have h1 : (b τ).toReal + max (-(c τ).re) 0 = max (c τ).re 0 := by
    have := congrArg ENNReal.toReal hA
    rwa [ENNReal.toReal_add hbt ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (le_max_right _ _),
      ENNReal.toReal_ofReal (le_max_right _ _)] at this
  have h2 : max (c τ).im 0 = max (-(c τ).im) 0 :=
    (ENNReal.ofReal_eq_ofReal_iff (le_max_right _ _) (le_max_right _ _)).mp hB
  have e1 := max_zero_sub_max_neg_zero_eq_self (c τ).re
  have e2 := max_zero_sub_max_neg_zero_eq_self (c τ).im
  refine ⟨hbt, Complex.ext ?_ ?_⟩
  · rw [Complex.ofReal_re]
    linarith
  · rw [Complex.ofReal_im]
    linarith

end Formalism.FourierDecayAlt.P
