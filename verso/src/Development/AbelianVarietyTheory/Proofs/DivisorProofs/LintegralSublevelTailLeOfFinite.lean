import Mathlib
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory

/- English proof (translation)
Establish `hms : ∀ T : ℝ, MeasurableSet {y | x y ≤ -T + 1}` using `fun T => measurableSet_le hx measurable_const`. Use `haveI : IsFiniteMeasure (μ.withDensity g) := isFiniteMeasure_withDensity hg.ne`. Establish `hanti : Antitone (fun n : ℕ => {y | x y ≤ -(n : ℝ) + 1})`. Introduce `a b hab y hy`. Establish `: (a : ℝ) ≤ b` using `by exact_mod_cast hab`.

Simplify using `only [Set.mem_setOf_eq] at hy ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h` using `tendsto_measure_iInter_atTop (μ := μ.withDensity g) (fun n : ℕ => (hms n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩`. Establish `hem : (⋂ n : ℕ, {y | x y ≤ -(n : ℝ) + 1}) = ∅`. Use extensionality with `y`.

Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall, not_le]`. Take `⟨n, hn⟩` from `exists_nat_gt (1 - x y)`. Conclude with `⟨n, by linarith⟩`. Rewrite `h` using `[hem, measure_empty]`. Take `⟨n, hn⟩` from `(h.eventually (ge_mem_nhds hε)).exists`.

Use `⟨n, fun T hT => ?_⟩` and prove the remaining obligations. Rewrite using `[← withDensity_apply _ (hms T)]`. Use `le_trans (measure_mono ?_) hn` and prove the remaining obligations. Introduce `y hy`. Simplify using `only [Set.mem_setOf_eq] at hy ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lintegral_sublevel_tail_le (Y : Type) [MeasurableSpace Y] (μ : Measure Y) (g : Y → ℝ≥0∞)
    (x : Y → ℝ) (hx : Measurable x) (hg : ∫⁻ y, g y ∂μ < ⊤) (_hm : Measurable g)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ T0 : ℝ, ∀ T, T0 ≤ T → ∫⁻ y in {y | x y ≤ -T + 1}, g y ∂μ ≤ ε := by
  have hms : ∀ T : ℝ, MeasurableSet {y | x y ≤ -T + 1} := fun T =>
    measurableSet_le hx measurable_const
  haveI : IsFiniteMeasure (μ.withDensity g) := isFiniteMeasure_withDensity hg.ne
  have hanti : Antitone (fun n : ℕ => {y | x y ≤ -(n : ℝ) + 1}) := by
    intro a b hab y hy
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    simp only [Set.mem_setOf_eq] at hy ⊢
    linarith
  have h := tendsto_measure_iInter_atTop (μ := μ.withDensity g)
    (fun n : ℕ => (hms n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have hem : (⋂ n : ℕ, {y | x y ≤ -(n : ℝ) + 1}) = ∅ := by
    ext y
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_le]
    obtain ⟨n, hn⟩ := exists_nat_gt (1 - x y)
    exact ⟨n, by linarith⟩
  rw [hem, measure_empty] at h
  obtain ⟨n, hn⟩ := (h.eventually (ge_mem_nhds hε)).exists
  refine ⟨n, fun T hT => ?_⟩
  rw [← withDensity_apply _ (hms T)]
  refine le_trans (measure_mono ?_) hn
  intro y hy
  simp only [Set.mem_setOf_eq] at hy ⊢
  linarith

end GlobalTheory
