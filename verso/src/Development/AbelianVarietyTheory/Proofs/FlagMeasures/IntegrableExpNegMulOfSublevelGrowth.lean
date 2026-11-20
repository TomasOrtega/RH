import Mathlib

open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `X _ μ d a b C hd hd0 hgrowth hab`. Use `set C' : ℝ := max C 0 with hC'`. Establish `hC'0 : 0 ≤ C'` using `le_max_right _ _`. Establish `hmeas : Measurable fun x => Real.exp (-(b * d x))` using `Real.measurable_exp.comp ((hd.const_mul b).neg)`. Use `⟨hmeas.aestronglyMeasurable, ?_⟩` and prove the remaining obligations.

Establish `hpos : 0 ≤ᵐ[μ] fun x => Real.exp (-(b * d x))` using `Filter.Eventually.of_forall fun x => (Real.exp_pos _).le`. Rewrite using `[hasFiniteIntegral_iff_ofReal hpos]`. Set `s : ℕ → Set X` to `fun n => {x | d x ≤ (n : ℝ) + 1}`. Establish `hs : ∀ n, MeasurableSet (s n)` using `fun n => measurableSet_le hd measurable_const`. Set `g : ℕ → X → ENNReal` to `fun n => (s n).indicator (fun _ => ENNReal.ofReal (Real.exp (|b| - b * n)))`.

Establish `hpt : ∀ x, ENNReal.ofReal (Real.exp (-(b * d x))) ≤ ∑' n, g n x`. Introduce `x`. Use `set n := ⌊d x⌋₊ with hn`. Establish `h1 : (n : ℝ) ≤ d x` using `Nat.floor_le (hd0 x)`. Establish `h2 : d x < (n : ℝ) + 1` using `Nat.lt_floor_add_one (d x)`.

Establish `hxs : x ∈ s n` using `by show d x ≤ (n : ℝ) + 1`. Conclude with `h2.le`. Establish `hexp : Real.exp (-(b * d x)) ≤ Real.exp (|b| - b * n)`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hdist : |d x - n| ≤ 1`.

Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`. Establish `: |b * (d x - n)| ≤ |b|`. Rewrite using `[abs_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hlow` using `neg_abs_le (b * (d x - n))`.

Establish `hy : -(b * d x) = |b| - b * n - (|b| + b * (d x - n))` using `by ring`. Rewrite using `[hy]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Set `u : ℕ → ℝ` to `fun n => C' * Real.exp (|b| + a) * Real.exp (a - b) ^ n`.

Establish `hu0 : ∀ n, 0 ≤ u n` using `fun n => by positivity`. Establish `hr0 : 0 ≤ Real.exp (a - b)` using `(Real.exp_pos _).le`. Establish `hr1 : Real.exp (a - b) < 1` using `Real.exp_lt_one_iff.mpr (by linarith)`. Establish `hsum : Summable u` using `(summable_geometric_of_lt_one hr0 hr1).mul_left _`. Establish `hterm : ∀ n, ∫⁻ x, g n x ∂μ ≤ ENNReal.ofReal (u n)`.

Introduce `n`. Simplify using `only [g]`. Rewrite using `[lintegral_indicator_const (hs n)]`. Establish `hμ : μ (s n) ≤ ENNReal.ofReal (C' * Real.exp (a * ((n : ℝ) + 1)))`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Simplify using `only [u]`. Rewrite using `[← Real.exp_nat_mul]`. Establish `hE : Real.exp (|b| - b * n) * Real.exp (a * ((n : ℝ) + 1)) = Real.exp (|b| + a) * Real.exp (n * (a - b))`.

Rewrite using `[← Real.exp_add, ← Real.exp_add]`. Put the polynomial expressions in normal form. Take the linear combination `C' * hE`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem integrable_exp_neg_mul_of_sublevel_growth :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (d : X → ℝ) (a b C : ℝ), Measurable d →
      (∀ x, 0 ≤ d x) →
      (∀ r : ℝ, 0 ≤ r → μ {x | d x ≤ r} ≤ ENNReal.ofReal (C * Real.exp (a * r))) → a < b →
      Integrable (fun x => Real.exp (-(b * d x))) μ := by
  intro X _ μ d a b C hd hd0 hgrowth hab
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hmeas : Measurable fun x => Real.exp (-(b * d x)) :=
    Real.measurable_exp.comp ((hd.const_mul b).neg)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hpos : 0 ≤ᵐ[μ] fun x => Real.exp (-(b * d x)) :=
    Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
  rw [hasFiniteIntegral_iff_ofReal hpos]

  let s : ℕ → Set X := fun n => {x | d x ≤ (n : ℝ) + 1}
  have hs : ∀ n, MeasurableSet (s n) := fun n => measurableSet_le hd measurable_const
  let g : ℕ → X → ENNReal := fun n =>
    (s n).indicator (fun _ => ENNReal.ofReal (Real.exp (|b| - b * n)))
  have hpt : ∀ x, ENNReal.ofReal (Real.exp (-(b * d x))) ≤ ∑' n, g n x := by
    intro x
    set n := ⌊d x⌋₊ with hn
    have h1 : (n : ℝ) ≤ d x := Nat.floor_le (hd0 x)
    have h2 : d x < (n : ℝ) + 1 := Nat.lt_floor_add_one (d x)
    have hxs : x ∈ s n := by
      show d x ≤ (n : ℝ) + 1
      exact h2.le
    have hexp : Real.exp (-(b * d x)) ≤ Real.exp (|b| - b * n) := by
      apply Real.exp_le_exp.mpr
      have hdist : |d x - n| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      have : |b * (d x - n)| ≤ |b| := by
        rw [abs_mul]
        calc |b| * |d x - n| ≤ |b| * 1 := mul_le_mul_of_nonneg_left hdist (abs_nonneg b)
          _ = |b| := mul_one _
      have hlow := neg_abs_le (b * (d x - n))
      have hy : -(b * d x) = |b| - b * n - (|b| + b * (d x - n)) := by ring
      rw [hy]
      linarith
    calc ENNReal.ofReal (Real.exp (-(b * d x))) ≤ ENNReal.ofReal (Real.exp (|b| - b * n)) :=
          ENNReal.ofReal_le_ofReal hexp
      _ = g n x := by simp only [g, Set.indicator_of_mem hxs]
      _ ≤ ∑' m, g m x := ENNReal.le_tsum n

  let u : ℕ → ℝ := fun n => C' * Real.exp (|b| + a) * Real.exp (a - b) ^ n
  have hu0 : ∀ n, 0 ≤ u n := fun n => by positivity
  have hr0 : 0 ≤ Real.exp (a - b) := (Real.exp_pos _).le
  have hr1 : Real.exp (a - b) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsum : Summable u := (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hterm : ∀ n, ∫⁻ x, g n x ∂μ ≤ ENNReal.ofReal (u n) := by
    intro n
    simp only [g]
    rw [lintegral_indicator_const (hs n)]
    have hμ : μ (s n) ≤ ENNReal.ofReal (C' * Real.exp (a * ((n : ℝ) + 1))) := by
      calc μ (s n) ≤ ENNReal.ofReal (C * Real.exp (a * ((n : ℝ) + 1))) :=
            hgrowth _ (by positivity)
        _ ≤ ENNReal.ofReal (C' * Real.exp (a * ((n : ℝ) + 1))) :=
            ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    calc ENNReal.ofReal (Real.exp (|b| - b * n)) * μ (s n)
        ≤ ENNReal.ofReal (Real.exp (|b| - b * n)) *
            ENNReal.ofReal (C' * Real.exp (a * ((n : ℝ) + 1))) := by gcongr
      _ = ENNReal.ofReal (Real.exp (|b| - b * n) * (C' * Real.exp (a * ((n : ℝ) + 1)))) :=
          (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
      _ = ENNReal.ofReal (u n) := by
          congr 1
          simp only [u]
          rw [← Real.exp_nat_mul]
          have hE : Real.exp (|b| - b * n) * Real.exp (a * ((n : ℝ) + 1)) =
              Real.exp (|b| + a) * Real.exp (n * (a - b)) := by
            rw [← Real.exp_add, ← Real.exp_add]; ring_nf
          linear_combination C' * hE
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (-(b * d x))) ∂μ ≤ ∫⁻ x, ∑' n, g n x ∂μ :=
        MeasureTheory.lintegral_mono hpt
    _ = ∑' n, ∫⁻ x, g n x ∂μ :=
        MeasureTheory.lintegral_tsum fun n => (measurable_const.indicator (hs n)).aemeasurable
    _ ≤ ∑' n, ENNReal.ofReal (u n) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' n, u n) := (ENNReal.ofReal_tsum_of_nonneg hu0 hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end GlobalTheory
