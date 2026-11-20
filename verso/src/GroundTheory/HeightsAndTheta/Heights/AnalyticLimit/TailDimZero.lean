import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot ChartPartition mInt integralWith locDens)

/- English proof (translation)
Establish `hv : (volume : Measure (Fin 0 → ℂ)) Set.univ = 1`. Rewrite using `[volume_pi, Measure.pi_univ]`. Simplify using the standard rewrite rules. Establish `: IsFiniteMeasure (volume : Measure (Fin 0 → ℂ))` using `⟨by rw [hv]; exact ENNReal.one_lt_top⟩`. Establish `hd : ∀ j y, locDens A T j y = 1` using `fun j y => by`.

Simplify using `[locDens, ReciprocityTheory.AnForm.maDens, ReciprocityTheory.AnForm.mdisc_zero]`. Establish `hint : ∀ (f : (Fin 0 → ℂ) → ℝ) (K : Set (Fin 0 → ℂ)), ∫ y in K, f y = (volume K).toReal * f default`. Introduce `f K`. Establish `: f = fun _ => f default` using `funext fun y => congrArg f (Subsingleton.elim y default)`. Rewrite using `[this, integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]`.

Establish `hvol : ∀ K : Set (Fin 0 → ℂ), 0 ≤ (volume K).toReal ∧ (volume K).toReal ≤ 1` using `fun K => ⟨ENNReal.toReal_nonneg, by`. Use `ENNReal.toReal_mono (by rw [hv]; exact ENNReal.one_ne_top) (measure_mono (μ := volume) (Set.subset_univ K))` as an intermediate fact. Rewrite using `[hv, ENNReal.toReal_one] at this⟩` and apply the resulting hypothesis. Use `set p : Fin A.n → X := fun j => (A.chart j).symm default`. Use `set B := ∑ j, |Real.log (r (p j))|`.

Use `set M := ∑ j, |r (p j)| + Real.exp 1`. Establish `hB : 0 ≤ B` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`. Establish `hM : 0 < M` using `by positivity`. Use `⟨B * M, fun R₀ hR₀ => ⟨fun j K _ _ => Integrable.of_finite.integrableOn, ?_⟩⟩` and prove the remaining obligations. Use `set g := (tail Yo r R₀).indicator fun x => Real.log (r x)`.

Establish `hR₀pos : 0 < R₀` using `lt_of_lt_of_le (Real.exp_pos 1) hR₀`. Establish `hlog : 1 ≤ Real.log R₀`. Use `Real.log_le_log (Real.exp_pos 1) hR₀` as an intermediate fact. Rewrite `this` using `[Real.log_exp]`. Then use the resulting hypothesis. Establish `hg : ∀ x, |g x| ≤ |Real.log (r x)|` using `fun x => by`.

Simplify using `only [g, Set.indicator]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hterm : ∀ (P : ChartPartition A) j, |∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A T j y| ≤ |Real.log (r (p j))| ∧ (M < R₀ → ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A T j y = 0)`. Introduce `P j`. Rewrite using `[hint, hd, mul_one]`.

Establish `hχ0` using `P.nonneg j (p j)`. Establish `hχ1 : P.χ j (p j) ≤ 1` using `P.sum_eq_one (p j) ▸ Finset.single_le_sum (fun i _ => P.nonneg i (p j)) (Finset.mem_univ j)`. Take `⟨hv0, hv1⟩` from `hvol (A.chart j).target`. Use `⟨?_, fun hMR => ?_⟩` and prove the remaining obligations. Rewrite using `[abs_mul, abs_mul, abs_of_nonneg hv0, abs_of_nonneg hχ0]`.

Use `hg (p j)` as an intermediate fact. Establish `h2 : P.χ j (p j) * |g (p j)| ≤ |Real.log (r (p j))|` using `by nlinarith [abs_nonneg (g (p j))]`. Use polynomial arithmetic with `[abs_nonneg (g (p j))]`. Establish `hr : |r (p j)| ≤ ∑ i, |r (p i)|` using `Finset.single_le_sum (f := fun i => |r (p i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)`. Establish `hn : p j ∉ tail Yo r R₀` using `fun h => by`.

Use `h.2` as an intermediate fact. Use `le_abs_self (r (p j))` as an intermediate fact. Use `Real.exp_pos 1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `show (volume (A.chart j).target).toReal * (P.χ j (p j) * g (p j)) = 0`.

Rewrite using `[show g (p j) = 0 from Set.indicator_of_notMem hn _]`. Simplify using the standard rewrite rules. Establish `hRHS : 0 ≤ B * M * Real.log R₀ ^ (0 + 1) / R₀`. Establish `: 0 ≤ Real.log R₀` using `by linarith`. Check the signs of the components of the expression.

Use `show mInt A T g ≤ B * M * Real.log R₀ ^ (0 + 1) / R₀`. Unfold `mInt`. Use `split_ifs with h`. Unfold `integralWith`. Distinguish the cases in `hMR : M < R₀`.

Rewrite using `[Finset.sum_eq_zero fun j _ => (hterm h.some j).2 hMR]`. Conclude with `hRHS`. Use `replace hMR := not_lt.mp hMR`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[le_div_iff₀ hR₀pos, pow_one]`.

Establish `h1 : B * R₀ ≤ B * M` using `mul_le_mul_of_nonneg_left hMR hB`. Establish `h2 : B * M ≤ B * M * Real.log R₀`. Use `mul_nonneg hB hM.le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `hRHS`.
-/
theorem tailLogBound_dim_zero {X : Type} [TopologicalSpace X] (A : FinHolAtlas 0 X) (Yo : Set X)
    (r : X → ℝ) (T : Fin 0 → LocPot X) : ∃ CE : ℝ, TailLogBound A Yo r T CE := by
  classical
  have hv : (volume : Measure (Fin 0 → ℂ)) Set.univ = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  have : IsFiniteMeasure (volume : Measure (Fin 0 → ℂ)) := ⟨by rw [hv]; exact ENNReal.one_lt_top⟩
  have hd : ∀ j y, locDens A T j y = 1 := fun j y => by
    simp [locDens, ReciprocityTheory.AnForm.maDens, ReciprocityTheory.AnForm.mdisc_zero]
  have hint : ∀ (f : (Fin 0 → ℂ) → ℝ) (K : Set (Fin 0 → ℂ)),
      ∫ y in K, f y = (volume K).toReal * f default := by
    intro f K
    have : f = fun _ => f default := funext fun y => congrArg f (Subsingleton.elim y default)
    rw [this, integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
  have hvol : ∀ K : Set (Fin 0 → ℂ), 0 ≤ (volume K).toReal ∧ (volume K).toReal ≤ 1 := fun K =>
    ⟨ENNReal.toReal_nonneg, by
      have := ENNReal.toReal_mono (by rw [hv]; exact ENNReal.one_ne_top)
        (measure_mono (μ := volume) (Set.subset_univ K))
      rwa [hv, ENNReal.toReal_one] at this⟩
  set p : Fin A.n → X := fun j => (A.chart j).symm default
  set B := ∑ j, |Real.log (r (p j))|
  set M := ∑ j, |r (p j)| + Real.exp 1
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM : 0 < M := by positivity
  refine ⟨B * M, fun R₀ hR₀ => ⟨fun j K _ _ => Integrable.of_finite.integrableOn, ?_⟩⟩
  set g := (tail Yo r R₀).indicator fun x => Real.log (r x)
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le (Real.exp_pos 1) hR₀
  have hlog : 1 ≤ Real.log R₀ := by
    have := Real.log_le_log (Real.exp_pos 1) hR₀
    rwa [Real.log_exp] at this
  have hg : ∀ x, |g x| ≤ |Real.log (r x)| := fun x => by
    simp only [g, Set.indicator]
    split_ifs <;> simp
  have hterm : ∀ (P : ChartPartition A) j,
      |∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
          locDens A T j y| ≤ |Real.log (r (p j))| ∧
        (M < R₀ → ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) *
          g ((A.chart j).symm y) * locDens A T j y = 0) := by
    intro P j
    rw [hint, hd, mul_one]
    have hχ0 := P.nonneg j (p j)
    have hχ1 : P.χ j (p j) ≤ 1 := P.sum_eq_one (p j) ▸
      Finset.single_le_sum (fun i _ => P.nonneg i (p j)) (Finset.mem_univ j)
    obtain ⟨hv0, hv1⟩ := hvol (A.chart j).target
    refine ⟨?_, fun hMR => ?_⟩
    · rw [abs_mul, abs_mul, abs_of_nonneg hv0, abs_of_nonneg hχ0]
      have := hg (p j)
      have h2 : P.χ j (p j) * |g (p j)| ≤ |Real.log (r (p j))| := by nlinarith [abs_nonneg (g (p j))]
      nlinarith [abs_nonneg (g (p j))]
    · have hr : |r (p j)| ≤ ∑ i, |r (p i)| :=
        Finset.single_le_sum (f := fun i => |r (p i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      have hn : p j ∉ tail Yo r R₀ := fun h => by
        have := h.2
        have := le_abs_self (r (p j))
        have := Real.exp_pos 1
        linarith
      show (volume (A.chart j).target).toReal * (P.χ j (p j) * g (p j)) = 0
      rw [show g (p j) = 0 from Set.indicator_of_notMem hn _]
      simp
  have hRHS : 0 ≤ B * M * Real.log R₀ ^ (0 + 1) / R₀ := by
    have : 0 ≤ Real.log R₀ := by linarith
    positivity
  show mInt A T g ≤ B * M * Real.log R₀ ^ (0 + 1) / R₀
  unfold mInt
  split_ifs with h
  · unfold integralWith
    by_cases hMR : M < R₀
    · rw [Finset.sum_eq_zero fun j _ => (hterm h.some j).2 hMR]
      exact hRHS
    · replace hMR := not_lt.mp hMR
      calc _ ≤ ∑ j, |Real.log (r (p j))| :=
            Finset.sum_le_sum fun j _ => (le_abs_self _).trans (hterm h.some j).1
        _ ≤ B * M * Real.log R₀ ^ (0 + 1) / R₀ := by
          rw [le_div_iff₀ hR₀pos, pow_one]
          have h1 : B * R₀ ≤ B * M := mul_le_mul_of_nonneg_left hMR hB
          have h2 : B * M ≤ B * M * Real.log R₀ := by
            have := mul_nonneg hB hM.le
            nlinarith
          linarith
  · exact hRHS

end GroundTheory.Heights₂.Heights.AnalyticLimit
