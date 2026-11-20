import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace Formalism.L2.SG.Pf.Tau

/- English proof (translation)
Introduce `X _ S g hne hpos hloc`. Establish `hbdd : ∀ x, BddBelow (Set.range (g x))` using `fun x => ⟨0, by rintro _ ⟨s, rfl⟩; exact hpos x s⟩`. Establish `hinf_nonneg : ∀ x, 0 ≤ ⨅ s, g x s` using `fun x => by haveI := hne x`. Conclude with `le_ciInf fun s => hpos x s`. Establish `key : ∀ x y (r : ℝ), 0 ≤ r → (∀ s, ∃ s', g y s' ≤ r * g x s) → (⨅ s, g y s) ≤ r * ⨅ s, g x s`.

Introduce `x y r hr h`. Use `haveI := hne x`. Rewrite using `[Real.mul_iInf_of_nonneg hr]`. Conclude with `le_ciInf fun s => by`. Take `⟨s', hs'⟩` from `h s`.

Conclude with `(ciInf_le (hbdd y) s').trans hs'`. Establish `hmin : ∀ a b r : ℝ, 1 ≤ r → 0 ≤ b → a ≤ r * b → min (1 / 2) a ≤ r * min (1 / 2) b`. Introduce `a b r hr hb hab`. Break down `le_total b (1 / 2) with h | h` into its components or cases. Rewrite using `[min_eq_right h]`.

Conclude with `(min_le_right _ _).trans hab`. Rewrite using `[min_eq_left h]`. Use polynomial arithmetic with `[min_le_left (1 / 2 : ℝ) a]`. Use `continuous_iff_continuousAt.2 fun x => Metric.tendsto_nhds.2 fun ε hε => ?_` and prove the remaining obligations. Establish `hr : (1 : ℝ) < 1 + ε` using `by linarith`.

Use `filter_upwards [hloc x (1 + ε) hr] with x' hx'`. Establish `h1` using `hmin _ _ _ hr.le (hinf_nonneg x) (key x x' _ (by linarith) hx'.1)`. Establish `h2` using `hmin _ _ _ hr.le (hinf_nonneg x') (key x' x _ (by linarith) hx'.2)`. Establish `hm1 : min (1 / 2 : ℝ) (⨅ s, g x s) ≤ 1 / 2` using `min_le_left _ _`. Establish `hm2 : min (1 / 2 : ℝ) (⨅ s, g x' s) ≤ 1 / 2` using `min_le_left _ _`.

Establish `hp1 : 0 ≤ min (1 / 2 : ℝ) (⨅ s, g x s)` using `le_min (by norm_num) (hinf_nonneg x)`. Establish `hp2 : 0 ≤ min (1 / 2 : ℝ) (⨅ s, g x' s)` using `le_min (by norm_num) (hinf_nonneg x')`. Rewrite using `[Real.dist_eq, abs_lt]`. Apply the tactic sequence `constructor <;> nlinarith`.
-/
theorem t7 : InfimumContinuousFamily := by
  intro X _ S g hne hpos hloc
  have hbdd : ∀ x, BddBelow (Set.range (g x)) := fun x => ⟨0, by rintro _ ⟨s, rfl⟩; exact hpos x s⟩
  have hinf_nonneg : ∀ x, 0 ≤ ⨅ s, g x s := fun x => by
    haveI := hne x
    exact le_ciInf fun s => hpos x s
  have key : ∀ x y (r : ℝ), 0 ≤ r → (∀ s, ∃ s', g y s' ≤ r * g x s) → (⨅ s, g y s) ≤ r * ⨅ s, g x s := by
    intro x y r hr h
    haveI := hne x
    rw [Real.mul_iInf_of_nonneg hr]
    exact le_ciInf fun s => by
      obtain ⟨s', hs'⟩ := h s
      exact (ciInf_le (hbdd y) s').trans hs'
  have hmin : ∀ a b r : ℝ, 1 ≤ r → 0 ≤ b → a ≤ r * b → min (1 / 2) a ≤ r * min (1 / 2) b := by
    intro a b r hr hb hab
    rcases le_total b (1 / 2) with h | h
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans hab
    · rw [min_eq_left h]
      nlinarith [min_le_left (1 / 2 : ℝ) a]
  refine continuous_iff_continuousAt.2 fun x => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hr : (1 : ℝ) < 1 + ε := by linarith
  filter_upwards [hloc x (1 + ε) hr] with x' hx'
  have h1 := hmin _ _ _ hr.le (hinf_nonneg x) (key x x' _ (by linarith) hx'.1)
  have h2 := hmin _ _ _ hr.le (hinf_nonneg x') (key x' x _ (by linarith) hx'.2)
  have hm1 : min (1 / 2 : ℝ) (⨅ s, g x s) ≤ 1 / 2 := min_le_left _ _
  have hm2 : min (1 / 2 : ℝ) (⨅ s, g x' s) ≤ 1 / 2 := min_le_left _ _
  have hp1 : 0 ≤ min (1 / 2 : ℝ) (⨅ s, g x s) := le_min (by norm_num) (hinf_nonneg x)
  have hp2 : 0 ≤ min (1 / 2 : ℝ) (⨅ s, g x' s) := le_min (by norm_num) (hinf_nonneg x')
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

end Formalism.L2.SG.Pf.Tau
