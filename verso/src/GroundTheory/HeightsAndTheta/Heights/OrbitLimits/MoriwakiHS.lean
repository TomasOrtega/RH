import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefCountLower
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefCountUpper
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

/- English proof (translation)
Use `tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Use `filter_upwards [hc, hlo ((T - a) / 2) (by linarith)] with n hcn hn`. Rewrite using `[lt_div_iff₀ hcn]`. Use `mul_lt_mul_of_pos_right (show a < T - (T - a) / 2 by linarith) hcn` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `filter_upwards [hc, hup ((a - T) / 2) (by linarith)] with n hcn hn`. Rewrite using `[div_lt_iff₀ hcn]`. Use `mul_lt_mul_of_pos_right (show T + (a - T) / 2 < a by linarith) hcn` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tendsto_div_of_bounds {h c : ℕ → ℝ} {T : ℝ} (hc : ∀ᶠ n in atTop, 0 < c n)
    (hlo : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, (T - ε) * c n ≤ h n)
    (hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, h n ≤ (T + ε) * c n) :
    Tendsto (fun n => h n / c n) atTop (𝓝 T) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [hc, hlo ((T - a) / 2) (by linarith)] with n hcn hn
    rw [lt_div_iff₀ hcn]
    have := mul_lt_mul_of_pos_right (show a < T - (T - a) / 2 by linarith) hcn
    linarith
  · filter_upwards [hc, hup ((a - T) / 2) (by linarith)] with n hcn hn
    rw [div_lt_iff₀ hcn]
    have := mul_lt_mul_of_pos_right (show T + (a - T) / 2 < a by linarith) hcn
    linarith

/- English proof (translation)
Use `filter_upwards [eventually_ge_atTop 1] with n hn`. Establish `: (0 : ℝ) < n` using `by exact_mod_cast hn`. Check the signs of the components of the expression.
-/
theorem eventually_pos_normaliser (D : ℕ) :
    ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen hht`. Conclude with `tendsto_div_of_bounds (h := smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a)) (c := fun n : ℕ => (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) (eventually_pos_normaliser D) (hL K ι Ω y D A P0 II hII har hb hP0 hs hc hnef hgen hht) (hU K ι Ω y D A P0 II hII har hb …`.
-/
theorem MoriwakiHS.of_found (hL : NefCountLower.Statement) (hU : NefCountUpper.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement := by
  intro K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen hht
  exact tendsto_div_of_bounds (h := smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a))
    (c := fun n : ℕ => (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) (eventually_pos_normaliser D)
    (hL K ι Ω y D A P0 II hII har hb hP0 hs hc hnef hgen hht)
    (hU K ι Ω y D A P0 II hII har hb hP0 hs hc hnef hgen hht)

end

end GroundTheory.Heights₂.Heights.Targets
