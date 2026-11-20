import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric

noncomputable section

/- English proof (translation)
Introduce `D U u z δ t C₁ hU hu hδ ht hC hCt`. Establish `hC0 : 0 < C₁` using `by linarith`. Establish `hb0 : 0 < C₁ * t` using `mul_pos hC0 ht`. Establish `hδ0 : 0 < δ` using `hb0.trans hCt`. Establish `hconv` using `(h0 D U u z δ hU hu hδ0 hδ).1`.

Establish `ha0 : 0 < t / (4 * C₁)` using `by positivity`. Establish `hab : t / (4 * C₁) < C₁ * t`. Rewrite using `[div_lt_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `key` using `hconv.slope_mono_adjacent (Set.mem_Iic.2 (Real.log_le_log ha0 (hab.trans hCt).le)) (Set.mem_Iic.2 le_rfl) (Real.log_lt_log ha0 hab) (Real.log_lt_log hb0 hCt)`.

Simplify using `only [Real.exp_log ha0, Real.exp_log hb0, Real.exp_log hδ0] at key`. Establish `h1 : Real.log (C₁ * t) - Real.log (t / (4 * C₁)) = Real.log (4 * C₁ ^ 2)`. Rewrite using `[← Real.log_div hb0.ne' ha0.ne']`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Establish `h2 : Real.log δ - Real.log (C₁ * t) = Real.log (δ / (C₁ * t))` using `(Real.log_div hδ0.ne' hb0.ne').symm`. Establish `hL1 : 0 < Real.log (4 * C₁ ^ 2)`. Rewrite using `[← h1]`. Conclude with `sub_pos.2 (Real.log_lt_log ha0 hab)`. Rewrite `key` using `[h1, h2, div_le_iff₀ hL1]`.

Rewrite using `[mul_div_assoc, mul_comm (Real.log (4 * C₁ ^ 2))]`. Conclude with `key`.
-/
theorem PolyMaxOscillation.proof (h0 : ReciprocityTheory.AnForm.A.PolyMaxLogConvexStatement) :
    PolyMaxOscillation.Statement := by
  intro D U u z δ t C₁ hU hu hδ ht hC hCt
  have hC0 : 0 < C₁ := by linarith
  have hb0 : 0 < C₁ * t := mul_pos hC0 ht
  have hδ0 : 0 < δ := hb0.trans hCt
  have hconv := (h0 D U u z δ hU hu hδ0 hδ).1
  have ha0 : 0 < t / (4 * C₁) := by positivity
  have hab : t / (4 * C₁) < C₁ * t := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have key := hconv.slope_mono_adjacent
    (Set.mem_Iic.2 (Real.log_le_log ha0 (hab.trans hCt).le)) (Set.mem_Iic.2 le_rfl)
    (Real.log_lt_log ha0 hab) (Real.log_lt_log hb0 hCt)
  simp only [Real.exp_log ha0, Real.exp_log hb0, Real.exp_log hδ0] at key
  have h1 : Real.log (C₁ * t) - Real.log (t / (4 * C₁)) = Real.log (4 * C₁ ^ 2) := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    congr 1
    field_simp
  have h2 : Real.log δ - Real.log (C₁ * t) = Real.log (δ / (C₁ * t)) :=
    (Real.log_div hδ0.ne' hb0.ne').symm
  have hL1 : 0 < Real.log (4 * C₁ ^ 2) := by
    rw [← h1]
    exact sub_pos.2 (Real.log_lt_log ha0 hab)
  rw [h1, h2, div_le_iff₀ hL1] at key
  rw [mul_div_assoc, mul_comm (Real.log (4 * C₁ ^ 2))]
  exact key

/- English proof (translation)
The claim follows from `PolyMaxOscillation.proof ReciprocityTheory.AnForm.A.polyMaxLogConvex_thm`.
-/
theorem PolyMaxOscillation.proof_closed : PolyMaxOscillation.Statement :=
  PolyMaxOscillation.proof ReciprocityTheory.AnForm.A.polyMaxLogConvex_thm

end

end GroundTheory.Heights₂.Heights.Regular
