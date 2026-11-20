import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

/- English proof (translation)
Introduce `C0 C1 C2 hC0 hC1 hC2`. Use `⟨C0 * (log (3 + C2) + 2) + C1, ?_⟩` and prove the remaining obligations. Introduce `h hmu g fj La H`. Take `⟨hg, hfj, hgexp, hLa, hlow, hup⟩` from `H`. Establish `hLa0 : 0 < La` using `by linarith`.

Establish `hfj0 : 0 < fj` using `by linarith`. Establish `hlog3 : 0 ≤ log (3 + C2)` using `Real.log_nonneg (by linarith)`. Establish `hCnn : 0 ≤ C0 * (log (3 + C2) + 2) + C1` using `by positivity`. Distinguish the cases in `hmu0 : 0 ≤ hmu`. Establish `: 0 ≤ (C0 * (log (3 + C2) + 2) + C1) * fj * La` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `replace hmu0 : hmu < 0 := lt_of_not_ge hmu0`. Establish `hgLa : 0 ≤ C2 * g * La` using `by positivity`. Establish `hmax : max h 0 ≤ C2 * g * La` using `max_le (by linarith) hgLa`. Establish `hpos : 0 < 2 + g + max h 0` using `by have := le_max_right h 0; linarith`.

Establish `hgLa1 : 1 ≤ g * La` using `one_le_mul_of_one_le_of_one_le hg hLa`. Establish `hstep1 : 2 + g + max h 0 ≤ (3 + C2) * (g * La)`. Establish `: g ≤ g * La` using `le_mul_of_one_le_right (by linarith) hLa`. Use the polynomial consequences of the given equalities and inequalities. Establish `hLaexp : La ≤ exp La` using `by have := Real.add_one_le_exp La; linarith`.

Establish `hstep2 : g * La ≤ exp (2 * La)`. Rewrite using `[show 2 * La = La + La by ring, Real.exp_add]`. Conclude with `mul_le_mul hgexp hLaexp hLa0.le (exp_pos La).le`. Establish `hstep3 : 2 + g + max h 0 ≤ (3 + C2) * exp (2 * La)` using `hstep1.trans (mul_le_mul_of_nonneg_left hstep2 (by linarith))`. Establish `hlog : log (2 + g + max h 0) ≤ (log (3 + C2) + 2) * La`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.log_mul (by linarith) (exp_pos _).ne', Real.log_exp]`. Use `_ ≤ (log (3 + C2) + 2) * La := by nlinarith`. Establish `hC0log : C0 * log (2 + g + max h 0) ≤ C0 * ((log (3 + C2) + 2) * La)` using `mul_le_mul_of_nonneg_left hlog hC0`. Establish `hin : C0 * log (2 + g + max h 0) + C1 * La ≤ (C0 * (log (3 + C2) + 2) + C1) * La`.

Use the polynomial consequences of the given equalities and inequalities. Use `mul_le_mul_of_nonneg_left hin hfj0.le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem InteriorDichotomy.proof : InteriorDichotomy.Statement := by
  intro C0 C1 C2 hC0 hC1 hC2
  refine ⟨C0 * (log (3 + C2) + 2) + C1, ?_⟩
  intro h hmu g fj La H
  obtain ⟨hg, hfj, hgexp, hLa, hlow, hup⟩ := H
  have hLa0 : 0 < La := by linarith
  have hfj0 : 0 < fj := by linarith
  have hlog3 : 0 ≤ log (3 + C2) := Real.log_nonneg (by linarith)
  have hCnn : 0 ≤ C0 * (log (3 + C2) + 2) + C1 := by positivity
  by_cases hmu0 : 0 ≤ hmu
  · have : 0 ≤ (C0 * (log (3 + C2) + 2) + C1) * fj * La := by positivity
    linarith
  replace hmu0 : hmu < 0 := lt_of_not_ge hmu0

  have hgLa : 0 ≤ C2 * g * La := by positivity
  have hmax : max h 0 ≤ C2 * g * La := max_le (by linarith) hgLa
  have hpos : 0 < 2 + g + max h 0 := by have := le_max_right h 0; linarith
  have hgLa1 : 1 ≤ g * La := one_le_mul_of_one_le_of_one_le hg hLa
  have hstep1 : 2 + g + max h 0 ≤ (3 + C2) * (g * La) := by
    have : g ≤ g * La := le_mul_of_one_le_right (by linarith) hLa
    nlinarith
  have hLaexp : La ≤ exp La := by have := Real.add_one_le_exp La; linarith
  have hstep2 : g * La ≤ exp (2 * La) := by
    rw [show 2 * La = La + La by ring, Real.exp_add]
    exact mul_le_mul hgexp hLaexp hLa0.le (exp_pos La).le
  have hstep3 : 2 + g + max h 0 ≤ (3 + C2) * exp (2 * La) :=
    hstep1.trans (mul_le_mul_of_nonneg_left hstep2 (by linarith))
  have hlog : log (2 + g + max h 0) ≤ (log (3 + C2) + 2) * La := by
    calc log (2 + g + max h 0) ≤ log ((3 + C2) * exp (2 * La)) := Real.log_le_log hpos hstep3
      _ = log (3 + C2) + 2 * La := by
          rw [Real.log_mul (by linarith) (exp_pos _).ne', Real.log_exp]
      _ ≤ (log (3 + C2) + 2) * La := by nlinarith
  have hC0log : C0 * log (2 + g + max h 0) ≤ C0 * ((log (3 + C2) + 2) * La) :=
    mul_le_mul_of_nonneg_left hlog hC0
  have hin : C0 * log (2 + g + max h 0) + C1 * La ≤ (C0 * (log (3 + C2) + 2) + C1) * La := by
    nlinarith
  have := mul_le_mul_of_nonneg_left hin hfj0.le
  nlinarith

end GroundTheory.Heights₂.Heights.LowerBound
