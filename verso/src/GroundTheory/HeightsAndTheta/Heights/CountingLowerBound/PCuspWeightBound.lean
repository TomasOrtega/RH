import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

/- English proof (translation)
Introduce `f j' ρ rd lam NI covol h`. Establish `hf : (1 : ℝ) ≤ f` using `by exact_mod_cast h.one_le_f`. Establish `hj : (1 : ℝ) ≤ j'` using `by exact_mod_cast h.one_le_j'`. Establish `hρ : (1 : ℝ) ≤ ρ` using `by exact_mod_cast h.one_le_ρ`. Establish `hρj : (ρ : ℝ) ≤ j'` using `by exact_mod_cast h.ρ_le_j'`.

Establish `hrd` using `h.one_le_rd`. Establish `hlam` using `h.lam_pos`. Establish `hNI` using `h.NI_pos`. Establish `h2fρ : (0 : ℝ) < 2 * f * ρ` using `by positivity`. Establish `hsq : 0 < √(2 * f * ρ : ℝ)` using `Real.sqrt_pos.mpr h2fρ`.

Establish `hmk : (lam / √(2 * f * ρ : ℝ)) ^ (2 * f * ρ) ≤ NI * rd ^ (f * ρ)` using `h.covol_eq ▸ h.minkowski`. Establish `hrdp : (0 : ℝ) < rd ^ (f * ρ)` using `by positivity`. Establish `hlog` using `Real.log_le_log (by positivity) hmk`. Rewrite `hlog` using `[Real.log_pow, Real.log_mul hNI.ne' hrdp.ne', Real.log_pow, Real.log_div hlam.ne' hsq.ne', Real.log_sqrt h2fρ.le]`. Move the coercions through the operations in `at hlog`.

Establish `hρbound : -log NI ≤ f * ρ * (2 * log (1 / lam) + log (2 * f * ρ * rd))`. Establish `hrd0 : rd ≠ 0` using `by positivity`. Rewrite using `[one_div, Real.log_inv, Real.log_mul h2fρ.ne' hrd0]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hB : 0 ≤ 2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd)`.

Establish `: 0 ≤ log (2 * f * j' * rd)`. Establish `h1 : (1 : ℝ) ≤ f * j'` using `one_le_mul_of_one_le_of_one_le hf hj`. Establish `h2 : (1 : ℝ) ≤ f * j' * rd` using `one_le_mul_of_one_le_of_one_le h1 hrd`. Conclude with `Real.log_nonneg (by linarith)`. Establish `: 0 ≤ max 0 (log (1 / lam))` using `le_max_left _ _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hin : 2 * log (1 / lam) + log (2 * f * ρ * rd) ≤ 2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd)`. Establish `h1 : log (1 / lam) ≤ max 0 (log (1 / lam))` using `le_max_right _ _`. Establish `h2 : log (2 * f * ρ * rd) ≤ log (2 * f * j' * rd)` using `Real.log_le_log (by positivity) (by gcongr)`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem CuspWeightBound.proof : CuspWeightBound.Statement := by
  intro f j' ρ rd lam NI covol h
  have hf : (1 : ℝ) ≤ f := by exact_mod_cast h.one_le_f
  have hj : (1 : ℝ) ≤ j' := by exact_mod_cast h.one_le_j'
  have hρ : (1 : ℝ) ≤ ρ := by exact_mod_cast h.one_le_ρ
  have hρj : (ρ : ℝ) ≤ j' := by exact_mod_cast h.ρ_le_j'
  have hrd := h.one_le_rd
  have hlam := h.lam_pos
  have hNI := h.NI_pos
  have h2fρ : (0 : ℝ) < 2 * f * ρ := by positivity
  have hsq : 0 < √(2 * f * ρ : ℝ) := Real.sqrt_pos.mpr h2fρ

  have hmk : (lam / √(2 * f * ρ : ℝ)) ^ (2 * f * ρ) ≤ NI * rd ^ (f * ρ) :=
    h.covol_eq ▸ h.minkowski
  have hrdp : (0 : ℝ) < rd ^ (f * ρ) := by positivity
  have hlog := Real.log_le_log (by positivity) hmk
  rw [Real.log_pow, Real.log_mul hNI.ne' hrdp.ne', Real.log_pow,
    Real.log_div hlam.ne' hsq.ne', Real.log_sqrt h2fρ.le] at hlog
  push_cast at hlog

  have hρbound : -log NI ≤ f * ρ * (2 * log (1 / lam) + log (2 * f * ρ * rd)) := by
    have hrd0 : rd ≠ 0 := by positivity
    rw [one_div, Real.log_inv, Real.log_mul h2fρ.ne' hrd0]
    nlinarith

  have hB : 0 ≤ 2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd) := by
    have : 0 ≤ log (2 * f * j' * rd) := by
      have h1 : (1 : ℝ) ≤ f * j' := one_le_mul_of_one_le_of_one_le hf hj
      have h2 : (1 : ℝ) ≤ f * j' * rd := one_le_mul_of_one_le_of_one_le h1 hrd
      exact Real.log_nonneg (by linarith)
    have : 0 ≤ max 0 (log (1 / lam)) := le_max_left _ _
    linarith
  have hin : 2 * log (1 / lam) + log (2 * f * ρ * rd) ≤
      2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd) := by
    have h1 : log (1 / lam) ≤ max 0 (log (1 / lam)) := le_max_right _ _
    have h2 : log (2 * f * ρ * rd) ≤ log (2 * f * j' * rd) :=
      Real.log_le_log (by positivity) (by gcongr)
    linarith
  calc -log NI ≤ f * ρ * (2 * log (1 / lam) + log (2 * f * ρ * rd)) := hρbound
    _ ≤ f * ρ * (2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd)) := by
        gcongr
    _ ≤ f * j' * (2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd)) := by
        gcongr

end GroundTheory.Heights₂.Heights.LowerBound
