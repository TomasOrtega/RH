import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCPsh

open Metric Filter Real

noncomputable section

/- English proof (translation)
Establish `hh' : AnalyticOnNhd ℂ h (closedBall 0 |(1 : ℝ)|)` using `by simpa using hh`. Rewrite using `[hh'.circleAverage_log_norm one_ne_zero h0]`. Establish `hnn : ∀ u : ℂ, 0 ≤ (MeromorphicOn.divisor h (closedBall 0 |(1:ℝ)|) u : ℝ) * Real.log (1 * ‖(0:ℂ) - u‖⁻¹)`. Introduce `u`. Distinguish the cases in `hu : u ∈ closedBall (0:ℂ) |(1:ℝ)|`.

Use `mul_nonneg ?_ ?_` and prove the remaining obligations. Conclude with `(MeromorphicOn.AnalyticOnNhd.divisor_nonneg hh') u` after adjusting the coercions. Rewrite using `[one_mul, zero_sub, norm_neg]`. Break down `eq_or_ne u 0 with rfl | hu0` into its components or cases. Simplify using the standard rewrite rules.

Apply `Real.log_nonneg` to reduce the goal to its premises. Establish `h1 : ‖u‖ ≤ 1` using `by simpa using hu`. Establish `h2 : 0 < ‖u‖` using `norm_pos_iff.mpr hu0`. Rewrite using `[le_inv_comm₀ zero_lt_one h2]`. Simplify using `using h1`.

Rewrite using `[Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]`. Simplify using the standard rewrite rules. Combine the linear relations using `[finsum_nonneg hnn]`.
-/
theorem log_norm_le_circleAverage {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1))
    (h0 : h 0 ≠ 0) :
    Real.log ‖h 0‖ ≤ circleAverage (fun ζ => Real.log ‖h ζ‖) 0 1 := by
  have hh' : AnalyticOnNhd ℂ h (closedBall 0 |(1 : ℝ)|) := by simpa using hh
  rw [hh'.circleAverage_log_norm one_ne_zero h0]
  have hnn : ∀ u : ℂ, 0 ≤ (MeromorphicOn.divisor h (closedBall 0 |(1:ℝ)|) u : ℝ) *
      Real.log (1 * ‖(0:ℂ) - u‖⁻¹) := by
    intro u
    by_cases hu : u ∈ closedBall (0:ℂ) |(1:ℝ)|
    · refine mul_nonneg ?_ ?_
      · exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hh') u
      · rw [one_mul, zero_sub, norm_neg]
        rcases eq_or_ne u 0 with rfl | hu0
        · simp
        · apply Real.log_nonneg
          have h1 : ‖u‖ ≤ 1 := by simpa using hu
          have h2 : 0 < ‖u‖ := norm_pos_iff.mpr hu0
          rw [le_inv_comm₀ zero_lt_one h2]
          simpa using h1
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      simp
  linarith [finsum_nonneg hnn]

/- English proof (translation)
Establish `: MeromorphicOn h (sphere (0:ℂ) |(1:ℝ)|)` using `(hh.mono (by simpa using sphere_subset_closedBall)).meromorphicOn`. Conclude with `this.circleIntegrable_log_norm`.
-/
theorem circleIntegrable_log_norm_of_analytic {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    CircleIntegrable (fun ζ => Real.log ‖h ζ‖) 0 1 := by
  have : MeromorphicOn h (sphere (0:ℂ) |(1:ℝ)|) :=
    (hh.mono (by simpa using sphere_subset_closedBall)).meromorphicOn
  exact this.circleIntegrable_log_norm

/- English proof (translation)
Establish `hlog` using `circleIntegrable_log_norm_of_analytic hh`. Establish `hj` using `log_norm_le_circleAverage hh h0`. Use `set ψ : ℂ → ℝ := fun ζ => 2 * Real.log ‖h ζ‖ - ℓ ζ with hψdef`. Establish `h2 : CircleIntegrable (fun ζ => (2:ℝ) • Real.log ‖h ζ‖) 0 1` using `hlog.const_fun_smul`. Establish `hψ : CircleIntegrable ψ 0 1`.

Use `h2.fun_sub hℓ` as an intermediate fact. Simplify `this` using `[ψ, smul_eq_mul]`. Establish `havgψ : circleAverage ψ 0 1 = 2 * circleAverage (fun ζ => Real.log ‖h ζ‖) 0 1 - circleAverage ℓ 0 1`. Use `circleAverage_fun_sub h2 hℓ` as an intermediate fact. Simplify using `only [smul_eq_mul] at this`.

Rewrite using `[show ψ = fun ζ => 2 * Real.log ‖h ζ‖ - ℓ ζ from rfl, this]`. Use `congr 1`. Use `circleAverage_fun_smul (c := (0:ℂ)) (R := 1) (a := (2:ℝ)) (f := fun ζ => Real.log ‖h ζ‖)` as an intermediate fact. Simplify `this` using `[smul_eq_mul]`. Establish `hzeros : h ⁻¹' {0}ᶜ ∈ codiscreteWithin (sphere (0:ℂ) |(1:ℝ)|)`.

Establish `hconn : IsConnected (closedBall (0:ℂ) 1)` using `⟨⟨0, mem_closedBall_self zero_le_one⟩, (convex_closedBall (0:ℂ) 1).isPreconnected⟩`. Use `hh.preimage_zero_mem_codiscreteWithin h0 (mem_closedBall_self zero_le_one) hconn` as an intermediate fact. Conclude with `codiscreteWithin_mono (by simpa using sphere_subset_closedBall) this`. Establish `heq : (fun ζ => φ ζ - ψ ζ) =ᶠ[codiscreteWithin (sphere (0:ℂ) |(1:ℝ)|)] (fun ζ => max (φ ζ - ψ ζ) 0)`. Establish `hs : sphere (0:ℂ) |(1:ℝ)| ∈ codiscreteWithin (sphere (0:ℂ) |(1:ℝ)|)` using `self_mem_codiscreteWithin _`.

Use `filter_upwards [hzeros, hs] with ζ hζ hζs`. Establish `hζs' : ζ ∈ sphere (0:ℂ) 1` using `by simpa using hζs`. Use `hpt ζ hζs' hζ` as an intermediate fact. Rewrite using `[max_eq_left (by simp only [ψ]; linarith)]`. Establish `hnn : 0 ≤ circleAverage (fun ζ => φ ζ - ψ ζ) 0 1`.

Rewrite using `[circleAverage_congr_codiscreteWithin heq one_ne_zero]`. Conclude with `circleAverage_nonneg_of_nonneg fun ζ _ => le_max_right _ _`. Rewrite `hnn` using `[circleAverage_fun_sub hφ hψ, havgψ]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_circleAverage_of_minorant {φ ℓ : ℂ → ℝ} {h : ℂ → ℂ} {ℓ0 : ℝ}
    (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) (h0 : h 0 ≠ 0)
    (hφ : CircleIntegrable φ 0 1) (hℓ : CircleIntegrable ℓ 0 1)
    (hpt : ∀ ζ ∈ sphere (0:ℂ) 1, h ζ ≠ 0 → 2 * Real.log ‖h ζ‖ - ℓ ζ ≤ φ ζ)
    (hℓavg : circleAverage ℓ 0 1 ≤ ℓ0) (hφ0 : φ 0 ≤ 2 * Real.log ‖h 0‖ - ℓ0) :
    φ 0 ≤ circleAverage φ 0 1 := by
  have hlog := circleIntegrable_log_norm_of_analytic hh
  have hj := log_norm_le_circleAverage hh h0
  set ψ : ℂ → ℝ := fun ζ => 2 * Real.log ‖h ζ‖ - ℓ ζ with hψdef
  have h2 : CircleIntegrable (fun ζ => (2:ℝ) • Real.log ‖h ζ‖) 0 1 := hlog.const_fun_smul
  have hψ : CircleIntegrable ψ 0 1 := by
    have := h2.fun_sub hℓ
    simpa [ψ, smul_eq_mul] using this
  have havgψ : circleAverage ψ 0 1 = 2 * circleAverage (fun ζ => Real.log ‖h ζ‖) 0 1 -
      circleAverage ℓ 0 1 := by
    have := circleAverage_fun_sub h2 hℓ
    simp only [smul_eq_mul] at this
    rw [show ψ = fun ζ => 2 * Real.log ‖h ζ‖ - ℓ ζ from rfl, this]
    congr 1
    have := circleAverage_fun_smul (c := (0:ℂ)) (R := 1) (a := (2:ℝ)) (f := fun ζ => Real.log ‖h ζ‖)
    simpa [smul_eq_mul] using this
  have hzeros : h ⁻¹' {0}ᶜ ∈ codiscreteWithin (sphere (0:ℂ) |(1:ℝ)|) := by
    have hconn : IsConnected (closedBall (0:ℂ) 1) :=
      ⟨⟨0, mem_closedBall_self zero_le_one⟩, (convex_closedBall (0:ℂ) 1).isPreconnected⟩
    have := hh.preimage_zero_mem_codiscreteWithin h0 (mem_closedBall_self zero_le_one) hconn
    exact codiscreteWithin_mono (by simpa using sphere_subset_closedBall) this
  have heq : (fun ζ => φ ζ - ψ ζ) =ᶠ[codiscreteWithin (sphere (0:ℂ) |(1:ℝ)|)]
      (fun ζ => max (φ ζ - ψ ζ) 0) := by
    have hs : sphere (0:ℂ) |(1:ℝ)| ∈ codiscreteWithin (sphere (0:ℂ) |(1:ℝ)|) :=
      self_mem_codiscreteWithin _
    filter_upwards [hzeros, hs] with ζ hζ hζs
    have hζs' : ζ ∈ sphere (0:ℂ) 1 := by simpa using hζs
    have := hpt ζ hζs' hζ
    rw [max_eq_left (by simp only [ψ]; linarith)]
  have hnn : 0 ≤ circleAverage (fun ζ => φ ζ - ψ ζ) 0 1 := by
    rw [circleAverage_congr_codiscreteWithin heq one_ne_zero]
    exact circleAverage_nonneg_of_nonneg fun ζ _ => le_max_right _ _
  rw [circleAverage_fun_sub hφ hψ, havgψ] at hnn
  linarith

end

end GroundTheory.Heights₂.Heights.MCPsh
