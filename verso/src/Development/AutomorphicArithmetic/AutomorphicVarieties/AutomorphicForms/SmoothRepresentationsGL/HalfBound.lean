import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Introduce `hT V M _ _ _ _ _ _ A e`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ, hAδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ‖A‖ * δ ≤ 1 / 2 := by`. Use `⟨1 / (2 * (‖A‖ + 1)), by positivity, ?_⟩` and prove the remaining obligations. Establish `h0 : 0 ≤ ‖A‖` using `norm_nonneg _`. Rewrite using `[mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hball : ∀ ξ ∈ Metric.ball e δ, ‖A (ξ - e)‖ ≤ 1 / 2`. Introduce `ξ hξ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← dist_eq_norm]`.

Conclude with `(Metric.mem_ball.mp hξ).le`. Use `_ ≤ 1 / 2 := hAδ`. Set `φ : ContDiffBump e` to `⟨δ / 4, δ / 2, by positivity, by linarith⟩`. Set `χ : ContDiffBump e` to `⟨δ / 2, δ, by positivity, by linarith⟩`. Set `g : V → (M →L[ℝ] M)` to `fun ξ => χ ξ • A (ξ - e)`.

Establish `hsmall : ∀ ξ : V, ‖g ξ‖ ≤ 1 / 2`. Introduce `ξ`. Distinguish the cases in `hξ : χ ξ = 0`. Simplify using `[g, hξ]`. Establish `hmem : ξ ∈ Metric.ball e δ`.

Establish `h1 : ξ ∈ Function.support χ` using `hξ`. Rewrite `h1` using `[χ.support_eq]`. Then use the resulting hypothesis. Simplify using `only [g]`. Rewrite using `[norm_smul, Real.norm_of_nonneg χ.nonneg]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `χ.le_one`. Conclude with `hball ξ hmem`. Use `_ = 1 / 2 := by norm_num`. Use `⟨fun ξ => ((φ ξ : ℝ) : ℂ), ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : φ e = 1` using `φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le)`.

Simplify using `[h1]`. Introduce `ξ hξ y hy`. Establish `hφ : φ ξ ≠ 0`. Introduce `h1`. Apply `hξ` to reduce the goal to its premises.

Simplify using `[h1]`. Establish `hmem : ξ ∈ Metric.ball e δ`. Establish `h1 : ξ ∈ Function.support φ` using `hφ`. Rewrite `h1` using `[φ.support_eq]`. Conclude with `Metric.ball_subset_ball (show δ / 2 ≤ δ by linarith) h1`.

Establish `h2 : y = -(A (ξ - e)) y` using `eq_neg_of_add_eq_zero_left hy`. Establish `h3 : ‖y‖ ≤ 1 / 2 * ‖y‖`. Combine the equalities or inequalities in the displayed calculation. Conclude with `norm_neg _`. Use `_ ≤ ‖A (ξ - e)‖ * ‖y‖ := (A (ξ - e)).le_opNorm y`.

Use `_ ≤ 1 / 2 * ‖y‖ := mul_le_mul_of_nonneg_right (hball ξ hmem) (norm_nonneg _)`. Establish `h4 : ‖y‖ = 0` using `le_antisymm (by linarith [norm_nonneg y]) (norm_nonneg y)`. Conclude with `norm_eq_zero.mp h4`. Introduce `α`. Establish `hh : ContDiff ℝ ∞ (fun ξ => ((φ ξ : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp φ.contDiff`.

Establish `hhc : HasCompactSupport (fun ξ => ((φ ξ : ℝ) : ℂ))` using `φ.hasCompactSupport.comp_left Complex.ofReal_zero`. Take `⟨G0, hG0⟩` from `hT V M (fun ξ => ((φ ξ : ℝ) : ℂ)) hh hhc α`. Establish `hg : Function.HasTemperateGrowth g`. Apply `HasCompactSupport.hasTemperateGrowth` to reduce the goal to its premises. Conclude with `χ.hasCompactSupport.smul_right (f' := fun ξ => A (ξ - e))`.

Conclude with `χ.contDiff.smul (A.contDiff.comp (contDiff_id.sub contDiff_const))`. Set `Φ : V × M → V × M` to `fun p => p + ContinuousLinearMap.inr ℝ V M (g p.1 p.2)`. Establish `hΦ : Function.HasTemperateGrowth Φ`. Establish `h1 : Function.HasTemperateGrowth (fun p : V × M => g p.1)` using `hg.comp (ContinuousLinearMap.fst ℝ V M).hasTemperateGrowth`. Establish `h2 : Function.HasTemperateGrowth (fun p : V × M => g p.1 p.2)` using `(ContinuousLinearMap.id ℝ (M →L[ℝ] M)).bilinear_hasTemperateGrowth h1 (ContinuousLinearMap.snd ℝ V M).hasTemperateGrowth`.

Conclude with `Function.HasTemperateGrowth.add Function.HasTemperateGrowth.id ((ContinuousLinearMap.inr ℝ V M).hasTemperateGrowth.comp h2)`. Establish `hΦp : ∀ p : V × M, Φ p = (p.1, p.2 + g p.1 p.2)`. Introduce `p`. Apply the tactic sequence `ext <;> simp [Φ]`. Establish `hup : ∃ (k : ℕ) (C : ℝ), ∀ p, ‖p‖ ≤ C * (1 + ‖Φ p‖) ^ k`.

Use `⟨1, 2, fun p => ?_⟩` and prove the remaining obligations. Establish `e1 : ‖p.2‖ ≤ ‖p.2 + g p.1 p.2‖ + ‖g p.1 p.2‖`. Simplify using `using norm_sub_le (p.2 + g p.1 p.2) (g p.1 p.2)`. Establish `e2 : ‖g p.1 p.2‖ ≤ 1 / 2 * ‖p.2‖` using `((g p.1).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hsmall _) (norm_nonneg _))`. Establish `e3 : ‖p.2 + g p.1 p.2‖ ≤ ‖Φ p‖`.

Rewrite using `[hΦp]`. Conclude with `norm_snd_le (p.1, p.2 + g p.1 p.2)`. Establish `e4 : ‖p.1‖ ≤ ‖Φ p‖`. Rewrite using `[hΦp]`. Conclude with `norm_fst_le (p.1, p.2 + g p.1 p.2)`.

Rewrite using `[pow_one]`. Apply the tactic sequence `refine norm_prod_le_iff.mpr ⟨?_, ?_⟩ <;> nlinarith [norm_nonneg (Φ p), norm_nonneg p.2]`. Use `⟨SchwartzMap.compCLM ℂ hΦ hup G0, fun ξ y => ?_⟩` and prove the remaining obligations. Rewrite using `[SchwartzMap.compCLM_apply, Function.comp_apply, hΦp, hG0]`. Distinguish the cases in `hφ : φ ξ = 0`.

Simplify using `[hφ]`. Establish `hmem : ξ ∈ Metric.closedBall e χ.rIn`. Establish `h1 : ξ ∈ Function.support φ` using `hφ`. Rewrite `h1` using `[φ.support_eq]`. Conclude with `Metric.ball_subset_closedBall h1`.

Simplify using `[g, χ.one_of_mem_closedBall hmem]`.
-/
theorem UpperTheory.V.Af.Smo.schTw :
    UpperTheory.V.Af.Smo.SchTensor → UpperTheory.V.Af.Smo.SchTw := by
  intro hT V M _ _ _ _ _ _ A e
  obtain ⟨δ, hδ, hAδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ‖A‖ * δ ≤ 1 / 2 := by
    refine ⟨1 / (2 * (‖A‖ + 1)), by positivity, ?_⟩
    have h0 : 0 ≤ ‖A‖ := norm_nonneg _
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hball : ∀ ξ ∈ Metric.ball e δ, ‖A (ξ - e)‖ ≤ 1 / 2 := by
    intro ξ hξ
    calc ‖A (ξ - e)‖ ≤ ‖A‖ * ‖ξ - e‖ := A.le_opNorm _
      _ ≤ ‖A‖ * δ := by
        gcongr
        rw [← dist_eq_norm]
        exact (Metric.mem_ball.mp hξ).le
      _ ≤ 1 / 2 := hAδ
  let φ : ContDiffBump e := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  let χ : ContDiffBump e := ⟨δ / 2, δ, by positivity, by linarith⟩
  let g : V → (M →L[ℝ] M) := fun ξ => χ ξ • A (ξ - e)
  have hsmall : ∀ ξ : V, ‖g ξ‖ ≤ 1 / 2 := by
    intro ξ
    by_cases hξ : χ ξ = 0
    · simp [g, hξ]
    · have hmem : ξ ∈ Metric.ball e δ := by
        have h1 : ξ ∈ Function.support χ := hξ
        rwa [χ.support_eq] at h1
      simp only [g]
      rw [norm_smul, Real.norm_of_nonneg χ.nonneg]
      calc χ ξ * ‖A (ξ - e)‖ ≤ 1 * (1 / 2) := by
            gcongr
            · exact χ.le_one
            · exact hball ξ hmem
        _ = 1 / 2 := by norm_num
  refine ⟨fun ξ => ((φ ξ : ℝ) : ℂ), ?_, ?_, ?_⟩
  · have h1 : φ e = 1 := φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le)
    simp [h1]
  · intro ξ hξ y hy
    have hφ : φ ξ ≠ 0 := by
      intro h1
      apply hξ
      simp [h1]
    have hmem : ξ ∈ Metric.ball e δ := by
      have h1 : ξ ∈ Function.support φ := hφ
      rw [φ.support_eq] at h1
      exact Metric.ball_subset_ball (show δ / 2 ≤ δ by linarith) h1
    have h2 : y = -(A (ξ - e)) y := eq_neg_of_add_eq_zero_left hy
    have h3 : ‖y‖ ≤ 1 / 2 * ‖y‖ := by
      calc ‖y‖ = ‖(A (ξ - e)) y‖ := by
            conv_lhs => rw [h2]
            exact norm_neg _
        _ ≤ ‖A (ξ - e)‖ * ‖y‖ := (A (ξ - e)).le_opNorm y
        _ ≤ 1 / 2 * ‖y‖ := mul_le_mul_of_nonneg_right (hball ξ hmem) (norm_nonneg _)
    have h4 : ‖y‖ = 0 := le_antisymm (by linarith [norm_nonneg y]) (norm_nonneg y)
    exact norm_eq_zero.mp h4
  · intro α
    have hh : ContDiff ℝ ∞ (fun ξ => ((φ ξ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp φ.contDiff
    have hhc : HasCompactSupport (fun ξ => ((φ ξ : ℝ) : ℂ)) :=
      φ.hasCompactSupport.comp_left Complex.ofReal_zero
    obtain ⟨G0, hG0⟩ := hT V M (fun ξ => ((φ ξ : ℝ) : ℂ)) hh hhc α
    have hg : Function.HasTemperateGrowth g := by
      apply HasCompactSupport.hasTemperateGrowth
      · exact χ.hasCompactSupport.smul_right (f' := fun ξ => A (ξ - e))
      · exact χ.contDiff.smul (A.contDiff.comp (contDiff_id.sub contDiff_const))
    let Φ : V × M → V × M := fun p => p + ContinuousLinearMap.inr ℝ V M (g p.1 p.2)
    have hΦ : Function.HasTemperateGrowth Φ := by
      have h1 : Function.HasTemperateGrowth (fun p : V × M => g p.1) :=
        hg.comp (ContinuousLinearMap.fst ℝ V M).hasTemperateGrowth
      have h2 : Function.HasTemperateGrowth (fun p : V × M => g p.1 p.2) :=
        (ContinuousLinearMap.id ℝ (M →L[ℝ] M)).bilinear_hasTemperateGrowth h1
          (ContinuousLinearMap.snd ℝ V M).hasTemperateGrowth
      exact Function.HasTemperateGrowth.add Function.HasTemperateGrowth.id
        ((ContinuousLinearMap.inr ℝ V M).hasTemperateGrowth.comp h2)
    have hΦp : ∀ p : V × M, Φ p = (p.1, p.2 + g p.1 p.2) := by
      intro p
      ext <;> simp [Φ]
    have hup : ∃ (k : ℕ) (C : ℝ), ∀ p, ‖p‖ ≤ C * (1 + ‖Φ p‖) ^ k := by
      refine ⟨1, 2, fun p => ?_⟩
      have e1 : ‖p.2‖ ≤ ‖p.2 + g p.1 p.2‖ + ‖g p.1 p.2‖ := by
        simpa using norm_sub_le (p.2 + g p.1 p.2) (g p.1 p.2)
      have e2 : ‖g p.1 p.2‖ ≤ 1 / 2 * ‖p.2‖ :=
        ((g p.1).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hsmall _) (norm_nonneg _))
      have e3 : ‖p.2 + g p.1 p.2‖ ≤ ‖Φ p‖ := by
        rw [hΦp]
        exact norm_snd_le (p.1, p.2 + g p.1 p.2)
      have e4 : ‖p.1‖ ≤ ‖Φ p‖ := by
        rw [hΦp]
        exact norm_fst_le (p.1, p.2 + g p.1 p.2)
      rw [pow_one]
      refine norm_prod_le_iff.mpr ⟨?_, ?_⟩ <;> nlinarith [norm_nonneg (Φ p), norm_nonneg p.2]
    refine ⟨SchwartzMap.compCLM ℂ hΦ hup G0, fun ξ y => ?_⟩
    rw [SchwartzMap.compCLM_apply, Function.comp_apply, hΦp, hG0]
    by_cases hφ : φ ξ = 0
    · simp [hφ]
    · have hmem : ξ ∈ Metric.closedBall e χ.rIn := by
        have h1 : ξ ∈ Function.support φ := hφ
        rw [φ.support_eq] at h1
        exact Metric.ball_subset_closedBall h1
      simp [g, χ.one_of_mem_closedBall hmem]
