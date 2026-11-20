import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.ChartIntegralLocal

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/- English proof (translation)
Establish `hcurve : ∀ t, cv b X t g ∈ GV k r` using `fun t => cv_mem hX hg t`. Establish `hd : ∀ ξ, ∀ g₁ ∈ GV k r, HasDerivAt (fun s : ℝ => G ξ (cv b X s g₁)) (op b X (G ξ) g₁) 0` using `fun ξ g₁ hg₁ => (ckOn_diff 0 b (hG1 ξ) hX hg₁).hasDerivAt`. Establish `hsm : ∀ ξ (e : E), ‖ψ ξ • e‖ ≤ ‖e‖` using `fun ξ e => by`. Rewrite using `[norm_smul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)`.

Establish `hs : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ)` using `Metric.ball_mem_nhds 0 hε`. Establish `h00 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) ε` using `Metric.mem_ball_self hε`. Establish `hm0 : AEStronglyMeasurable (fun ξ => G ξ (cv b X 0 g)) μ` using `hGm 0 h00`. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ) (bound := β) (F := fun t ξ => ψ ξ • G ξ (cv b X t g)) (x₀ := 0) (s := Metric.ball 0 ε) hs (Filter.mem_of_superset hs fun t ht => hψm.smul (hGm t ht)) (hβ.mono' (hψm.smul hm0) (Eventually.of_forall fun ξ => (hsm ξ …`. Establish `e : (fun t' : ℝ => G ξ (cv b X t' g)) = fun t' => G ξ (cv b X (t' - t) (cv b X t g))`.

Use function extensionality and compare the values at `t'`. Rewrite using `[← cv_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : HasDerivAt (fun s => G ξ (cv b X s (cv b X t g))) (op b X (G ξ) (cv b X t g)) (t - t)`.

Rewrite using `[sub_self]`. Conclude with `hd ξ _ (hcurve t)`. Establish `h3` using `(h2.comp_sub_const t t)`. Rewrite `h3` using `[← e]`. Conclude with `h3.const_smul (ψ ξ))`.

Establish `e1 : (fun t : ℝ => Φ (cv b X t g)) =ᶠ[𝓝 0] fun t => ∫ ξ, ψ ξ • G ξ (cv b X t g) ∂μ` using `Filter.mem_of_superset hs fun t ht => hΦ t ht`. Use `show deriv (fun t : ℝ => Φ (cv b X t g)) 0 = _`. Rewrite using `[e1.deriv_eq, key.2.deriv]`. Simplify using `only [cv_zero]`.
-/
lemma step_loc {b : Bool} {X : Mat k r} (hX : inLie k r X) (ψ : α → ℂ) (hψ : ∀ ξ, ‖ψ ξ‖ ≤ 1)
    (hψm : AEStronglyMeasurable ψ μ) (G : α → Mat k r → E) (hG1 : ∀ ξ, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (G ξ))
    {g : Mat k r} (hg : g ∈ GV k r) {ε : ℝ} (hε : 0 < ε)
    (hGm : ∀ t ∈ Metric.ball (0 : ℝ) ε, AEStronglyMeasurable (fun ξ => G ξ (cv b X t g)) μ)
    (hG'm : AEStronglyMeasurable (fun ξ => op b X (G ξ) g) μ)
    (β : α → ℝ) (hβ : Integrable β μ)
    (hb0 : ∀ ξ, ‖G ξ g‖ ≤ β ξ) (hb1 : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ ξ, ‖op b X (G ξ) (cv b X t g)‖ ≤ β ξ)
    (Φ : Mat k r → E) (hΦ : ∀ t ∈ Metric.ball (0 : ℝ) ε, Φ (cv b X t g) = ∫ ξ, ψ ξ • G ξ (cv b X t g) ∂μ) :
    op b X Φ g = ∫ ξ, ψ ξ • op b X (G ξ) g ∂μ := by
  have hcurve : ∀ t, cv b X t g ∈ GV k r := fun t => cv_mem hX hg t
  have hd : ∀ ξ, ∀ g₁ ∈ GV k r, HasDerivAt (fun s : ℝ => G ξ (cv b X s g₁)) (op b X (G ξ) g₁) 0 :=
    fun ξ g₁ hg₁ => (ckOn_diff 0 b (hG1 ξ) hX hg₁).hasDerivAt
  have hsm : ∀ ξ (e : E), ‖ψ ξ • e‖ ≤ ‖e‖ := fun ξ e => by
    rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)
  have hs : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hε
  have h00 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) ε := Metric.mem_ball_self hε
  have hm0 : AEStronglyMeasurable (fun ξ => G ξ (cv b X 0 g)) μ := hGm 0 h00
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ) (bound := β)
    (F := fun t ξ => ψ ξ • G ξ (cv b X t g)) (x₀ := 0) (s := Metric.ball 0 ε) hs
    (Filter.mem_of_superset hs fun t ht => hψm.smul (hGm t ht))
    (hβ.mono' (hψm.smul hm0) (Eventually.of_forall fun ξ => (hsm ξ _).trans (by rw [cv_zero]; exact hb0 ξ)))
    (F' := fun t ξ => ψ ξ • op b X (G ξ) (cv b X t g))
    (by simp only [cv_zero]; exact hψm.smul hG'm)
    (Eventually.of_forall fun ξ t ht => (hsm ξ _).trans (hb1 t ht ξ)) hβ
    (Eventually.of_forall fun ξ t _ => by
      have e : (fun t' : ℝ => G ξ (cv b X t' g)) = fun t' => G ξ (cv b X (t' - t) (cv b X t g)) := by
        funext t'; rw [← cv_add]; congr 2; ring
      have h2 : HasDerivAt (fun s => G ξ (cv b X s (cv b X t g))) (op b X (G ξ) (cv b X t g)) (t - t) := by
        rw [sub_self]; exact hd ξ _ (hcurve t)
      have h3 := (h2.comp_sub_const t t)
      rw [← e] at h3
      exact h3.const_smul (ψ ξ))
  have e1 : (fun t : ℝ => Φ (cv b X t g)) =ᶠ[𝓝 0] fun t => ∫ ξ, ψ ξ • G ξ (cv b X t g) ∂μ :=
    Filter.mem_of_superset hs fun t ht => hΦ t ht
  show deriv (fun t : ℝ => Φ (cv b X t g)) 0 = _
  rw [e1.deriv_eq, key.2.deriv]
  simp only [cv_zero]

/- English proof (translation)
Establish `hΩ : Metric.ball (0 : J k r → ℝ) δ ⊆ Dom k r` using `Metric.ball_subset_closedBall.trans hcl`. Establish `hcomp : IsCompact (Metric.closedBall (0 : J k r → ℝ) δ)` using `isCompact_closedBall _ _`. Establish `hac : ContinuousOn (fun Y => ∑ i, ‖aC g0 i Y‖) (Metric.closedBall (0 : J k r → ℝ) δ)` using `continuousOn_finsetSum _ fun i _ => ((aC_cd hg0 i).continuousOn.mono hcl).norm`. Take `⟨Ba, hBa⟩` from `hcomp.exists_bound_of_continuousOn hac`. Establish `hBa' : ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, ∑ i, ‖aC g0 i Y‖ ≤ Ba`.

Introduce `Y hY`. Establish `h1` using `hBa Y (Metric.ball_subset_closedBall hY)`. Rewrite `h1` using `[Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]`. Then use the resulting hypothesis. Establish `hunit : ∀ w : List (J k r), ∀ X ∈ w.map Lt, unitLie k r X`. Introduce `w X hX`.

Take `⟨i, _, rfl⟩` from `List.mem_map.1 hX`. Conclude with `Lt_unit i`. Establish `hckw : ∀ ξ (w : List (J k r)) (m : ℕ), m + w.length ≤ mm → CkOn ((m : ℕ) : ℕ∞) (GV k r) (dLR (w.map Lt) [] (h ξ))`. Introduce `ξ w m hm'`. Rewrite using `[dLR_eq]`.

Conclude with `smooth_on_of_word_derivatives _ (allLie_lr (hunit w) (by simp)) m (ckOn_mono (by rw [length_lr]; simp; omega) (hh ξ))`. Establish `hsm : ∀ ξ (e : E), ‖ψ ξ • e‖ ≤ ‖e‖` using `fun ξ e => by`. Rewrite using `[norm_smul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)`. Establish `hbw : ∀ (w : List (J k r)), w.length ≤ mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, ∀ ξ, ‖ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y)‖ ≤ β ξ` using `fun w hw Y hY ξ => (hsm ξ _).trans (hbd w hw Y hY ξ)`.

Establish `hmw : ∀ (w : List (J k r)), w.length ≤ mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, AEStronglyMeasurable (fun ξ => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y)) μ` using `fun w hw Y hY => hψm.smul (hM w hw Y hY)`. Use `set L : List (J k r) → (J k r → ℝ) → E := fun w Y => ∫ ξ, ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y) ∂μ with hL`. Establish `hLc : ∀ w : List (J k r), w.length ≤ mm → ContinuousOn (L w) (Metric.ball (0 : J k r → ℝ) δ)`. Introduce `w hw`. Use `continuousOn_of_dominated (F := fun Y ξ => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y)) (bound := β) (fun Y hY => hmw w hw Y hY) (fun Y hY => Eventually.of_forall fun ξ => hbw w hw Y hY ξ) hβ (Eventually.of_forall fun ξ => ?_)` and prove the remaining obligations.

Conclude with `((cont_chart hg0 (hckw ξ w 0 (by omega))).mono hΩ).const_smul (ψ ξ)`. Establish `hLd : ∀ w : List (J k r), w.length < mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, HasFDerivAt (L w) (∑ i, (aC g0 i Y).smulRight (L (i :: w) Y)) Y`. Introduce `w hw Y hY`. Establish `hD : ∀ ξ, ∀ Y' ∈ Metric.ball (0 : J k r → ℝ) δ, HasFDerivAt (fun Y'' => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y'')) (∑ i, (aC g0 i Y').smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y'))) Y'`. Introduce `ξ Y' hY'`.

Establish `h1` using `(hasFDeriv_chart hg0 (hckw ξ w 1 (by omega)) (hΩ hY')).const_smul (ψ ξ)`. Use `h1.congr_fderiv ?_` and prove the remaining obligations. Use `ext1 W`. Simplify using `only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_comm]`. Both sides reduce to the same expression. Establish `hβ0 : ∀ ξ, 0 ≤ β ξ` using `fun ξ => (norm_nonneg _).trans (hbd [] (by simp) 0 (Metric.mem_ball_self hδp) ξ)`. Establish `hF'm : AEStronglyMeasurable (fun ξ => ∑ i, (aC g0 i Y).smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y))) μ`. Use `Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_` and prove the remaining obligations.

Conclude with `(ContinuousLinearMap.smulRightL ℝ (J k r → ℝ) E (aC g0 i Y)).continuous.comp_aestronglyMeasurable (hmw (i :: w) (by simp; omega) Y hY)`. Establish `hbF' : ∀ ξ, ∀ Y' ∈ Metric.ball (0 : J k r → ℝ) δ, ‖∑ i, (aC g0 i Y').smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y'))‖ ≤ Ba * β ξ`. Introduce `ξ Y' hY'`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ContinuousLinearMap.norm_smulRight_apply]`.

Conclude with `mul_le_mul_of_nonneg_left (hbw (i :: w) (by simp; omega) Y' hY' ξ) (norm_nonneg _)`. Use `_ = (∑ i, ‖aC g0 i Y'‖) * β ξ := by rw [Finset.sum_mul]`. Use `_ ≤ Ba * β ξ := mul_le_mul_of_nonneg_right (hBa' Y' hY') (hβ0 ξ)`. Establish `key` using `hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (𝕜 := ℝ) (F := fun Y' ξ => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y')) (F' := fun Y' ξ => ∑ i, (aC g0 i Y').smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y'))) (bound := fun ξ => Ba * β ξ) (Metric.isOpen_ball.me …`. Use `key.congr_fderiv ?_` and prove the remaining obligations.

Establish `hint : ∀ i, Integrable (fun ξ => ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y)) μ` using `fun i => hβ.mono' (hmw (i :: w) (by simp; omega) Y hY) (Eventually.of_forall fun ξ => hbw (i :: w) (by simp; omega) Y hY ξ)`. Establish `hI : ∀ i, Integrable (fun ξ => (aC g0 i Y).smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y))) μ` using `fun i => (ContinuousLinearMap.smulRightL ℝ (J k r → ℝ) E (aC g0 i Y)).integrable_comp (hint i)`. Rewrite using `[integral_finsetSum _ (fun i _ => hI i)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `(ContinuousLinearMap.smulRightL ℝ (J k r → ℝ) E (aC g0 i Y)).integral_comp_comm (hint i)`.

Establish `hAL` using `ALd (𝔤 := J k r → ℝ) (E := E) Metric.isOpen_ball (aC g0) (fun i => (aC_cd hg0 i).mono hΩ) mm L hLc hLd`. Conclude with `hAL.congr fun Y _ => rfl`.
-/
theorem int_chart_loc (ψ : α → ℂ) (hψ : ∀ ξ, ‖ψ ξ‖ ≤ 1) (hψm : AEStronglyMeasurable ψ μ) (h : α → Mat k r → E)
    (mm : ℕ) (hh : ∀ ξ, CkOn ((mm : ℕ) : ℕ∞) (GV k r) (h ξ)) {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {δ : ℝ}
    (hδp : 0 < δ) (hcl : Metric.closedBall (0 : J k r → ℝ) δ ⊆ Dom k r)
    (hM : ∀ w : List (J k r), w.length ≤ mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ,
      AEStronglyMeasurable (fun ξ => dLR (w.map Lt) [] (h ξ) (chart g0 Y)) μ)
    (β : α → ℝ) (hβ : Integrable β μ)
    (hbd : ∀ w : List (J k r), w.length ≤ mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, ∀ ξ,
      ‖dLR (w.map Lt) [] (h ξ) (chart g0 Y)‖ ≤ β ξ) :
    ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (fun Y => ∫ ξ, ψ ξ • h ξ (chart g0 Y) ∂μ) (Metric.ball 0 δ) := by
  have hΩ : Metric.ball (0 : J k r → ℝ) δ ⊆ Dom k r := Metric.ball_subset_closedBall.trans hcl
  have hcomp : IsCompact (Metric.closedBall (0 : J k r → ℝ) δ) := isCompact_closedBall _ _
  have hac : ContinuousOn (fun Y => ∑ i, ‖aC g0 i Y‖) (Metric.closedBall (0 : J k r → ℝ) δ) :=
    continuousOn_finsetSum _ fun i _ => ((aC_cd hg0 i).continuousOn.mono hcl).norm
  obtain ⟨Ba, hBa⟩ := hcomp.exists_bound_of_continuousOn hac
  have hBa' : ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, ∑ i, ‖aC g0 i Y‖ ≤ Ba := by
    intro Y hY
    have h1 := hBa Y (Metric.ball_subset_closedBall hY)
    rwa [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1
  have hunit : ∀ w : List (J k r), ∀ X ∈ w.map Lt, unitLie k r X := by
    intro w X hX
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hX
    exact Lt_unit i
  have hckw : ∀ ξ (w : List (J k r)) (m : ℕ), m + w.length ≤ mm →
      CkOn ((m : ℕ) : ℕ∞) (GV k r) (dLR (w.map Lt) [] (h ξ)) := by
    intro ξ w m hm'
    rw [dLR_eq]
    exact smooth_on_of_word_derivatives _ (allLie_lr (hunit w) (by simp)) m (ckOn_mono (by rw [length_lr]; simp; omega) (hh ξ))
  have hsm : ∀ ξ (e : E), ‖ψ ξ • e‖ ≤ ‖e‖ := fun ξ e => by
    rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)
  have hbw : ∀ (w : List (J k r)), w.length ≤ mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, ∀ ξ,
      ‖ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y)‖ ≤ β ξ := fun w hw Y hY ξ =>
    (hsm ξ _).trans (hbd w hw Y hY ξ)
  have hmw : ∀ (w : List (J k r)), w.length ≤ mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ,
      AEStronglyMeasurable (fun ξ => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y)) μ := fun w hw Y hY =>
    hψm.smul (hM w hw Y hY)
  set L : List (J k r) → (J k r → ℝ) → E :=
    fun w Y => ∫ ξ, ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y) ∂μ with hL
  have hLc : ∀ w : List (J k r), w.length ≤ mm → ContinuousOn (L w) (Metric.ball (0 : J k r → ℝ) δ) := by
    intro w hw
    refine continuousOn_of_dominated (F := fun Y ξ => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y)) (bound := β)
      (fun Y hY => hmw w hw Y hY) (fun Y hY => Eventually.of_forall fun ξ => hbw w hw Y hY ξ) hβ
      (Eventually.of_forall fun ξ => ?_)
    exact ((cont_chart hg0 (hckw ξ w 0 (by omega))).mono hΩ).const_smul (ψ ξ)
  have hLd : ∀ w : List (J k r), w.length < mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ,
      HasFDerivAt (L w) (∑ i, (aC g0 i Y).smulRight (L (i :: w) Y)) Y := by
    intro w hw Y hY
    have hD : ∀ ξ, ∀ Y' ∈ Metric.ball (0 : J k r → ℝ) δ,
        HasFDerivAt (fun Y'' => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y''))
          (∑ i, (aC g0 i Y').smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y'))) Y' := by
      intro ξ Y' hY'
      have h1 := (hasFDeriv_chart hg0 (hckw ξ w 1 (by omega)) (hΩ hY')).const_smul (ψ ξ)
      refine h1.congr_fderiv ?_
      ext1 W
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
        ContinuousLinearMap.smulRight_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm]
      rfl
    have hβ0 : ∀ ξ, 0 ≤ β ξ := fun ξ =>
      (norm_nonneg _).trans (hbd [] (by simp) 0 (Metric.mem_ball_self hδp) ξ)
    have hF'm : AEStronglyMeasurable (fun ξ => ∑ i, (aC g0 i Y).smulRight
        (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y))) μ := by
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      exact (ContinuousLinearMap.smulRightL ℝ (J k r → ℝ) E (aC g0 i Y)).continuous.comp_aestronglyMeasurable
        (hmw (i :: w) (by simp; omega) Y hY)
    have hbF' : ∀ ξ, ∀ Y' ∈ Metric.ball (0 : J k r → ℝ) δ, ‖∑ i, (aC g0 i Y').smulRight
        (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y'))‖ ≤ Ba * β ξ := by
      intro ξ Y' hY'
      calc _ ≤ ∑ i, ‖(aC g0 i Y').smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y'))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ i, ‖aC g0 i Y'‖ * β ξ := Finset.sum_le_sum fun i _ => by
            rw [ContinuousLinearMap.norm_smulRight_apply]
            exact mul_le_mul_of_nonneg_left (hbw (i :: w) (by simp; omega) Y' hY' ξ) (norm_nonneg _)
        _ = (∑ i, ‖aC g0 i Y'‖) * β ξ := by rw [Finset.sum_mul]
        _ ≤ Ba * β ξ := mul_le_mul_of_nonneg_right (hBa' Y' hY') (hβ0 ξ)
    have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (𝕜 := ℝ)
      (F := fun Y' ξ => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y'))
      (F' := fun Y' ξ => ∑ i, (aC g0 i Y').smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y')))
      (bound := fun ξ => Ba * β ξ) (Metric.isOpen_ball.mem_nhds hY)
      (by filter_upwards [Metric.isOpen_ball.mem_nhds hY] with Y' hY' using hmw w hw.le Y' hY')
      (hβ.mono' (hmw w hw.le Y hY) (Eventually.of_forall fun ξ => hbw w hw.le Y hY ξ))
      hF'm (Eventually.of_forall fun ξ Y' hY' => hbF' ξ Y' hY') (hβ.const_mul Ba)
      (Eventually.of_forall fun ξ Y' hY' => hD ξ Y' hY')
    refine key.congr_fderiv ?_
    have hint : ∀ i, Integrable (fun ξ => ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y)) μ := fun i =>
      hβ.mono' (hmw (i :: w) (by simp; omega) Y hY)
        (Eventually.of_forall fun ξ => hbw (i :: w) (by simp; omega) Y hY ξ)
    have hI : ∀ i, Integrable (fun ξ => (aC g0 i Y).smulRight
        (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y))) μ := fun i =>
      (ContinuousLinearMap.smulRightL ℝ (J k r → ℝ) E (aC g0 i Y)).integrable_comp (hint i)
    rw [integral_finsetSum _ (fun i _ => hI i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (ContinuousLinearMap.smulRightL ℝ (J k r → ℝ) E (aC g0 i Y)).integral_comp_comm (hint i)
  have hAL := ALd (𝔤 := J k r → ℝ) (E := E) Metric.isOpen_ball (aC g0) (fun i => (aC_cd hg0 i).mono hΩ) mm L
    hLc hLd
  exact hAL.congr fun Y _ => rfl

/- English proof (translation)
Establish `hgu : IsUnit g0.det` using `Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0`. Establish `hg1 : g0 * g0⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hgu`. Use `set U := Sr g0 ∩ Formalism.FourierDecayAlt.P.Ux10.rho g0 ⁻¹' Metric.ball (0 : J k r → ℝ) δ with hUdef`. Establish `hUo : IsOpen U` using `(rho_cd g0).continuousOn.isOpen_inter_preimage (sr_open g0) Metric.isOpen_ball`. Establish `hg0U : g0 ∈ U`.

Establish `h2 : (1 + 1 : Mat k r) = (2 : ℂ) • (1 : Mat k r)` using `by rw [two_smul]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show IsUnit (g0 * g0⁻¹ + 1).det`. Rewrite using `[hg1, h2, Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `(isUnit_iff_ne_zero.2 two_ne_zero).pow _`.

Use `show Formalism.FourierDecayAlt.P.Ux10.rho g0 g0 ∈ Metric.ball (0 : J k r → ℝ) δ`. Establish `h3 : Formalism.FourierDecayAlt.P.Ux10.rho g0 g0 = 0`. Use function extensionality and compare the values at `i`. Simplify using `only [Formalism.FourierDecayAlt.P.Ux10.rho, hg1, iot, sub_self, Matrix.zero_mul]`. Conclude with `co_zero i`.

Rewrite using `[h3]`. Conclude with `Metric.mem_ball_self hδ`. Use `⟨U, fun x => F (chart g0 (Formalism.FourierDecayAlt.P.Ux10.rho g0 x)), hUo, hg0U, ?_, ?_⟩` and prove the remaining obligations. Establish `h4 : ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (Formalism.FourierDecayAlt.P.Ux10.rho g0) U` using `((rho_cd g0).mono Set.inter_subset_left).of_le (by exact_mod_cast le_top)`. Conclude with `hAL.comp h4 (by intro x hx; exact hx.2)`.

Introduce `x hx hxG`. Establish `hh : x * g0⁻¹ ∈ GV k r` using `Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hxG (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg0)`. Take `⟨hl, -, hk⟩` from `iot_facts hh hx.1`. Use `show F x = F (kap (prj (Mv (co (iot (x * g0⁻¹))))) * g0)`. Rewrite using `[Mv_co, prj_of_lie hl, hk, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.mul_one]`.
-/
theorem ck_at_of_chart {F : Mat k r → E} {mm : ℕ} {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {δ : ℝ} (hδ : 0 < δ)
    (hAL : ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Metric.ball 0 δ)) :
    ∃ (U : Set (Mat k r)) (F' : Mat k r → E), IsOpen U ∧ g0 ∈ U ∧
      ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) F' U ∧ ∀ g ∈ U, g ∈ GV k r → F g = F' g := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  set U := Sr g0 ∩ Formalism.FourierDecayAlt.P.Ux10.rho g0 ⁻¹' Metric.ball (0 : J k r → ℝ) δ with hUdef
  have hUo : IsOpen U :=
    (rho_cd g0).continuousOn.isOpen_inter_preimage (sr_open g0) Metric.isOpen_ball
  have hg0U : g0 ∈ U := by
    have h2 : (1 + 1 : Mat k r) = (2 : ℂ) • (1 : Mat k r) := by rw [two_smul]
    refine ⟨?_, ?_⟩
    · show IsUnit (g0 * g0⁻¹ + 1).det
      rw [hg1, h2, Matrix.det_smul, Matrix.det_one, mul_one]
      exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _
    · show Formalism.FourierDecayAlt.P.Ux10.rho g0 g0 ∈ Metric.ball (0 : J k r → ℝ) δ
      have h3 : Formalism.FourierDecayAlt.P.Ux10.rho g0 g0 = 0 := by
        funext i
        simp only [Formalism.FourierDecayAlt.P.Ux10.rho, hg1, iot, sub_self, Matrix.zero_mul]
        exact co_zero i
      rw [h3]; exact Metric.mem_ball_self hδ
  refine ⟨U, fun x => F (chart g0 (Formalism.FourierDecayAlt.P.Ux10.rho g0 x)), hUo, hg0U, ?_, ?_⟩
  · have h4 : ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (Formalism.FourierDecayAlt.P.Ux10.rho g0) U :=
      ((rho_cd g0).mono Set.inter_subset_left).of_le (by exact_mod_cast le_top)
    exact hAL.comp h4 (by intro x hx; exact hx.2)
  · intro x hx hxG
    have hh : x * g0⁻¹ ∈ GV k r := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hxG (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg0)
    obtain ⟨hl, -, hk⟩ := iot_facts hh hx.1
    show F x = F (kap (prj (Mv (co (iot (x * g0⁻¹))))) * g0)
    rw [Mv_co, prj_of_lie hl, hk, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.mul_one]

end Formalism.FourierDecayAlt.P.ChartIntegralLocal
