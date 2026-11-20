import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth

/- English proof (translation)
Establish `hc : ContDiff ℝ ∞ (fun q : ℂ × ℝ => circleMap 0 ρ q.2)` using `(contDiff_circleMap 0 ρ).comp contDiff_snd`. Establish `e : (fun q : ℂ × ℝ => pker ρ q.1 q.2) = (fun q : ℂ × ℝ => ‖circleMap 0 ρ q.2 - 0‖ ^ 2 - ‖q.1 - 0‖ ^ 2) / (fun q : ℂ × ℝ => ‖circleMap 0 ρ q.2 - 0 - (q.1 - 0)‖ ^ 2)`. Use function extensionality and compare the values at `q`. Both sides reduce to the same expression. Rewrite using `[e]`.

Use `ContDiffOn.div ?_ ?_ ?_` and prove the remaining obligations. Conclude with `(((contDiff_norm_sq ℝ).comp (hc.sub contDiff_const)).sub ((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_const))).contDiffOn`. Conclude with `((contDiff_norm_sq ℝ).comp ((hc.sub contDiff_const).sub (contDiff_fst.sub contDiff_const))).contDiffOn`. Introduce and unpack `⟨w, t⟩ ⟨hw, -⟩`. Establish `hw' : ‖w‖ < ρ` using `mem_ball_zero_iff.mp hw`.

Establish `hne : circleMap 0 ρ t - 0 - (w - 0) ≠ 0`. Introduce `h0`. Establish `h1 : circleMap 0 ρ t = w` using `by simpa [sub_eq_zero] using h0`. Establish `hn` using `norm_circleMap_zero ρ t`. Rewrite `hn` using `[h1, abs_of_pos hρ]`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)`.
-/
theorem contDiffOn_pker {ρ : ℝ} (hρ : 0 < ρ) :
    ContDiffOn ℝ ∞ (fun q : ℂ × ℝ => pker ρ q.1 q.2)
      (Metric.ball (0 : ℂ) ρ ×ˢ (Set.univ : Set ℝ)) := by
  have hc : ContDiff ℝ ∞ (fun q : ℂ × ℝ => circleMap 0 ρ q.2) := (contDiff_circleMap 0 ρ).comp contDiff_snd
  have e : (fun q : ℂ × ℝ => pker ρ q.1 q.2) =
      (fun q : ℂ × ℝ => ‖circleMap 0 ρ q.2 - 0‖ ^ 2 - ‖q.1 - 0‖ ^ 2) /
        (fun q : ℂ × ℝ => ‖circleMap 0 ρ q.2 - 0 - (q.1 - 0)‖ ^ 2) := by
    funext q
    rfl
  rw [e]
  refine ContDiffOn.div ?_ ?_ ?_
  · exact (((contDiff_norm_sq ℝ).comp (hc.sub contDiff_const)).sub
      ((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_const))).contDiffOn
  · exact ((contDiff_norm_sq ℝ).comp ((hc.sub contDiff_const).sub (contDiff_fst.sub contDiff_const))).contDiffOn
  · rintro ⟨w, t⟩ ⟨hw, -⟩
    have hw' : ‖w‖ < ρ := mem_ball_zero_iff.mp hw
    have hne : circleMap 0 ρ t - 0 - (w - 0) ≠ 0 := by
      intro h0
      have h1 : circleMap 0 ρ t = w := by simpa [sub_eq_zero] using h0
      have hn := norm_circleMap_zero ρ t
      rw [h1, abs_of_pos hρ] at hn
      linarith
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)

/- English proof (translation)
Establish `hmaps : ∀ i : Fin n, Set.MapsTo (fun q : (Fin n → ℂ) × (Fin n → ℝ) => (q.1 i, q.2 i)) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) (Metric.ball (0 : ℂ) ρ ×ˢ (Set.univ : Set ℝ))`. Introduce and unpack `i ⟨z, θ⟩ ⟨hz, -⟩`. Use `Set.mk_mem_prod ?_ (Set.mem_univ _)` and prove the remaining obligations. Rewrite `hz`, the goal using `[mem_ball_zero_iff]`. Conclude with `lt_of_le_of_lt (norm_le_pi_norm z i) hz`.

Establish `hlin : ∀ i : Fin n, ContDiff ℝ ∞ (fun q : (Fin n → ℂ) × (Fin n → ℝ) => (q.1 i, q.2 i))` using `fun i => ((contDiff_apply ℝ ℂ i).comp contDiff_fst).prodMk ((contDiff_apply ℝ ℝ i).comp contDiff_snd)`. Establish `hcomp : ∀ i : Fin n, ContDiffOn ℝ ∞ ((fun q : ℂ × ℝ => pker ρ q.1 q.2) ∘ (fun q : (Fin n → ℂ) × (Fin n → ℝ) => (q.1 i, q.2 i))) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ)))` using `fun i => (contDiffOn_pker hρ).comp (hlin i).contDiffOn (hmaps i)`. Establish `hi : ∀ i : Fin n, ContDiffOn ℝ ∞ (fun q : (Fin n → ℂ) × (Fin n → ℝ) => pker ρ (q.1 i) (q.2 i)) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ)))` using `hcomp`. Conclude with `contDiffOn_prod (fun i _ => hi i)`.
-/
theorem contDiffOn_prod_pker {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    ContDiffOn ℝ ∞ (fun q : (Fin n → ℂ) × (Fin n → ℝ) => ∏ i, pker ρ (q.1 i) (q.2 i))
      (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) := by
  have hmaps : ∀ i : Fin n, Set.MapsTo (fun q : (Fin n → ℂ) × (Fin n → ℝ) => (q.1 i, q.2 i))
      (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) (Metric.ball (0 : ℂ) ρ ×ˢ (Set.univ : Set ℝ)) := by
    rintro i ⟨z, θ⟩ ⟨hz, -⟩
    refine Set.mk_mem_prod ?_ (Set.mem_univ _)
    rw [mem_ball_zero_iff] at hz ⊢
    exact lt_of_le_of_lt (norm_le_pi_norm z i) hz
  have hlin : ∀ i : Fin n, ContDiff ℝ ∞ (fun q : (Fin n → ℂ) × (Fin n → ℝ) => (q.1 i, q.2 i)) := fun i =>
    ((contDiff_apply ℝ ℂ i).comp contDiff_fst).prodMk ((contDiff_apply ℝ ℝ i).comp contDiff_snd)
  have hcomp : ∀ i : Fin n, ContDiffOn ℝ ∞
      ((fun q : ℂ × ℝ => pker ρ q.1 q.2) ∘ (fun q : (Fin n → ℂ) × (Fin n → ℝ) => (q.1 i, q.2 i))) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
    fun i => (contDiffOn_pker hρ).comp (hlin i).contDiffOn (hmaps i)
  have hi : ∀ i : Fin n, ContDiffOn ℝ ∞ (fun q : (Fin n → ℂ) × (Fin n → ℝ) => pker ρ (q.1 i) (q.2 i)) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
    hcomp
  exact contDiffOn_prod (fun i _ => hi i)

/- English proof (translation)
Establish `h1 : ∀ᵐ t ∂angMeas, t ∈ Set.Ioc 0 (2 * Real.pi)` using `Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem measurableSet_Ioc)`. Rewrite using `[ae_all_iff]`. Introduce `i`. Conclude with `Measure.tendsto_eval_ae_ae.eventually h1`.
-/
theorem ae_mem_box (n : ℕ) :
    ∀ᵐ θ ∂(Measure.pi fun _ : Fin n => angMeas), ∀ i, θ i ∈ Set.Ioc 0 (2 * Real.pi) := by
  have h1 : ∀ᵐ t ∂angMeas, t ∈ Set.Ioc 0 (2 * Real.pi) :=
    Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem measurableSet_Ioc)
  rw [ae_all_iff]
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually h1

/- English proof (translation)
Establish `hopen : IsOpen (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ)))` using `Metric.isOpen_ball.prod isOpen_univ`. Establish `hK : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) (2 * Real.pi))` using `isCompact_univ_pi fun _ => isCompact_Icc`. Establish `hbox : ∀ᵐ θ ∂(Measure.pi fun _ : Fin n => angMeas), θ ∈ Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) (2 * Real.pi)` using `by filter_upwards [ae_mem_box n] with θ hθ`. Conclude with `fun i _ => Set.Ioc_subset_Icc_self (hθ i)`. Take `⟨Cg, hCg⟩` from `hK.exists_bound_of_continuousOn hg.continuousOn`.

Establish `key : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (G : (Fin n → ℂ) × (Fin n → ℝ) → E), ContDiffOn ℝ ∞ G (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) → ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ, HasFDerivAt (fun z => ∫ θ, g θ • G (z, θ) ∂( …`. Introduce `E _ _ _ G hG z₀ hz₀`. Establish `hGd` using `(contDiffOn_infty_iff_fderiv_of_isOpen hopen).mp hG`. Establish `hz₀' : ‖z₀‖ < ρ` using `mem_ball_zero_iff.mp hz₀`. Take `⟨r, hr, hrdef⟩ : ∃ r : ℝ, 0 < r ∧ r = (ρ - ‖z₀‖) / 2` from `⟨_, by linarith, rfl⟩`.

Establish `hsub : Metric.closedBall z₀ r ⊆ Metric.ball (0 : Fin n → ℂ) ρ`. Introduce `z hz`. Rewrite `hz` using `[Metric.mem_closedBall, dist_eq_norm]`. Rewrite using `[mem_ball_zero_iff]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hSK : IsCompact (Metric.closedBall z₀ r ×ˢ Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) (2 * Real.pi))` using `(isCompact_closedBall z₀ r).prod hK`. Establish `hSsub : (Metric.closedBall z₀ r ×ˢ Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) (2 * Real.pi)) ⊆ Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))` using `Set.prod_mono hsub (Set.subset_univ _)`. Establish `hGc : ContinuousOn G (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ)))` using `hG.continuousOn`. Establish `hG'c : ContinuousOn (fun p => (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ)))` using `hGd.2.continuousOn.clm_comp continuousOn_const`. Take `⟨C, hC⟩` from `hSK.exists_bound_of_continuousOn (hG'c.mono hSsub)`.

Take `⟨C0, hC0⟩` from `hSK.exists_bound_of_continuousOn (hGc.mono hSsub)`. Establish `hslice : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, Continuous fun θ => g θ • G (z, θ)` using `fun z hz => hg.smul (hGc.comp_continuous (continuous_const.prodMk continuous_id) (fun θ => Set.mk_mem_prod hz (Set.mem_univ θ)))`. Establish `hslice' : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, Continuous fun θ => g θ • (fderiv ℝ G (z, θ)).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))` using `fun z hz => hg.smul (hG'c.comp_continuous (continuous_const.prodMk continuous_id) (fun θ => Set.mk_mem_prod hz (Set.mem_univ θ)))`. Establish `hball : Metric.ball z₀ r ⊆ Metric.ball (0 : Fin n → ℂ) ρ` using `Metric.ball_subset_closedBall.trans hsub`. Use `hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun z θ => g θ • G (z, θ)) (F' := fun z θ => g θ • (fderiv ℝ G (z, θ)).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))) (bound := fun _ => Cg * C) (Metric.ball_mem_nhds z₀ hr) ?_ ?_ ?_ ?_ (integrable_const _) ?_` and prove the remaining obligations.

Use `filter_upwards [Metric.isOpen_ball.mem_nhds hz₀] with z hz`. Conclude with `(hslice z hz).aestronglyMeasurable`. Use `Integrable.mono' (integrable_const (Cg * C0)) (hslice z₀ hz₀).aestronglyMeasurable ?_ filter_upwards [hbox] with θ hθ show ‖g θ • G (z₀, θ)‖ ≤ Cg * C0` and prove the remaining obligations. Rewrite using `[norm_smul]`. Conclude with `mul_le_mul (hCg θ hθ) (hC0 (z₀, θ) (Set.mk_mem_prod (Metric.mem_closedBall_self hr.le) hθ)) (norm_nonneg _) ((norm_nonneg _).trans (hCg θ hθ))`.

Conclude with `(hslice' z₀ hz₀).aestronglyMeasurable`. Use `filter_upwards [hbox] with θ hθ z hz show ‖g θ • (fderiv ℝ G (z, θ)).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))‖ ≤ Cg * C`. Rewrite using `[norm_smul]`. Conclude with `mul_le_mul (hCg θ hθ) (hC (z, θ) (Set.mk_mem_prod (Metric.ball_subset_closedBall hz) hθ)) (norm_nonneg _) ((norm_nonneg _).trans (hCg θ hθ))`. Use `filter_upwards with θ z hz`.

Establish `hz' : z ∈ Metric.ball (0 : Fin n → ℂ) ρ` using `hball hz`. Establish `hd : DifferentiableAt ℝ G (z, θ)` using `hGd.1.differentiableAt (hopen.mem_nhds (Set.mk_mem_prod hz' (Set.mem_univ θ)))`. Conclude with `(hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_left z θ)).const_smul (g θ)`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `E _ _ _ G hG`. Rewrite using `[Nat.cast_zero, contDiffOn_zero]`. Conclude with `fun z hz => (key E G hG z hz).continuousAt.continuousWithinAt`. Consider the case `succ k ih`.

Introduce `E _ _ _ G hG`. Establish `hGd` using `(contDiffOn_infty_iff_fderiv_of_isOpen hopen).mp hG`. Establish `hG' : ContDiffOn ℝ ∞ (fun p => (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ)))` using `hGd.2.clm_comp contDiffOn_const`. Rewrite using `[Nat.cast_succ]`. Use `(contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball).mpr ⟨fun z hz => (key E G hG z hz).differentiableAt.differentiableWithinAt, fun h => by simp at h, ?_⟩` and prove the remaining obligations.

Conclude with `(ih _ _ hG').congr fun z hz => (key E G hG z hz).fderiv`.
-/
private theorem contDiffOn_integral_angMeas {n : ℕ} {ρ : ℝ} (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) :
    ∀ (k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (G : (Fin n → ℂ) × (Fin n → ℝ) → E),
      ContDiffOn ℝ ∞ G (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) →
      ContDiffOn ℝ k (fun z => ∫ θ, g θ • G (z, θ) ∂(Measure.pi fun _ : Fin n => angMeas)) (Metric.ball (0 : Fin n → ℂ) ρ) := by
  have hopen : IsOpen (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) := Metric.isOpen_ball.prod isOpen_univ
  have hK : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hbox : ∀ᵐ θ ∂(Measure.pi fun _ : Fin n => angMeas), θ ∈ Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) (2 * Real.pi) := by
    filter_upwards [ae_mem_box n] with θ hθ
    exact fun i _ => Set.Ioc_subset_Icc_self (hθ i)
  obtain ⟨Cg, hCg⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  have key : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (G : (Fin n → ℂ) × (Fin n → ℝ) → E), ContDiffOn ℝ ∞ G (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) →
      ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ,
        HasFDerivAt (fun z => ∫ θ, g θ • G (z, θ) ∂(Measure.pi fun _ : Fin n => angMeas))
          (∫ θ, g θ • (fderiv ℝ G (z₀, θ)).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ)) ∂(Measure.pi fun _ : Fin n => angMeas)) z₀ := by
    intro E _ _ _ G hG z₀ hz₀
    have hGd := (contDiffOn_infty_iff_fderiv_of_isOpen hopen).mp hG
    have hz₀' : ‖z₀‖ < ρ := mem_ball_zero_iff.mp hz₀
    obtain ⟨r, hr, hrdef⟩ : ∃ r : ℝ, 0 < r ∧ r = (ρ - ‖z₀‖) / 2 := ⟨_, by linarith, rfl⟩
    have hsub : Metric.closedBall z₀ r ⊆ Metric.ball (0 : Fin n → ℂ) ρ := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      rw [mem_ball_zero_iff]
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ < ρ := by linarith
    have hSK : IsCompact (Metric.closedBall z₀ r ×ˢ Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) (2 * Real.pi)) :=
      (isCompact_closedBall z₀ r).prod hK
    have hSsub : (Metric.closedBall z₀ r ×ˢ Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) (2 * Real.pi)) ⊆ Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ)) :=
      Set.prod_mono hsub (Set.subset_univ _)
    have hGc : ContinuousOn G (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) := hG.continuousOn
    have hG'c : ContinuousOn (fun p => (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
      hGd.2.continuousOn.clm_comp continuousOn_const
    obtain ⟨C, hC⟩ := hSK.exists_bound_of_continuousOn (hG'c.mono hSsub)
    obtain ⟨C0, hC0⟩ := hSK.exists_bound_of_continuousOn (hGc.mono hSsub)
    have hslice : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, Continuous fun θ => g θ • G (z, θ) := fun z hz =>
      hg.smul (hGc.comp_continuous (continuous_const.prodMk continuous_id)
        (fun θ => Set.mk_mem_prod hz (Set.mem_univ θ)))
    have hslice' : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ,
        Continuous fun θ => g θ • (fderiv ℝ G (z, θ)).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ)) := fun z hz =>
      hg.smul (hG'c.comp_continuous (continuous_const.prodMk continuous_id)
        (fun θ => Set.mk_mem_prod hz (Set.mem_univ θ)))
    have hball : Metric.ball z₀ r ⊆ Metric.ball (0 : Fin n → ℂ) ρ := Metric.ball_subset_closedBall.trans hsub
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun z θ => g θ • G (z, θ))
      (F' := fun z θ => g θ • (fderiv ℝ G (z, θ)).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))) (bound := fun _ => Cg * C)
      (Metric.ball_mem_nhds z₀ hr) ?_ ?_ ?_ ?_ (integrable_const _) ?_
    · filter_upwards [Metric.isOpen_ball.mem_nhds hz₀] with z hz
      exact (hslice z hz).aestronglyMeasurable
    · refine Integrable.mono' (integrable_const (Cg * C0)) (hslice z₀ hz₀).aestronglyMeasurable ?_
      filter_upwards [hbox] with θ hθ
      show ‖g θ • G (z₀, θ)‖ ≤ Cg * C0
      rw [norm_smul]
      exact mul_le_mul (hCg θ hθ) (hC0 (z₀, θ) (Set.mk_mem_prod (Metric.mem_closedBall_self hr.le) hθ))
        (norm_nonneg _) ((norm_nonneg _).trans (hCg θ hθ))
    · exact (hslice' z₀ hz₀).aestronglyMeasurable
    · filter_upwards [hbox] with θ hθ z hz
      show ‖g θ • (fderiv ℝ G (z, θ)).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))‖ ≤ Cg * C
      rw [norm_smul]
      exact mul_le_mul (hCg θ hθ) (hC (z, θ) (Set.mk_mem_prod (Metric.ball_subset_closedBall hz) hθ))
        (norm_nonneg _) ((norm_nonneg _).trans (hCg θ hθ))
    · filter_upwards with θ z hz
      have hz' : z ∈ Metric.ball (0 : Fin n → ℂ) ρ := hball hz
      have hd : DifferentiableAt ℝ G (z, θ) :=
        hGd.1.differentiableAt (hopen.mem_nhds (Set.mk_mem_prod hz' (Set.mem_univ θ)))
      exact (hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_left z θ)).const_smul (g θ)
  intro k
  induction k with
  | zero =>
    intro E _ _ _ G hG
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun z hz => (key E G hG z hz).continuousAt.continuousWithinAt
  | succ k ih =>
    intro E _ _ _ G hG
    have hGd := (contDiffOn_infty_iff_fderiv_of_isOpen hopen).mp hG
    have hG' : ContDiffOn ℝ ∞ (fun p => (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
      hGd.2.clm_comp contDiffOn_const
    rw [Nat.cast_succ]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball).mpr
      ⟨fun z hz => (key E G hG z hz).differentiableAt.differentiableWithinAt, fun h => by simp at h, ?_⟩
    exact (ih _ _ hG').congr fun z hz => (key E G hG z hz).fderiv

/- English proof (translation)
Introduce `n ρ h hρ hh`. Establish `e : polyPoisson ρ h = fun z => ∫ θ, h (torusPt ρ θ) • (fun q : (Fin n → ℂ) × (Fin n → ℝ) => ∏ i, pker ρ (q.1 i) (q.2 i)) (z, θ) ∂(Measure.pi fun _ : Fin n => angMeas)`. Use function extensionality and compare the values at `z`. Use `show (∫ θ, (∏ i, pker ρ (z i) (θ i)) * h (torusPt ρ θ) ∂(Measure.pi fun _ : Fin n => angMeas)) = _`. Use `congr 1`.

Use function extensionality and compare the values at `θ`. Rewrite using `[smul_eq_mul, mul_comm]`. Rewrite using `[e, contDiffOn_infty]`. Introduce `k`. Conclude with `contDiffOn_integral_angMeas _ hh k ℝ _ (contDiffOn_prod_pker hρ)`.
-/
theorem contDiffOn_polyPoisson :
    ∀ (n : ℕ) (ρ : ℝ) (h : (Fin n → ℂ) → ℝ), 0 < ρ →
      Continuous (fun θ : Fin n → ℝ => h (torusPt ρ θ)) →
      ContDiffOn ℝ ∞ (polyPoisson ρ h) (Metric.ball 0 ρ) := by
  intro n ρ h hρ hh
  have e : polyPoisson ρ h = fun z => ∫ θ, h (torusPt ρ θ) •
      (fun q : (Fin n → ℂ) × (Fin n → ℝ) => ∏ i, pker ρ (q.1 i) (q.2 i)) (z, θ) ∂(Measure.pi fun _ : Fin n => angMeas) := by
    funext z
    show (∫ θ, (∏ i, pker ρ (z i) (θ i)) * h (torusPt ρ θ) ∂(Measure.pi fun _ : Fin n => angMeas)) = _
    congr 1
    funext θ
    rw [smul_eq_mul, mul_comm]
  rw [e, contDiffOn_infty]
  intro k
  exact contDiffOn_integral_angMeas _ hh k ℝ _ (contDiffOn_prod_pker hρ)

end GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth
