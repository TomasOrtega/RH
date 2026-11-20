import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonReproducesHarmonicStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonSmoothStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DenseCoordinateTorusStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviFlatSeparatelyHarmonicStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncBoundaryCoordinateChartStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodenseStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothInCompatibleChartStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnOfChartCompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviZeroInCompatibleChartStatement
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

/- English proof (translation)
Conclude with `WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)`.
-/
theorem locExt_two_le : (2 : WithTop ℕ∞) ≤ ∞ := by
  exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)

/- English proof (translation)
Establish `h : punct (n` using `n) R = ⋂ i, ({z | z i ≠ 0} ∩ {z | ‖z i‖ < R}) := by`. Use extensionality with `z`. Simplify using `[punct]`. Rewrite using `[h]`. Conclude with `isOpen_iInter_of_finite fun i => (isOpen_ne_fun (continuous_apply i) continuous_const).inter (isOpen_lt (continuous_apply i).norm continuous_const)`.
-/
theorem locExt_isOpen_punct {n : ℕ} (R : ℝ) : IsOpen (punct (n := n) R) := by
  have h : punct (n := n) R = ⋂ i, ({z | z i ≠ 0} ∩ {z | ‖z i‖ < R}) := by
    ext z; simp [punct]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_ne_fun (continuous_apply i) continuous_const).inter
      (isOpen_lt (continuous_apply i).norm continuous_const)

/- English proof (translation)
Establish `h : {z : Fin n → ℂ | ∀ i ∈ S, z i ≠ 0} = ⋂ i ∈ S, {z | z i ≠ 0}`. Use extensionality with `z`. Simplify using the standard rewrite rules. Rewrite using `[h]`. Conclude with `isOpen_biInter_finset fun i _ => isOpen_ne_fun (continuous_apply i) continuous_const`.
-/
theorem locExt_isOpen_nz {n : ℕ} (S : Finset (Fin n)) :
    IsOpen {z : Fin n → ℂ | ∀ i ∈ S, z i ≠ 0} := by
  have h : {z : Fin n → ℂ | ∀ i ∈ S, z i ≠ 0} = ⋂ i ∈ S, {z | z i ≠ 0} := by
    ext z; simp
  rw [h]
  exact isOpen_biInter_finset fun i _ => isOpen_ne_fun (continuous_apply i) continuous_const

/- English proof (translation)
Use `set f : (Fin n → ℂ) → ℝ := fun w => F (c + w) with hf`. Establish `hmem : ∀ w ∈ punct (n` using `n) r, c + w ∈ Metric.ball c r ∩ Q := by`. Introduce `w hw`. Establish `hb : c + w ∈ Metric.ball c r`. Rewrite using `[Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]`.

Conclude with `(pi_norm_lt_iff hr).2 fun i => (hw i).2`. Use `⟨hb, hcov _ hb fun i => ?_⟩` and prove the remaining obligations. Simplify using `using (hw i).1`. Establish `hτ : ∀ w : Fin n → ℂ, ContDiffAt ℝ ∞ (fun w : Fin n → ℂ => c + w) w` using `fun w => contDiffAt_const.add contDiffAt_id`. Establish `hfsm : ∀ w ∈ punct (n` using `n) r, ContDiffAt ℝ ∞ f w := fun w hw => ContDiffAt.comp w (hsm _ (hmem w hw)) (hτ w)`.

Establish `hharm : SepHarm r f`. Use `GlobalTheory.T.levi_flat_separately_harmonic n f (punct r) (locExt_isOpen_punct r) (fun w hw => (hfsm w hw).contDiffWithinAt) ?_` and prove the remaining obligations. Introduce `w hw v`. Establish `hA : AnalyticAt ℂ (fun w : Fin n → ℂ => c + w) w` using `analyticAt_const.add analyticAt_id`. Establish `h2 : ContDiffAt ℝ 2 F (c + w)` using `(hsm _ (hmem w hw)).of_le locExt_two_le`.

Use `levi_comp (φ := F) (τ := fun w : Fin n → ℂ => c + w) (z := w) v hA h2` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `hfc : ContinuousOn f (punct r)` using `fun w hw => (hfsm w hw).continuousAt.continuousWithinAt`. Establish `hpo` using `GlobalTheory.T.polydisc_poisson_reproduces_harmonic n f (r / 2) r B (half_pos hr) (half_lt_self hr) hfc hharm (fun w hw => hB _ (hmem w hw))`. Establish `htor : ∀ θ : Fin n → ℝ, torusPt (r / 2) θ ∈ punct (n` using `n) r := by`.

Introduce `θ i`. Establish `hn : ‖torusPt (r / 2) θ i‖ = r / 2`. Simplify using `only [torusPt]`. Rewrite using `[norm_circleMap_zero, abs_of_pos (half_pos hr)]`. Use `⟨fun h0 => ?_, by rw [hn]; exact half_lt_self hr⟩` and prove the remaining obligations.

Rewrite `hn` using `[h0, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcont : Continuous fun θ : Fin n → ℝ => f (torusPt (r / 2) θ)` using `hfc.comp_continuous (continuous_pi fun i => (continuous_circleMap 0 _).comp (continuous_apply i)) htor`. Establish `hG` using `GlobalTheory.T.polydisc_poisson_smooth n (r / 2) f (half_pos hr) hcont`. Establish `hGc : ContDiffOn ℝ ∞ (fun z => polyPoisson (r / 2) f (z - c)) (Metric.ball c (r / 2))`.

Use `ContDiffOn.comp (g := polyPoisson (r / 2) f) (f := fun z : Fin n → ℂ => z - c) (t := Metric.ball 0 (r / 2)) hG (contDiff_id.sub contDiff_const).contDiffOn ?_` and prove the remaining obligations. Introduce `z hz`. Simplify `hz` using `[dist_eq_norm]`. Use `⟨fun z => polyPoisson (r / 2) f (z - c), hGc, ?_⟩` and prove the remaining obligations. Establish `hT : Dense {z : Fin n → ℂ | ∀ i, z i ≠ c i}`.

Establish `h` using `(GlobalTheory.T.dense_coordinate_torus n).preimage (Homeomorph.subRight c).isOpenMap`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`. Simplify using `[sub_ne_zero]`. Establish `hD : IsOpen (Metric.ball c (r / 2) ∩ Q)` using `Metric.isOpen_ball.inter hQ`.

Establish `hsub : Metric.ball c (r / 2) ∩ Q ⊆ Metric.ball c r ∩ Q` using `Set.inter_subset_inter_left _ (Metric.ball_subset_ball (half_le_self hr.le))`. Establish `heq : Set.EqOn (fun z => polyPoisson (r / 2) f (z - c)) F ((Metric.ball c (r / 2) ∩ Q) ∩ {z : Fin n → ℂ | ∀ i, z i ≠ c i})`. Introduce `z hz`. Establish `hw : z - c ∈ punct (n` using `n) (r / 2) := by`. Introduce `i`.

Use `⟨sub_ne_zero.2 (hz.2 i), ?_⟩` and prove the remaining obligations. Establish `h1 : ‖z - c‖ < r / 2` using `by simpa [dist_eq_norm] using hz.1.1`. Conclude with `(norm_le_pi_norm (z - c) i).trans_lt h1`. Simplify using `only`. Rewrite using `[hpo _ hw, hf]`.

Simplify using the standard rewrite rules. Conclude with `Set.EqOn.of_subset_closure heq (hGc.mono Set.inter_subset_left).continuousOn (fun z hz => (hsm z (hsub hz)).continuousAt.continuousWithinAt) Set.inter_subset_left (hT.open_subset_closure_inter hD)`.
-/
theorem locExt_core {n : ℕ} (c : Fin n → ℂ) (r : ℝ) (hr : 0 < r) (Q : Set (Fin n → ℂ))
    (hQ : IsOpen Q) (hcov : ∀ z ∈ Metric.ball c r, (∀ i, z i ≠ c i) → z ∈ Q)
    (F : (Fin n → ℂ) → ℝ) (hsm : ∀ z ∈ Metric.ball c r ∩ Q, ContDiffAt ℝ ∞ F z)
    (hlevi : ∀ z ∈ Metric.ball c r ∩ Q, ∀ w, levi F z w = 0)
    (B : ℝ) (hB : ∀ z ∈ Metric.ball c r ∩ Q, |F z| ≤ B) :
    ∃ G : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ G (Metric.ball c (r / 2)) ∧
      ∀ z ∈ Metric.ball c (r / 2) ∩ Q, G z = F z := by
  set f : (Fin n → ℂ) → ℝ := fun w => F (c + w) with hf
  have hmem : ∀ w ∈ punct (n := n) r, c + w ∈ Metric.ball c r ∩ Q := by
    intro w hw
    have hb : c + w ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact (pi_norm_lt_iff hr).2 fun i => (hw i).2
    refine ⟨hb, hcov _ hb fun i => ?_⟩
    simpa using (hw i).1
  have hτ : ∀ w : Fin n → ℂ, ContDiffAt ℝ ∞ (fun w : Fin n → ℂ => c + w) w :=
    fun w => contDiffAt_const.add contDiffAt_id
  have hfsm : ∀ w ∈ punct (n := n) r, ContDiffAt ℝ ∞ f w :=
    fun w hw => ContDiffAt.comp w (hsm _ (hmem w hw)) (hτ w)
  have hharm : SepHarm r f := by
    refine GlobalTheory.T.levi_flat_separately_harmonic n f (punct r) (locExt_isOpen_punct r)
      (fun w hw => (hfsm w hw).contDiffWithinAt) ?_
    intro w hw v
    have hA : AnalyticAt ℂ (fun w : Fin n → ℂ => c + w) w := analyticAt_const.add analyticAt_id
    have h2 : ContDiffAt ℝ 2 F (c + w) := (hsm _ (hmem w hw)).of_le locExt_two_le
    have := levi_comp (φ := F) (τ := fun w : Fin n → ℂ => c + w) (z := w) v hA h2
    calc levi f w v = levi (F ∘ fun w : Fin n → ℂ => c + w) w v := rfl
      _ = 0 := by rw [this]; exact hlevi _ (hmem w hw) _
  have hfc : ContinuousOn f (punct r) :=
    fun w hw => (hfsm w hw).continuousAt.continuousWithinAt
  have hpo := GlobalTheory.T.polydisc_poisson_reproduces_harmonic n f (r / 2) r B (half_pos hr) (half_lt_self hr) hfc hharm
    (fun w hw => hB _ (hmem w hw))
  have htor : ∀ θ : Fin n → ℝ, torusPt (r / 2) θ ∈ punct (n := n) r := by
    intro θ i
    have hn : ‖torusPt (r / 2) θ i‖ = r / 2 := by
      simp only [torusPt]
      rw [norm_circleMap_zero, abs_of_pos (half_pos hr)]
    refine ⟨fun h0 => ?_, by rw [hn]; exact half_lt_self hr⟩
    rw [h0, norm_zero] at hn
    linarith
  have hcont : Continuous fun θ : Fin n → ℝ => f (torusPt (r / 2) θ) :=
    hfc.comp_continuous
      (continuous_pi fun i => (continuous_circleMap 0 _).comp (continuous_apply i)) htor
  have hG := GlobalTheory.T.polydisc_poisson_smooth n (r / 2) f (half_pos hr) hcont
  have hGc : ContDiffOn ℝ ∞ (fun z => polyPoisson (r / 2) f (z - c)) (Metric.ball c (r / 2)) := by
    refine ContDiffOn.comp (g := polyPoisson (r / 2) f) (f := fun z : Fin n → ℂ => z - c)
      (t := Metric.ball 0 (r / 2)) hG (contDiff_id.sub contDiff_const).contDiffOn ?_
    intro z hz
    simpa [dist_eq_norm] using hz
  refine ⟨fun z => polyPoisson (r / 2) f (z - c), hGc, ?_⟩
  have hT : Dense {z : Fin n → ℂ | ∀ i, z i ≠ c i} := by
    have h := (GlobalTheory.T.dense_coordinate_torus n).preimage (Homeomorph.subRight c).isOpenMap
    convert h using 1
    ext z
    simp [sub_ne_zero]
  have hD : IsOpen (Metric.ball c (r / 2) ∩ Q) := Metric.isOpen_ball.inter hQ
  have hsub : Metric.ball c (r / 2) ∩ Q ⊆ Metric.ball c r ∩ Q :=
    Set.inter_subset_inter_left _ (Metric.ball_subset_ball (half_le_self hr.le))
  have heq : Set.EqOn (fun z => polyPoisson (r / 2) f (z - c)) F
      ((Metric.ball c (r / 2) ∩ Q) ∩ {z : Fin n → ℂ | ∀ i, z i ≠ c i}) := by
    intro z hz
    have hw : z - c ∈ punct (n := n) (r / 2) := by
      intro i
      refine ⟨sub_ne_zero.2 (hz.2 i), ?_⟩
      have h1 : ‖z - c‖ < r / 2 := by simpa [dist_eq_norm] using hz.1.1
      exact (norm_le_pi_norm (z - c) i).trans_lt h1
    simp only
    rw [hpo _ hw, hf]
    simp
  exact Set.EqOn.of_subset_closure heq
    (hGc.mono Set.inter_subset_left).continuousOn
    (fun z hz => (hsm z (hsub hz)).continuousAt.continuousWithinAt)
    Set.inter_subset_left (hT.open_subset_closure_inter hD)

/- English proof (translation)
Introduce `e X _ A L s nb m W hs hsnc th u M hth hu hP hPn hM x`. Take `⟨ψ, hψ, hxψ, S, hbd⟩` from `GlobalTheory.T.snc_boundary_coordinate_chart e X A L s nb m W hs hsnc x`. Take `⟨hcl, -⟩` from `GlobalTheory.T.section_boundary_closed_and_codense e X A L s nb m W hs hsnc`. Set `g₀ : X → ℝ` to `fun y => th.φ x y + u y`. Set `U' : Set X` to `th.U x ∩ (bdry s)ᶜ`.

Establish `hU' : IsOpen U'` using `(th.isOpen_U x).inter hcl.isOpen_compl`. Establish `hsm0 : A.SmoothOn U' g₀` using `fun j => ((hth.1 x j).mono fun y hy => ⟨hy.1, hy.2.1⟩).add ((hu j).mono fun y hy => ⟨hy.1, hy.2.2⟩)`. Establish `hlz : ∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U', ∀ w, levi (g₀ ∘ (A.chart j).symm) y w = 0`. Introduce `j y hy w`. Establish `hmemP : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' ((th + LocPot.ofFun u).U x ∩ (bdry s)ᶜ)` using `⟨hy.1, ⟨hy.2.1, trivial⟩, hy.2.2⟩`.

Establish `h1 : 0 ≤ levi (g₀ ∘ (A.chart j).symm) y w` using `hP x j y hmemP w`. Establish `h2 : 0 ≤ levi (fun z => (-1 : ℝ) * (g₀ ∘ (A.chart j).symm) z) y w` using `hPn x j y hmemP w`. Establish `hc2 : ContDiffAt ℝ 2 (g₀ ∘ (A.chart j).symm) y` using `((hsm0 j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU').mem_nhds hy)).of_le locExt_two_le`. Establish `h3` using `levi_add_smul (f := fun _ => (0 : ℝ)) (-1) contDiffAt_const hc2 w`. Simplify using `only [zero_add] at h3`.

Rewrite `h2` using `[h3]`. Establish `h0 : levi (fun _ : Fin e → ℂ => (0 : ℝ)) y w = 0` using `by simp [levi]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hO₁ : IsOpen (ψ.target ∩ ψ.symm ⁻¹' th.U x)` using `ψ.isOpen_inter_preimage_symm (th.isOpen_U x)`. Establish `hcO₁ : ψ x ∈ ψ.target ∩ ψ.symm ⁻¹' th.U x` using `⟨ψ.map_source hxψ, by rw [Set.mem_preimage, ψ.left_inv hxψ]; exact th.mem_U x⟩`.

Set `Q : Set (Fin e → ℂ)` to `{z | ∀ i ∈ S, z i ≠ 0}`. Establish `hQ : IsOpen Q` using `locExt_isOpen_nz S`. Set `S' : Finset (Fin e)` to `S.filter fun i => ψ x i ≠ 0`. Establish `hQ₂ : IsOpen {z : Fin e → ℂ | ∀ i ∈ S', z i ≠ 0}` using `locExt_isOpen_nz S'`. Establish `hcQ₂ : ψ x ∈ {z : Fin e → ℂ | ∀ i ∈ S', z i ≠ 0}` using `fun i hi => (Finset.mem_filter.1 hi).2`.

Take `⟨r, hr, hball⟩` from `Metric.nhds_basis_closedBall.mem_iff.1 ((hO₁.inter hQ₂).mem_nhds ⟨hcO₁, hcQ₂⟩)`. Establish `hcov : ∀ z ∈ Metric.ball (ψ x) r, (∀ i, z i ≠ ψ x i) → z ∈ Q`. Introduce `z hz hne i hi`. Distinguish the cases in `h0 : ψ x i = 0`. Rewrite using `[← h0]`.

Conclude with `hne i`. Conclude with `(hball (Metric.ball_subset_closedBall hz)).2 i (Finset.mem_filter.2 ⟨hi, h0⟩)`. Establish `hoff : ∀ z ∈ Metric.ball (ψ x) r ∩ Q, z ∈ ψ.target ∧ ψ.symm z ∈ U'`. Introduce `z hz`. Establish `hz1` using `(hball (Metric.ball_subset_closedBall hz.1)).1`.

Use `⟨hz1.1, hz1.2, fun hb => ?_⟩` and prove the remaining obligations. Take `⟨i, hi, h0⟩` from `(hbd _ (ψ.map_target hz1.1)).1 hb`. Rewrite `h0` using `[ψ.right_inv hz1.1]`. Conclude with `hz.2 i hi h0`. Take `⟨C, hC⟩` from `(isCompact_closedBall (ψ x) r).exists_bound_of_continuousOn (f := th.φ x ∘ ψ.symm) fun z hz => (GlobalTheory.T.smooth_in_compatible_chart e X A ψ (th.U x) (th.φ x) hψ (th.isOpen_U x) (hth.1 x) z (hball hz).1.1 (hball hz).1.2).continuousAt.continuousWithinAt`.

Take `⟨G, hGs, hGe⟩` from `locExt_core (ψ x) r hr Q hQ hcov (g₀ ∘ ψ.symm) (fun z hz => GlobalTheory.T.smooth_in_compatible_chart e X A ψ U' g₀ hψ hU' hsm0 z (hoff z hz).1 (hoff z hz).2) (fun z hz => GlobalTheory.T.levi_zero_in_compatible_chart e X A ψ U' g₀ hψ hU' hsm0 hlz z (hoff z hz).1 (hoff z hz).2) (C …`. Establish `h1` using `hC z (Metric.ball_subset_closedBall hz.1)`. Establish `h2` using `hM _ (hoff z hz).2.2`. Rewrite `h1` using `[Real.norm_eq_abs]`. Conclude with `(abs_add_le _ _).trans (add_le_add h1 h2))`.

Establish `hhalf : Metric.ball (ψ x) (r / 2) ⊆ Metric.closedBall (ψ x) r` using `(Metric.ball_subset_ball (half_le_self hr.le)).trans Metric.ball_subset_closedBall`. Establish `hNU : ψ.source ∩ ψ ⁻¹' Metric.ball (ψ x) (r / 2) ⊆ th.U x`. Introduce `y hy`. Establish `h` using `(hball (hhalf hy.2)).1.2`. Rewrite `h` using `[Set.mem_preimage, ψ.left_inv hy.1]`. Then use the resulting hypothesis.

Use `⟨ψ.source ∩ ψ ⁻¹' Metric.ball (ψ x) (r / 2), fun y => (G ∘ ψ) y - th.φ x y, ψ.isOpen_inter_preimage Metric.isOpen_ball, ⟨hxψ, Metric.mem_ball_self (half_pos hr)⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `j`. Establish `h1` using `GlobalTheory.T.smoothOn_of_chart_composition e X A ψ (Metric.ball (ψ x) (r / 2)) G hψ Metric.isOpen_ball (fun z hz => (hball (hhalf hz)).1.1) hGs`. Conclude with `(h1 j).sub ((hth.1 x j).mono fun y hy => ⟨hy.1, hNU hy.2⟩)`. Introduce `y hy hyb`.

Establish `hz : ψ y ∈ Metric.ball (ψ x) (r / 2) ∩ Q` using `⟨hy.2, fun i hi h0 => hyb ((hbd y hy.1).2 ⟨i, hi, h0⟩)⟩`. Establish `h` using `hGe _ hz`. Simplify using `only [Function.comp_apply] at h ⊢`. Rewrite using `[h, ψ.left_inv hy.1]`. Simplify using `[g₀]`.
-/
theorem locExt : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → ∀ (th : LocPot X) (u : X → ℝ) (M : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1)) → (∀ y ∉ bdry s, |u y| ≤ M) → ∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ bdry s → E y = u y := by
  intro e X _ A L s nb m W hs hsnc th u M hth hu hP hPn hM x
  obtain ⟨ψ, hψ, hxψ, S, hbd⟩ := GlobalTheory.T.snc_boundary_coordinate_chart e X A L s nb m W hs hsnc x
  obtain ⟨hcl, -⟩ := GlobalTheory.T.section_boundary_closed_and_codense e X A L s nb m W hs hsnc
  let g₀ : X → ℝ := fun y => th.φ x y + u y
  let U' : Set X := th.U x ∩ (bdry s)ᶜ
  have hU' : IsOpen U' := (th.isOpen_U x).inter hcl.isOpen_compl
  have hsm0 : A.SmoothOn U' g₀ := fun j =>
    ((hth.1 x j).mono fun y hy => ⟨hy.1, hy.2.1⟩).add ((hu j).mono fun y hy => ⟨hy.1, hy.2.2⟩)
  have hlz : ∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U', ∀ w,
      levi (g₀ ∘ (A.chart j).symm) y w = 0 := by
    intro j y hy w
    have hmemP : y ∈ (A.chart j).target ∩
        (A.chart j).symm ⁻¹' ((th + LocPot.ofFun u).U x ∩ (bdry s)ᶜ) :=
      ⟨hy.1, ⟨hy.2.1, trivial⟩, hy.2.2⟩
    have h1 : 0 ≤ levi (g₀ ∘ (A.chart j).symm) y w := hP x j y hmemP w
    have h2 : 0 ≤ levi (fun z => (-1 : ℝ) * (g₀ ∘ (A.chart j).symm) z) y w :=
      hPn x j y hmemP w
    have hc2 : ContDiffAt ℝ 2 (g₀ ∘ (A.chart j).symm) y :=
      ((hsm0 j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU').mem_nhds hy)).of_le
        locExt_two_le
    have h3 := levi_add_smul (f := fun _ => (0 : ℝ)) (-1) contDiffAt_const hc2 w
    simp only [zero_add] at h3
    rw [h3] at h2
    have h0 : levi (fun _ : Fin e → ℂ => (0 : ℝ)) y w = 0 := by simp [levi]
    linarith
  have hO₁ : IsOpen (ψ.target ∩ ψ.symm ⁻¹' th.U x) :=
    ψ.isOpen_inter_preimage_symm (th.isOpen_U x)
  have hcO₁ : ψ x ∈ ψ.target ∩ ψ.symm ⁻¹' th.U x :=
    ⟨ψ.map_source hxψ, by rw [Set.mem_preimage, ψ.left_inv hxψ]; exact th.mem_U x⟩
  let Q : Set (Fin e → ℂ) := {z | ∀ i ∈ S, z i ≠ 0}
  have hQ : IsOpen Q := locExt_isOpen_nz S
  let S' : Finset (Fin e) := S.filter fun i => ψ x i ≠ 0
  have hQ₂ : IsOpen {z : Fin e → ℂ | ∀ i ∈ S', z i ≠ 0} := locExt_isOpen_nz S'
  have hcQ₂ : ψ x ∈ {z : Fin e → ℂ | ∀ i ∈ S', z i ≠ 0} :=
    fun i hi => (Finset.mem_filter.1 hi).2
  obtain ⟨r, hr, hball⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.1 ((hO₁.inter hQ₂).mem_nhds ⟨hcO₁, hcQ₂⟩)
  have hcov : ∀ z ∈ Metric.ball (ψ x) r, (∀ i, z i ≠ ψ x i) → z ∈ Q := by
    intro z hz hne i hi
    by_cases h0 : ψ x i = 0
    · rw [← h0]; exact hne i
    · exact (hball (Metric.ball_subset_closedBall hz)).2 i (Finset.mem_filter.2 ⟨hi, h0⟩)
  have hoff : ∀ z ∈ Metric.ball (ψ x) r ∩ Q, z ∈ ψ.target ∧ ψ.symm z ∈ U' := by
    intro z hz
    have hz1 := (hball (Metric.ball_subset_closedBall hz.1)).1
    refine ⟨hz1.1, hz1.2, fun hb => ?_⟩
    obtain ⟨i, hi, h0⟩ := (hbd _ (ψ.map_target hz1.1)).1 hb
    rw [ψ.right_inv hz1.1] at h0
    exact hz.2 i hi h0
  obtain ⟨C, hC⟩ := (isCompact_closedBall (ψ x) r).exists_bound_of_continuousOn
    (f := th.φ x ∘ ψ.symm) fun z hz =>
      (GlobalTheory.T.smooth_in_compatible_chart e X A ψ (th.U x) (th.φ x) hψ (th.isOpen_U x) (hth.1 x) z (hball hz).1.1
        (hball hz).1.2).continuousAt.continuousWithinAt
  obtain ⟨G, hGs, hGe⟩ := locExt_core (ψ x) r hr Q hQ hcov (g₀ ∘ ψ.symm)
    (fun z hz => GlobalTheory.T.smooth_in_compatible_chart e X A ψ U' g₀ hψ hU' hsm0 z (hoff z hz).1 (hoff z hz).2)
    (fun z hz => GlobalTheory.T.levi_zero_in_compatible_chart e X A ψ U' g₀ hψ hU' hsm0 hlz z (hoff z hz).1 (hoff z hz).2)
    (C + M) (fun z hz => by
      have h1 := hC z (Metric.ball_subset_closedBall hz.1)
      have h2 := hM _ (hoff z hz).2.2
      rw [Real.norm_eq_abs] at h1
      exact (abs_add_le _ _).trans (add_le_add h1 h2))
  have hhalf : Metric.ball (ψ x) (r / 2) ⊆ Metric.closedBall (ψ x) r :=
    (Metric.ball_subset_ball (half_le_self hr.le)).trans Metric.ball_subset_closedBall
  have hNU : ψ.source ∩ ψ ⁻¹' Metric.ball (ψ x) (r / 2) ⊆ th.U x := by
    intro y hy
    have h := (hball (hhalf hy.2)).1.2
    rwa [Set.mem_preimage, ψ.left_inv hy.1] at h
  refine ⟨ψ.source ∩ ψ ⁻¹' Metric.ball (ψ x) (r / 2), fun y => (G ∘ ψ) y - th.φ x y,
    ψ.isOpen_inter_preimage Metric.isOpen_ball, ⟨hxψ, Metric.mem_ball_self (half_pos hr)⟩, ?_, ?_⟩
  · intro j
    have h1 := GlobalTheory.T.smoothOn_of_chart_composition e X A ψ (Metric.ball (ψ x) (r / 2)) G hψ Metric.isOpen_ball
      (fun z hz => (hball (hhalf hz)).1.1) hGs
    exact (h1 j).sub ((hth.1 x j).mono fun y hy => ⟨hy.1, hNU hy.2⟩)
  · intro y hy hyb
    have hz : ψ y ∈ Metric.ball (ψ x) (r / 2) ∩ Q :=
      ⟨hy.2, fun i hi h0 => hyb ((hbd y hy.1).2 ⟨i, hi, h0⟩)⟩
    have h := hGe _ hz
    simp only [Function.comp_apply] at h ⊢
    rw [h, ψ.left_inv hy.1]
    simp [g₀]

end GlobalTheory.CompanionTheory.Ar.PB.Flat
